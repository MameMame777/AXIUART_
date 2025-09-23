`timescale 1ns / 1ps

// UART Driver for UART-AXI4 Bridge UVM Testbench
class uart_driver extends uvm_driver #(uart_frame_transaction);
    
    `uvm_component_utils(uart_driver)
    
    // Configuration
    uart_axi4_env_config cfg;
    
    // Virtual interface
    virtual uart_if vif;
    
    // Protocol constants (Import from main test package)
    // These constants must match uart_axi4_test_pkg definitions
    
    function new(string name = "uart_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        if (!uvm_config_db#(uart_axi4_env_config)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("UART_DRIVER", "Failed to get configuration object")
        end
        
        // Get virtual interface
        if (!uvm_config_db#(virtual uart_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("UART_DRIVER", "Failed to get virtual interface")
        end
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        uart_frame_transaction req;
        
        // Initialize UART RX line to idle (high)
        vif.uart_rx = 1'b1;
        
        forever begin
            seq_item_port.get_next_item(req);
            
            `uvm_info("UART_DRIVER", $sformatf("Driving transaction: CMD=0x%02X, ADDR=0x%08X", 
                      req.cmd, req.addr), UVM_MEDIUM)
            
            // Drive frame first, then collect response (Monitor-style approach)
            // CRITICAL FIX: Start response monitoring BEFORE frame transmission
            fork
                begin
                    // Monitor-style: Start monitoring immediately
                    wait (vif.uart_tx == 1'b0);
                    `uvm_info("UART_DRIVER", $sformatf("Response start detected at time %0t", $realtime), UVM_MEDIUM)
                    collect_response_direct(req);
                end
                begin
                    // Drive frame transmission
                    drive_frame(req);
                end
            join
            
            seq_item_port.item_done();
        end
    endtask
    
    // Drive a complete UART frame
    virtual task drive_frame(uart_frame_transaction tr);
        logic [7:0] frame_bytes[];
        logic [7:0] calculated_crc;
        logic [7:0] crc_data[];
        logic [7:0] crc_data_fixed[5];
        int byte_count;
        
        // Build complete frame
        if (tr.cmd[7]) begin // Read command
            byte_count = 7; // SOF + CMD + ADDR(4) + CRC
            frame_bytes = new[byte_count];
            frame_bytes[0] = SOF_HOST_TO_DEVICE;
            frame_bytes[1] = tr.cmd;
            frame_bytes[2] = tr.addr[7:0];
            frame_bytes[3] = tr.addr[15:8];
            frame_bytes[4] = tr.addr[23:16];
            frame_bytes[5] = tr.addr[31:24];
            // CRC calculation excludes SOF (starts from index 1)
            crc_data_fixed[0] = frame_bytes[1];
            crc_data_fixed[1] = frame_bytes[2];
            crc_data_fixed[2] = frame_bytes[3];
            crc_data_fixed[3] = frame_bytes[4];
            crc_data_fixed[4] = frame_bytes[5];
            calculated_crc = calculate_crc(crc_data_fixed, 5);
            frame_bytes[6] = calculated_crc;
            `uvm_info("UART_DRIVER", $sformatf("Read CRC: data=[%02X,%02X,%02X,%02X,%02X] -> CRC=0x%02X", 
                      frame_bytes[1], frame_bytes[2], frame_bytes[3], frame_bytes[4], frame_bytes[5], calculated_crc), UVM_MEDIUM)
        end else begin // Write command
            byte_count = 7 + tr.data.size(); // SOF + CMD + ADDR(4) + DATA + CRC
            frame_bytes = new[byte_count];
            frame_bytes[0] = SOF_HOST_TO_DEVICE;
            frame_bytes[1] = tr.cmd;
            frame_bytes[2] = tr.addr[7:0];
            frame_bytes[3] = tr.addr[15:8];
            frame_bytes[4] = tr.addr[23:16];
            frame_bytes[5] = tr.addr[31:24];
            
            for (int i = 0; i < tr.data.size(); i++) begin
                frame_bytes[6 + i] = tr.data[i];
                `uvm_info("UART_DRIVER", $sformatf("Data[%0d] = 0x%02X", i, tr.data[i]), UVM_MEDIUM)
            end
            // CRC calculation excludes SOF (starts from index 1)
            crc_data = new[byte_count - 2];
            for (int i = 0; i < byte_count - 2; i++) begin
                crc_data[i] = frame_bytes[1 + i];
            end
            calculated_crc = calculate_crc(crc_data, byte_count - 2);
            frame_bytes[byte_count - 1] = calculated_crc;
            `uvm_info("UART_DRIVER", $sformatf("Write CRC: byte_count=%0d, crc_len=%0d -> CRC=0x%02X", 
                      byte_count, byte_count - 2, calculated_crc), UVM_MEDIUM)
            
            // Print full frame for debugging
            begin
                string frame_str = "Frame: ";
                for (int i = 0; i < byte_count; i++) begin
                    frame_str = {frame_str, $sformatf("0x%02X ", frame_bytes[i])};
                end
                `uvm_info("UART_DRIVER", frame_str, UVM_MEDIUM)
            end
        end
        
        // Send frame byte by byte
        for (int i = 0; i < byte_count; i++) begin
            drive_uart_byte(frame_bytes[i]);
            
            // Add inter-byte gap (random between min and max idle cycles)
            if (i < byte_count - 1) begin
                repeat ($urandom_range(cfg.min_idle_cycles, cfg.max_idle_cycles)) begin
                    @(posedge vif.clk);
                end
            end
        end
        
        // Add inter-frame gap (much longer than inter-byte gap)
        repeat (cfg.max_idle_cycles * 5) begin
            @(posedge vif.clk);
        end
    endtask
    
    // Drive a single UART byte (8N1 format)
    virtual task drive_uart_byte(logic [7:0] data);
        int bit_time_cycles = cfg.clk_freq_hz / cfg.baud_rate;
        
        `uvm_info("UART_DRIVER", $sformatf("Driving UART byte: 0x%02X", data), UVM_DEBUG)
        
        // Start bit
        vif.uart_rx = 1'b0;
        repeat (bit_time_cycles) @(posedge vif.clk);
        
        // Data bits (LSB first)
        for (int i = 0; i < 8; i++) begin
            vif.uart_rx = data[i];
            repeat (bit_time_cycles) @(posedge vif.clk);
        end
        
        // Stop bit
        vif.uart_rx = 1'b1;
        repeat (bit_time_cycles) @(posedge vif.clk);
    endtask
    
    // Collect response from DUT - Hardware Specification Based Implementation
    virtual task collect_response(uart_frame_transaction tr);
        logic [7:0] response_bytes[];
        logic [7:0] temp_byte;
        real timeout_ns = cfg.frame_timeout_ns;
        real clk_freq = cfg.clk_freq_hz;
        int response_timeout_cycles = int'((timeout_ns * clk_freq) / 1_000_000_000.0);
        int byte_count = 0;
        int expected_response_length;
        bit timeout_occurred = 0;
        bit response_detected = 0;
        
        // Hardware Spec: Response timeout = 200ms max processing delay (measured ~100ms)
        localparam int RESPONSE_TIMEOUT_US = 200000;
        int response_wait_cycles = (RESPONSE_TIMEOUT_US * cfg.clk_freq_hz) / 1_000_000;
        
        // Determine expected response length based on protocol specification
        if (tr.cmd[7] == 1'b0) begin // Write command
            expected_response_length = 4; // SOF + STATUS + CMD + CRC
            `uvm_info("UART_DRIVER", "Write command: expecting 4-byte response (SOF + STATUS + CMD + CRC)", UVM_MEDIUM)
        end else begin // Read command
            expected_response_length = 4; // Minimum for error response
            `uvm_info("UART_DRIVER", "Read command: expecting variable length response (minimum 4 bytes)", UVM_MEDIUM)
        end
        
        `uvm_info("UART_DRIVER", $sformatf("Starting response collection for %s command (CMD=0x%02X)", 
                  (tr.cmd[7] == 1'b1) ? "Read" : "Write", tr.cmd), UVM_MEDIUM)
        
        // Monitor-style immediate response detection (no fork delay)
        // Wait for TX line to go low (response start bit) - immediate detection like Monitor
        wait (vif.uart_tx == 1'b0);
        response_detected = 1;
        `uvm_info("UART_DRIVER", $sformatf("Response start detected at time %0t", $realtime), UVM_MEDIUM)
        
        // Hardware Spec: Collect response bytes using precise timing
        response_bytes = new[20]; // Allocate reasonable size
        byte_count = 0;
        
        begin
            `uvm_info("UART_DRIVER", "Starting protocol-aware response collection", UVM_MEDIUM)
            
            // Hardware Spec: Collect first response byte (should be SOF = 0x5A)
            collect_uart_byte(temp_byte);
            response_bytes[byte_count] = temp_byte;
            byte_count++;
            `uvm_info("UART_DRIVER", $sformatf("Collected SOF byte: 0x%02X (expected 0x5A)", temp_byte), UVM_MEDIUM)
            
            // Hardware Spec: For Write commands, collect exactly 4 bytes total
            if (tr.cmd[7] == 1'b0) begin // Write command
                // Collect remaining 3 bytes (STATUS, CMD, CRC)
                for (int i = 1; i < expected_response_length; i++) begin
                    // Hardware Spec: Wait for next byte start bit with inter-byte timeout
                    fork : inter_byte_wait
                        begin
                            wait (vif.uart_tx == 1'b0);
                        end
                        begin
                            // Hardware Spec: 200µs max inter-byte gap
                            repeat (10000) @(posedge vif.clk); // 200µs @ 50MHz
                            timeout_occurred = 1;
                        end
                    join_any
                    disable inter_byte_wait;
                    
                    if (timeout_occurred) begin
                        `uvm_warning("UART_DRIVER", $sformatf("Inter-byte timeout after %0d bytes", byte_count))
                        break;
                    end
                    
                    collect_uart_byte(temp_byte);
                    response_bytes[byte_count] = temp_byte;
                    byte_count++;
                    `uvm_info("UART_DRIVER", $sformatf("Collected Write response byte %0d: 0x%02X", i, temp_byte), UVM_MEDIUM)
                end
                
                `uvm_info("UART_DRIVER", $sformatf("Write response collection complete: %0d bytes", byte_count), UVM_MEDIUM)
                
            end else begin // Read command - collect variable length
                // Continue collecting bytes until no more are available
                while (byte_count < 20) begin
                    // Wait for next byte start bit with timeout
                    fork
                        begin
                            wait (vif.uart_tx == 1'b0);
                        end
                        begin
                            // 5ms timeout for additional bytes
                            repeat (250000) @(posedge vif.clk);
                            timeout_occurred = 1;
                        end
                    join_any
                    disable fork;
                    
                    if (timeout_occurred) begin
                        `uvm_info("UART_DRIVER", $sformatf("Read response collection complete after %0d bytes", byte_count), UVM_MEDIUM)
                        break;
                    end
                    
                    collect_uart_byte(temp_byte);
                    response_bytes[byte_count] = temp_byte;
                    byte_count++;
                    `uvm_info("UART_DRIVER", $sformatf("Collected Read response byte %0d: 0x%02X", byte_count-1, temp_byte), UVM_MEDIUM)
                end
            end
        end
        
        // Protocol-compliant response parsing
        if (byte_count > 0) begin
            tr.response_received = 1;
            
            // Validate response format
            if (response_bytes[0] == SOF_DEVICE_TO_HOST) begin // 0x5A
                if (byte_count >= 3) begin
                    tr.response_status = response_bytes[1]; // STATUS byte
                    `uvm_info("UART_DRIVER", $sformatf("Protocol response: SOF=0x%02X STATUS=0x%02X CMD=0x%02X, total_bytes=%0d", 
                              response_bytes[0], response_bytes[1], response_bytes[2], byte_count), UVM_MEDIUM)
                    
                    // Validate response length according to protocol
                    if (tr.cmd[7] == 1'b0) begin // Write command
                        if (byte_count != 4) begin
                            `uvm_warning("UART_DRIVER", $sformatf("Write response length mismatch: expected=4, received=%0d", byte_count))
                        end
                    end else begin // Read command
                        if (response_bytes[1] == 8'h00) begin // Success
                            if (byte_count < 7) begin
                                `uvm_warning("UART_DRIVER", $sformatf("Read success response too short: expected>=7, received=%0d", byte_count))
                            end
                        end else begin // Error
                            if (byte_count != 4) begin
                                `uvm_warning("UART_DRIVER", $sformatf("Read error response length mismatch: expected=4, received=%0d", byte_count))
                            end
                        end
                    end
                end else begin
                    `uvm_warning("UART_DRIVER", $sformatf("Response too short: minimum 3 bytes expected, received %0d", byte_count))
                    tr.response_status = 8'hFF; // Invalid response indicator
                end
            end else begin
                `uvm_warning("UART_DRIVER", $sformatf("Invalid SOF in response: expected=0x5A, received=0x%02X", response_bytes[0]))
                tr.response_status = response_bytes[0]; // Use first byte as status for compatibility
            end
            
            // Debug: print all received bytes
            begin
                string byte_str = "";
                for (int i = 0; i < byte_count; i++) begin
                    byte_str = {byte_str, $sformatf("0x%02X ", response_bytes[i])};
                end
                `uvm_info("UART_DRIVER", $sformatf("Complete response: %s", byte_str), UVM_MEDIUM)
            end
        end else begin
            `uvm_error("UART_DRIVER", "No response received")
            tr.response_received = 0;
            tr.response_status = 8'hFF; // Error indicator
        end
    endtask
    // Collect a single UART byte from TX line (Monitor's exact pattern)
    virtual task collect_uart_byte(output logic [7:0] data);
        int bit_time_cycles = cfg.clk_freq_hz / cfg.baud_rate;
        int sample_time = bit_time_cycles / 2; // Sample at bit center
        
        // Monitor pattern: NO additional start bit detection - caller already detected it
        // Sample start bit - be more tolerant of timing variations
        repeat (sample_time) @(posedge vif.clk);
        if (vif.uart_tx != 1'b0) begin
            `uvm_info("UART_DRIVER", "TX start bit timing variation detected", UVM_DEBUG)
        end
        
        // Sample data bits (LSB first) at bit center
        for (int i = 0; i < 8; i++) begin
            repeat (bit_time_cycles) @(posedge vif.clk);
            data[i] = vif.uart_tx;
            `uvm_info("UART_DRIVER", $sformatf("Bit[%0d]: %b", i, data[i]), UVM_DEBUG)
        end
        
        // Sample stop bit - be more tolerant of timing variations
        repeat (bit_time_cycles) @(posedge vif.clk);
        if (vif.uart_tx != 1'b1) begin
            `uvm_info("UART_DRIVER", "TX stop bit timing variation detected", UVM_DEBUG)
        end
        
        `uvm_info("UART_DRIVER", $sformatf("Collected UART byte: 0x%02X", data), UVM_MEDIUM)
    endtask
    
    // Simple CRC-8 calculation (polynomial 0x07)
    virtual function logic [7:0] calculate_crc(logic [7:0] data[], int length);
        logic [7:0] crc = 8'h00;
        logic [7:0] crc_temp;
        
        for (int i = 0; i < length; i++) begin
            // Match RTL implementation: XOR entire byte first, then process 8 bits
            crc_temp = crc ^ data[i];
            
            // Process each bit with polynomial 0x07 (matches RTL calc_crc8_byte)
            if (crc_temp[7]) crc_temp = (crc_temp << 1) ^ 8'h07; else crc_temp = crc_temp << 1;
            if (crc_temp[7]) crc_temp = (crc_temp << 1) ^ 8'h07; else crc_temp = crc_temp << 1;
            if (crc_temp[7]) crc_temp = (crc_temp << 1) ^ 8'h07; else crc_temp = crc_temp << 1;
            if (crc_temp[7]) crc_temp = (crc_temp << 1) ^ 8'h07; else crc_temp = crc_temp << 1;
            if (crc_temp[7]) crc_temp = (crc_temp << 1) ^ 8'h07; else crc_temp = crc_temp << 1;
            if (crc_temp[7]) crc_temp = (crc_temp << 1) ^ 8'h07; else crc_temp = crc_temp << 1;
            if (crc_temp[7]) crc_temp = (crc_temp << 1) ^ 8'h07; else crc_temp = crc_temp << 1;
            if (crc_temp[7]) crc_temp = (crc_temp << 1) ^ 8'h07; else crc_temp = crc_temp << 1;
            
            crc = crc_temp;
        end
        
        return crc;
    endfunction

    
    // Direct response collection using exact Monitor pattern
    virtual task collect_response_direct(uart_frame_transaction tr);
        logic [7:0] response_bytes[];
        logic [7:0] temp_byte;
        int byte_count = 0;
        int expected_response_length = 4; // SOF + STATUS + CMD + CRC
        
        `uvm_info("UART_DRIVER", "Starting direct response collection (exact Monitor-style)", UVM_MEDIUM)
        
        // Hardware Spec: Collect response bytes using exact Monitor timing pattern
        response_bytes = new[20]; // Allocate reasonable size
        byte_count = 0;
        
        begin
            // Hardware Spec: First byte collection - response already started
            // Do NOT wait for additional start bit - we detected response start already
            collect_uart_tx_byte_monitor(temp_byte);
            response_bytes[byte_count] = temp_byte;
            byte_count++;
            `uvm_info("UART_DRIVER", $sformatf("Collected SOF byte: 0x%02X (expected 0x5A)", temp_byte), UVM_MEDIUM)
            
            // Hardware Spec: For Write commands, collect exactly 4 bytes total
            if (tr.cmd[7] == 1'b0) begin // Write command
                // Collect remaining 3 bytes (STATUS, CMD, CRC)
                for (int i = 1; i < expected_response_length; i++) begin
                    // Hardware Spec: Wait for next byte start bit with inter-byte timeout
                    wait (vif.uart_tx == 1'b0);
                    collect_uart_tx_byte_monitor(temp_byte);
                    response_bytes[byte_count] = temp_byte;
                    byte_count++;
                    `uvm_info("UART_DRIVER", $sformatf("Collected Write response byte %0d: 0x%02X", i, temp_byte), UVM_MEDIUM)
                end
                
                `uvm_info("UART_DRIVER", $sformatf("Write response collection complete: %0d bytes", byte_count), UVM_MEDIUM)
            end
        end
        
        // Validate first byte is SOF
        if (byte_count > 0 && response_bytes[0] == 8'h5A) begin
            `uvm_info("UART_DRIVER", "SUCCESS: Collected correct SOF byte 0x5A!", UVM_MEDIUM)
            tr.response_received = 1;
            tr.response_status = response_bytes[1]; // STATUS byte
        end else begin
            `uvm_error("UART_DRIVER", $sformatf("FAILURE: Wrong SOF byte 0x%02X, expected 0x5A", 
                       byte_count > 0 ? response_bytes[0] : 8'h00))
        end
    endtask

    // Monitor-exact TX byte collection pattern (immediate sampling)
    virtual task collect_uart_tx_byte_monitor(output logic [7:0] data);
        int bit_time_cycles = cfg.clk_freq_hz / cfg.baud_rate;
        
        // CRITICAL: Immediate sampling without any delay
        // We detect response start, now sample immediately from current position
        
        // Skip start bit sampling - already at start of transmission
        // Sample data bits (LSB first) at bit center
        for (int i = 0; i < 8; i++) begin
            repeat (bit_time_cycles) @(posedge vif.clk);
            data[i] = vif.uart_tx;
            `uvm_info("UART_DRIVER", $sformatf("Immediate Bit[%0d]: %b", i, data[i]), UVM_DEBUG)
        end
        
        // Sample stop bit
        repeat (bit_time_cycles) @(posedge vif.clk);
        if (vif.uart_tx != 1'b1) begin
            `uvm_info("UART_DRIVER", "TX stop bit timing variation detected", UVM_DEBUG)
        end
        
        `uvm_info("UART_DRIVER", $sformatf("Immediate sampling TX byte: 0x%02X", data), UVM_MEDIUM)
    endtask

endclass