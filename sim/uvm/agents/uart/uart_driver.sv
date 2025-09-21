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
            
            drive_frame(req);
            collect_response(req);
            
            seq_item_port.item_done();
        end
    endtask
    
    // Drive a complete UART frame
    virtual task drive_frame(uart_frame_transaction tr);
        logic [7:0] frame_bytes[];
        logic [7:0] calculated_crc;
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
            calculated_crc = calculate_crc_from_index(frame_bytes, 1, 5);
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
            end
            // CRC calculation excludes SOF (starts from index 1)
            calculated_crc = calculate_crc_from_index(frame_bytes, 1, byte_count - 2);
            frame_bytes[byte_count - 1] = calculated_crc;
            `uvm_info("UART_DRIVER", $sformatf("Write CRC: byte_count=%0d, crc_len=%0d -> CRC=0x%02X", 
                      byte_count, byte_count - 2, calculated_crc), UVM_MEDIUM)
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
    
    // Collect response from DUT
    virtual task collect_response(uart_frame_transaction tr);
        logic [7:0] response_bytes[];
        logic [7:0] temp_byte;
        int response_timeout_cycles = cfg.frame_timeout_ns * cfg.clk_freq_hz / 1_000_000_000;
        int byte_count = 0;
        bit timeout_occurred = 0;
        
        // Wait for response start
        fork
            begin
                wait (vif.uart_tx == 1'b0); // Wait for start bit
                timeout_occurred = 0;
            end
            begin
                repeat (response_timeout_cycles) @(posedge vif.clk);
                timeout_occurred = 1;
            end
        join_any
        disable fork;
        
        if (timeout_occurred) begin
            `uvm_error("UART_DRIVER", "Timeout waiting for response")
            tr.response_received = 0;
            return;
        end
        
        // Collect response bytes
        response_bytes = new[100]; // Allocate max size
        
        do begin
            collect_uart_byte(temp_byte);
            response_bytes[byte_count] = temp_byte;
            byte_count++;
            
            // Check for end of frame (simple timeout-based detection)
            fork
                begin
                    wait (vif.uart_tx == 1'b0); // Next start bit
                    timeout_occurred = 0;
                end
                begin
                    repeat (cfg.byte_time_ns * cfg.clk_freq_hz / 1_000_000_000 * 2) @(posedge vif.clk);
                    timeout_occurred = 1;
                end
            join_any
            disable fork;
            
        end while (!timeout_occurred && byte_count < 100);
        
        // Parse response
        if (byte_count >= 4 && response_bytes[0] == SOF_DEVICE_TO_HOST) begin
            tr.response_status = response_bytes[1];
            tr.response_received = 1;
            
            // Extract response data for read operations
            if (tr.cmd[7] && tr.response_status == STATUS_OK && byte_count > 7) begin
                int data_bytes = byte_count - 7; // SOF + STATUS + CMD + ADDR(4) + CRC
                tr.response_data = new[data_bytes];
                for (int i = 0; i < data_bytes; i++) begin
                    tr.response_data[i] = response_bytes[7 + i];
                end
            end
            
            `uvm_info("UART_DRIVER", $sformatf("Response received: STATUS=0x%02X, bytes=%0d", 
                      tr.response_status, byte_count), UVM_MEDIUM)
        end else begin
            `uvm_error("UART_DRIVER", "Invalid response format")
            tr.response_received = 0;
        end
    endtask
    
    // Collect a single UART byte
    virtual task collect_uart_byte(output logic [7:0] data);
        int bit_time_cycles = cfg.clk_freq_hz / cfg.baud_rate;
        int sample_time = bit_time_cycles / 2; // Sample at bit center
        
        // Wait for start bit (already detected)
        repeat (sample_time) @(posedge vif.clk);
        
        if (vif.uart_tx != 1'b0) begin
            `uvm_warning("UART_DRIVER", "Start bit not detected correctly")
        end
        
        // Collect data bits (LSB first)
        for (int i = 0; i < 8; i++) begin
            repeat (bit_time_cycles) @(posedge vif.clk);
            data[i] = vif.uart_tx;
        end
        
        // Check stop bit
        repeat (bit_time_cycles) @(posedge vif.clk);
        if (vif.uart_tx != 1'b1) begin
            `uvm_warning("UART_DRIVER", "Stop bit not detected correctly")
        end
        
        `uvm_info("UART_DRIVER", $sformatf("Collected UART byte: 0x%02X", data), UVM_DEBUG)
    endtask
    
    // Simple CRC-8 calculation (polynomial 0x07)
    virtual function logic [7:0] calculate_crc(logic [7:0] data[], int length);
        logic [7:0] crc = 8'h00;
        
        for (int i = 0; i < length; i++) begin
            crc = crc ^ data[i];
            for (int j = 0; j < 8; j++) begin
                if (crc[7]) begin
                    crc = (crc << 1) ^ 8'h07;
                end else begin
                    crc = crc << 1;
                end
            end
        end
        
        return crc;
    endfunction

    // CRC-8 calculation starting from specific index (excludes SOF)
    virtual function logic [7:0] calculate_crc_from_index(logic [7:0] data[], int start_idx, int length);
        logic [7:0] crc = 8'h00;
        
        for (int i = start_idx; i < start_idx + length; i++) begin
            crc = crc ^ data[i];
            for (int j = 0; j < 8; j++) begin
                if (crc[7]) begin
                    crc = (crc << 1) ^ 8'h07;
                end else begin
                    crc = crc << 1;
                end
            end
        end
        
        return crc;
    endfunction

endclass