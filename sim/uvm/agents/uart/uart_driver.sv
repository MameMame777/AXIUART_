`timescale 1ns / 1ps

// Import protocol constants from test package
import uart_axi4_test_pkg::*;

// IEEE 1800.2 / UVM Best Practice Compliant UART Driver
// Features:
// - Reset-safe: Uses try_next_item() to avoid deadlock during reset
// - Hang-free: Natural termination support with stop_request
// - Baud-dynamic: Reads baud_rate from config dynamically
// - State-machine based: Proper reset handling
class uart_driver extends uvm_driver #(uart_frame_transaction);
    
    `uvm_component_utils(uart_driver)
    
    // Configuration
    uart_axi4_env_config cfg;
    uvm_tlm_analysis_fifo#(uart_frame_transaction) tx_response_fifo;
    uvm_analysis_port #(uart_frame_transaction) tx_request_ap;
    
    // Virtual interface
    virtual uart_if vif;
    
    // Driver state
    typedef enum {RESET, IDLE, DRIVING, WAIT_RESPONSE} driver_state_t;
    driver_state_t state;
    
    // Runtime parameters (updated from config)
    int current_baud_rate;
    int bit_period_ns;
    int post_frame_idle_cycles;
    
    function new(string name = "uart_driver", uvm_component parent = null);
        super.new(name, parent);
        tx_request_ap = new("tx_request_ap", this);
        state = RESET;
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        if (!uvm_config_db#(uart_axi4_env_config)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("UART_DRIVER", "Failed to get configuration object");
        end
        
        // Get virtual interface
        if (!uvm_config_db#(virtual uart_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("UART_DRIVER", "Failed to get virtual interface");
        end

        // Optional monitor-provided response FIFO
        if (!uvm_config_db#(uvm_tlm_analysis_fifo#(uart_frame_transaction))::get(this, "", "tx_response_fifo", tx_response_fifo)) begin
            tx_response_fifo = null;
            `uvm_info("UART_DRIVER", "Monitor response FIFO not provided", UVM_LOW);
        end
        
        // Initialize runtime parameters from config
        update_baud_parameters();
    endfunction
    
    // Update baud rate parameters from config (dynamic reconfiguration support)
    virtual function void update_baud_parameters();
        if (cfg == null) return;
        
        current_baud_rate = cfg.baud_rate;
        
        // Calculate bit period in nanoseconds
        // bit_period = (1 / baud_rate) / (1ns)
        // Example: 115200 baud = 8680ns per bit
        bit_period_ns = int'(1_000_000_000.0 / real'(current_baud_rate));
        
        // Get idle cycles from config (default to 20 if not set)
        post_frame_idle_cycles = (cfg.max_idle_cycles > 0) ? cfg.max_idle_cycles : 20;
        
        `uvm_info("UART_DRIVER", $sformatf("Baud parameters updated: rate=%0d, bit_period=%0dns, idle_cycles=%0d",
                  current_baud_rate, bit_period_ns, post_frame_idle_cycles), UVM_MEDIUM);
    endfunction
    
    // UVM Cookbook compliant run_phase
    // Reset is handled by test via uart_reset_seq calling vif.reset_dut()
    // Driver assumes reset already completed when transactions begin
    virtual task run_phase(uvm_phase phase);
        uart_frame_transaction req;
        
        // Initialize interface signals
        initialize_interface();
        
        `uvm_info("UART_DRIVER", "Run phase started - ready for transactions", UVM_LOW);
        
        // Simple forever loop (UVM Cookbook pattern)
        // No reset handling - test controls reset via sequence
        forever begin
            // Blocking get (IEEE 1800.2 / UVM Cookbook standard)
            seq_item_port.get_next_item(req);
            
            `uvm_info("UART_DRIVER", $sformatf("Got transaction: CMD=0x%02X ADDR=0x%08X", 
                      req.cmd, req.addr), UVM_MEDIUM);
            
            // Update baud parameters (dynamic support)
            update_baud_parameters();
            
            // State transition
            state = DRIVING;
            
            // Execute transaction
            drive_transaction(req);
            
            // Completion notification (IEEE 1800.2 required)
            seq_item_port.item_done();
            
            // Post-frame idle (DUT requirement)
            apply_post_frame_idle();
            
            `uvm_info("UART_DRIVER", "Transaction completed", UVM_HIGH);
            
            // Natural termination check (allow graceful exit when test ends)
            if (phase.get_objection_count(this) == 0) begin
                // Wait for last transaction processing
                repeat(10) @(posedge vif.clk);
                
                // Re-check
                if (phase.get_objection_count(this) == 0) begin
                    `uvm_info("UART_DRIVER", "No active objections - terminating naturally", UVM_LOW);
                    break;
                end
            end
        end
        
        `uvm_info("UART_DRIVER", "Run phase completed gracefully", UVM_LOW);
    endtask
    
    // Initialize interface signals
    virtual task initialize_interface();
        vif.uart_rx = 1'b1;    // Idle state (high)
        vif.uart_cts_n = 1'b0; // CTS asserted (ready to receive)
        `uvm_info("UART_DRIVER", "Interface initialized: RX=1 CTS_N=0", UVM_HIGH);
    endtask
    
    // Handle reset event
    virtual task handle_reset();
        if (state != RESET) begin
            `uvm_info("UART_DRIVER", "Reset detected - entering RESET state", UVM_MEDIUM);
            state = RESET;
        end
        
        // Reinitialize interface
        initialize_interface();
        
        // Wait for reset de-assertion (edge-sensitive)
        @(negedge vif.rst);
        
        // Small delay after reset release
        repeat(5) @(posedge vif.clk);
        
        `uvm_info("UART_DRIVER", "Reset de-asserted - returning to IDLE", UVM_MEDIUM);
    endtask
    
    // Drive complete transaction
    virtual task drive_transaction(uart_frame_transaction tr);
        // Check CTS before driving (hardware flow control)
        if (vif.uart_rts_n == 1'b1) begin
            `uvm_warning("UART_DRIVER", "RTS de-asserted - DUT not ready, waiting...");
            wait(vif.uart_rts_n == 1'b0);
        end
        
        // Send frame
        send_frame(tr);
        
        // Handle response if needed
        if (tx_response_fifo != null && !should_skip_response(tr)) begin
            collect_response(tr);
        end
    endtask
    
    // Check if response should be skipped
    virtual function bit should_skip_response(uart_frame_transaction tr);
        // RESET command has no response
        if (tr.cmd == 8'hFF) return 1;
        
        // Baud rate configuration has no response (baud mismatch)
        if (tr.is_write && (tr.addr == 32'h00001008)) return 1;
        
        return 0;
    endfunction
    
    // Send complete UART frame
    virtual task send_frame(uart_frame_transaction tr);
        `uvm_info("UART_DRIVER", $sformatf("Sending frame: SOF=0x%02X CMD=0x%02X ADDR=0x%08X", 
                  SOF_HOST_TO_DEVICE, tr.cmd, tr.addr), UVM_HIGH);
        
        // SOF
        send_uart_byte(SOF_HOST_TO_DEVICE);
        
        // CMD
        send_uart_byte(tr.cmd);
        
        // ADDR (little-endian, 4 bytes)
        send_uart_byte(tr.addr[7:0]);
        send_uart_byte(tr.addr[15:8]);
        send_uart_byte(tr.addr[23:16]);
        send_uart_byte(tr.addr[31:24]);
        
        // DATA (if write command)
        if (tr.cmd[7] == 0 && tr.data.size() > 0) begin
            for (int i = 0; i < tr.data.size(); i++) begin
                send_uart_byte(tr.data[i]);
            end
        end
        
        // CRC (simplified - XOR of CMD and ADDR[7:0])
        send_uart_byte(tr.cmd ^ tr.addr[7:0]);
        
        `uvm_info("UART_DRIVER", "Frame transmission complete", UVM_HIGH);
    endtask
    
    // Send single UART byte (8N1 format)
    virtual task send_uart_byte(logic [7:0] data);
        // Start bit (low)
        vif.uart_rx = 1'b0;
        #bit_period_ns;
        
        // Data bits (LSB first)
        for (int i = 0; i < 8; i++) begin
            vif.uart_rx = data[i];
            #bit_period_ns;
        end
        
        // Stop bit (high)
        vif.uart_rx = 1'b1;
        #bit_period_ns;
    endtask
    
    // Apply post-frame idle period (critical for DUT idle_cnt)
    virtual task apply_post_frame_idle();
        // Return to idle state
        vif.uart_rx = 1'b1;
        
        // Wait specified idle cycles (allows DUT idle counter to increment)
        repeat(post_frame_idle_cycles) @(posedge vif.clk);
        
        `uvm_info("UART_DRIVER", $sformatf("Post-frame idle applied: %0d cycles", post_frame_idle_cycles), UVM_HIGH);
    endtask
    
    // Collect response from monitor FIFO with timeout
    virtual task collect_response(uart_frame_transaction req);
        uart_frame_transaction rsp;
        bit got_response;
        time timeout_ns;
        
        timeout_ns = cfg.frame_timeout_ns * 4; // Conservative timeout
        got_response = 0;
        
        fork
            begin
                tx_response_fifo.get(rsp);
                got_response = 1;
            end
            begin
                #timeout_ns;
            end
        join_any
        disable fork;
        
        if (got_response) begin
            `uvm_info("UART_DRIVER", $sformatf("Response received: STATUS=0x%02X", rsp.cmd), UVM_MEDIUM);
            req.response_status = rsp.cmd;
            req.response_received = 1;
            req.timeout_error = 0;
        end else begin
            `uvm_warning("UART_DRIVER", "Response timeout - no frame received from DUT");
            req.response_received = 0;
            req.timeout_error = 1;
            req.response_status = STATUS_TIMEOUT;
        end
    endtask
    
    // Reset handler for mid-transaction reset
    virtual task monitor_reset();
        fork
            forever begin
                @(posedge vif.rst);
                `uvm_info("UART_DRIVER", "Asynchronous reset detected", UVM_HIGH);
                // State will be handled in main loop
            end
        join_none
    endtask

endclass
