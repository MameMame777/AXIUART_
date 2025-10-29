`timescale 1ns / 1ps

// Advanced Coverage Sequences for UART-AXI4 Bridge
// Specialized sequences designed to maximize coverage metrics
// Utilizes standardized uart_frame_transaction class features

import uvm_pkg::*;
import uart_axi4_test_pkg::*;
`include "uvm_macros.svh"

// Helper to configure a transaction with consistent payload and metadata
function automatic void configure_uart_transaction(
    uart_frame_transaction req,
    bit is_write,
    bit auto_increment,
    logic [1:0] size_field,
    logic [3:0] length_field,
    logic [31:0] addr_value,
    bit expect_error = 1'b0,
    bit error_inject = 1'b0
);
    int bytes_per_beat;
    int beat_count;

    req.is_write       = is_write;
    req.auto_increment = auto_increment;
    req.size           = size_field;
    req.length         = length_field;
    req.addr           = addr_value;
    req.expect_error   = expect_error;
    req.error_inject   = error_inject;
    req.data_randomization = 1'b0;
    req.sof            = SOF_HOST_TO_DEVICE;

    if (is_write) begin
        case (size_field)
            2'b00: bytes_per_beat = 1;
            2'b01: bytes_per_beat = 2;
            2'b10: bytes_per_beat = 4;
            default: bytes_per_beat = 1;
        endcase

        beat_count = length_field + 1;
        req.data = new[beat_count * bytes_per_beat];
        for (int i = 0; i < req.data.size(); i++) begin
            req.data[i] = 8'(i + addr_value[3:0]);
        end
    end else begin
        req.data = new[0];
    end

    req.post_randomize();
endfunction

//===============================================
// Coverage Corner Cases Sequence
//===============================================
class coverage_corner_cases_sequence extends uvm_sequence #(uart_frame_transaction);
    `uvm_object_utils(coverage_corner_cases_sequence)
    
    int num_transactions = 50;
    
    function new(string name = "coverage_corner_cases_sequence");
        super.new(name);
    endfunction
    
    task body();
        uart_frame_transaction req;
        
        `uvm_info("COV_CORNER", "Starting corner cases coverage sequence", UVM_MEDIUM)
        
        // Test 1: Minimum and maximum addresses
        for (int i = 0; i < 10; i++) begin
            req = uart_frame_transaction::type_id::create("req");
            start_item(req);
            
            req.addr = 32'h00001000;

            if (!req.randomize() with {
                is_write == 1'b1;
                size == 2'b00; // 8-bit
                length == 4'h0; // Single byte
            }) begin
                `uvm_error("COV_CORNER", "Randomization failed for corner case test")
            end
            
            finish_item(req);
            `uvm_info("COV_CORNER", $sformatf("Corner case write: addr=0x%08X, size=%0d, len=%0d", 
                     req.addr, req.size, req.length), UVM_HIGH)
        end
        
        // Test 2: All command combinations
        for (int rw = 0; rw <= 1; rw++) begin
            for (int inc = 0; inc <= 1; inc++) begin
                for (int sz = 0; sz <= 2; sz++) begin // Skip 2'b11 (invalid)
                    for (int len = 0; len <= 15; len++) begin
                        req = uart_frame_transaction::type_id::create("req");
                        start_item(req);
                        
                        req.addr = 32'h00001000; // Safe address
                        req.error_inject = 1'b0;
                        req.data_randomization = 1'b1;

                        if (!req.randomize() with {
                            is_write == rw;
                            auto_increment == inc;
                            size == sz;
                            length == len;
                        }) begin
                            `uvm_error("COV_CORNER", "Randomization failed for command combination")
                        end
                        
                        finish_item(req);
                    end
                end
            end
        end
        
        `uvm_info("COV_CORNER", "Corner cases coverage sequence completed", UVM_MEDIUM)
    endtask
    
endclass

//===============================================
// Coverage Error Injection Sequence
//===============================================
class coverage_error_injection_sequence extends uvm_sequence #(uart_frame_transaction);
    `uvm_object_utils(coverage_error_injection_sequence)
    
    function new(string name = "coverage_error_injection_sequence");
        super.new(name);
    endfunction
    
    task body();
        uart_frame_transaction req;
        
        `uvm_info("COV_ERROR", "Starting error injection coverage sequence", UVM_MEDIUM)
        
        // Test 1: CRC errors
        for (int i = 0; i < 10; i++) begin
            req = uart_frame_transaction::type_id::create("req");
            start_item(req);
            
            req.addr = 32'h00001000;
            req.error_inject = 1'b1;
            req.data_randomization = 1'b1;

            if (!req.randomize() with {
                is_write == 1'b1;
                size inside {2'b00, 2'b01, 2'b10};
                length inside {4'h0, 4'h7, 4'hF};
            }) begin
                `uvm_error("COV_ERROR", "Randomization failed for CRC error test")
            end
            
            // Manually corrupt CRC after randomization
            req.crc = req.crc ^ 8'hFF; // Flip all bits to ensure CRC error
                req.expect_error = 1'b1; // CRCエラー注入時は必ずエラー期待フラグを立てる
            
            finish_item(req);
            `uvm_info("COV_ERROR", $sformatf("CRC error injection: original_crc=0x%02X, corrupted_crc=0x%02X, expect_error=%0b", 
                     req.crc ^ 8'hFF, req.crc, req.expect_error), UVM_HIGH)
        end
        
        // Test 2: Invalid SOF patterns
        for (int i = 0; i < 5; i++) begin
            req = uart_frame_transaction::type_id::create("req");
            start_item(req);
            
            req.addr = 32'h00001000;
            req.error_inject = 1'b0;
            req.data_randomization = 1'b0;

            if (!req.randomize() with {
                sof inside {8'h00, 8'hFF, 8'hA5, 8'h3C}; // Invalid SOF values
                is_write == 1'b1;
            }) begin
                `uvm_error("COV_ERROR", "Randomization failed for invalid SOF test")
            end
            
            finish_item(req);
            `uvm_info("COV_ERROR", $sformatf("Invalid SOF: 0x%02X", req.sof), UVM_HIGH)
        end
        
        // Test 3: Invalid command fields
        for (int i = 0; i < 5; i++) begin
            req = uart_frame_transaction::type_id::create("req");
            start_item(req);
            
            req.addr = 32'h00001000;
            req.error_inject = 1'b0;
            req.data_randomization = 1'b1;

            if (!req.randomize() with {
                size == 2'b11; // Invalid size field
                is_write == 1'b1;
            }) begin
                `uvm_error("COV_ERROR", "Randomization failed for invalid command test")
            end
            
            finish_item(req);
            `uvm_info("COV_ERROR", $sformatf("Invalid command size field: 0b%02b", req.size), UVM_HIGH)
        end
        
        `uvm_info("COV_ERROR", "Error injection coverage sequence completed", UVM_MEDIUM)
    endtask
    
endclass

//===============================================
// Coverage Boundary Values Sequence  
//===============================================
class coverage_boundary_values_sequence extends uvm_sequence #(uart_frame_transaction);
    `uvm_object_utils(coverage_boundary_values_sequence)
    
    function new(string name = "coverage_boundary_values_sequence");
        super.new(name);
    endfunction
    
    task body();
        uart_frame_transaction req;
        logic [31:0] boundary_addresses[] = {
            32'h00000000, 32'h00000001, 32'h00000002, 32'h00000003, 32'h00000004,
            32'h000007FC, 32'h000007FD, 32'h000007FE, 32'h000007FF,
            32'h00001000, 32'h00001FFC, 32'h00001FFD, 32'h00001FFE, 32'h00001FFF
        };
        
        `uvm_info("COV_BOUNDARY", "Starting boundary values coverage sequence", UVM_MEDIUM)
        
        // Test boundary addresses with different data sizes
        foreach (boundary_addresses[i]) begin
            for (int sz = 0; sz <= 2; sz++) begin
                for (int rw = 0; rw <= 1; rw++) begin
                    req = uart_frame_transaction::type_id::create("req");
                    start_item(req);
                    
                    req.addr = boundary_addresses[i];
                    req.error_inject = 1'b0;
                    req.data_randomization = 1'b1;

                    if (!req.randomize() with {
                        size == sz;
                        is_write == rw;
                        length inside {4'h0, 4'h1, 4'hE, 4'hF};
                    }) begin
                        `uvm_error("COV_BOUNDARY", "Randomization failed for boundary test")
                    end
                    
                    finish_item(req);
                    `uvm_info("COV_BOUNDARY", $sformatf("Boundary test: addr=0x%08X, size=%0d, rw=%0d", 
                             req.addr, req.size, req.is_write), UVM_HIGH)
                end
            end
        end
        
        `uvm_info("COV_BOUNDARY", "Boundary values coverage sequence completed", UVM_MEDIUM)
    endtask
    
endclass

//===============================================
// Coverage State Transitions Sequence
//===============================================
class coverage_state_transitions_sequence extends uvm_sequence #(uart_frame_transaction);
    `uvm_object_utils(coverage_state_transitions_sequence)
    
    function new(string name = "coverage_state_transitions_sequence");
        super.new(name);
    endfunction
    
    task body();
        uart_frame_transaction req;
        logic [31:0] state_addrs[3];
        
        `uvm_info("COV_STATE", "Starting state transitions coverage sequence", UVM_MEDIUM)
        
        state_addrs[0] = 32'h00001000;
        state_addrs[1] = 32'h00001004;
        state_addrs[2] = 32'h00001008;

        // Test rapid state transitions
        for (int i = 0; i < 20; i++) begin
            // Send valid transaction
            req = uart_frame_transaction::type_id::create("req");
            start_item(req);
            
            req.addr = state_addrs[i % 3];
            req.error_inject = 1'b0;
            req.data_randomization = 1'b1;

            if (!req.randomize() with {
                is_write dist {1'b0 := 50, 1'b1 := 50};
                size inside {2'b00, 2'b01, 2'b10};
                length inside {4'h0, 4'h3, 4'h7, 4'hF};
            }) begin
                `uvm_error("COV_STATE", "Randomization failed for state transition test")
            end
            
            finish_item(req);
            
            // Small delay to allow state transitions
            #(100ns + $urandom_range(0, 500));
        end
        
        `uvm_info("COV_STATE", "State transitions coverage sequence completed", UVM_MEDIUM)
    endtask
    
endclass

//===============================================
// Coverage FIFO Stress Sequence
//===============================================
class coverage_fifo_stress_sequence extends uvm_sequence #(uart_frame_transaction);
    `uvm_object_utils(coverage_fifo_stress_sequence)
    
    function new(string name = "coverage_fifo_stress_sequence");
        super.new(name);
    endfunction
    
    task body();
        uart_frame_transaction req_array[10];
        
        `uvm_info("COV_FIFO", "Starting FIFO stress coverage sequence", UVM_MEDIUM)
        
        // Generate burst of transactions to stress FIFOs
        for (int burst = 0; burst < 5; burst++) begin
            // Create burst of back-to-back transactions
            for (int i = 0; i < 10; i++) begin
                req_array[i] = uart_frame_transaction::type_id::create($sformatf("req_%0d", i));
                start_item(req_array[i]);
                
                req_array[i].addr = 32'h00001000 + (i * 4);
                req_array[i].error_inject = 1'b0;
                req_array[i].data_randomization = 1'b1;

                if (!req_array[i].randomize() with {
                    is_write == 1'b1;
                    size == 2'b10; // 32-bit for maximum data
                    length == 4'hF; // Maximum length
                }) begin
                    `uvm_error("COV_FIFO", $sformatf("Randomization failed for FIFO stress test %0d", i))
                end
                
                finish_item(req_array[i]);
                // No delay - back-to-back transactions
            end
            
            // Recovery period
            #10us;
            `uvm_info("COV_FIFO", $sformatf("FIFO stress burst %0d completed", burst), UVM_HIGH)
        end
        
        `uvm_info("COV_FIFO", "FIFO stress coverage sequence completed", UVM_MEDIUM)
    endtask
    
endclass

//===============================================
// Coverage Timing Variations Sequence
//===============================================
class coverage_timing_variations_sequence extends uvm_sequence #(uart_frame_transaction);
    `uvm_object_utils(coverage_timing_variations_sequence)
    
    function new(string name = "coverage_timing_variations_sequence");
        super.new(name);
    endfunction
    
    task body();
        uart_frame_transaction req;
        int delay_variations[] = {0, 100, 500, 1000, 5000, 10000}; // ns
        
        `uvm_info("COV_TIMING", "Starting timing variations coverage sequence", UVM_MEDIUM)
        
        // Test different inter-transaction delays
        foreach (delay_variations[i]) begin
            for (int j = 0; j < 5; j++) begin
                req = uart_frame_transaction::type_id::create("req");
                start_item(req);
                
                req.addr = 32'h00001000 + (j * 4);
                req.error_inject = 1'b0;
                req.data_randomization = 1'b1;

                if (!req.randomize() with {
                    is_write dist {1'b0 := 30, 1'b1 := 70};
                    size inside {2'b00, 2'b01, 2'b10};
                    length inside {4'h0, 4'h7, 4'hF};
                }) begin
                    `uvm_error("COV_TIMING", "Randomization failed for timing variation test")
                end
                
                finish_item(req);
                
                // Apply delay variation
                #(delay_variations[i] * 1ns);
                `uvm_info("COV_TIMING", $sformatf("Applied %0d ns delay", delay_variations[i]), UVM_HIGH)
            end
        end
        
        `uvm_info("COV_TIMING", "Timing variations coverage sequence completed", UVM_MEDIUM)
    endtask
    
endclass

//===============================================
// [REMOVED] Duplicate classes - using enhanced versions below
//===============================================


//===============================================
// UART TX Coverage Enhancement Sequence
// Target: uart_tx signal toggle improvement (0% → >50%)
//===============================================
class uart_tx_coverage_sequence extends uvm_sequence #(uart_frame_transaction);
    `uvm_object_utils(uart_tx_coverage_sequence)
    
    function new(string name = "uart_tx_coverage_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction tx_req;
        
        `uvm_info("UART_TX_COV", "Starting UART TX coverage sequence", UVM_MEDIUM)
        
        // UART transmission test with multiple frame sizes
        for (int i = 1; i <= 16; i++) begin
            tx_req = uart_frame_transaction::type_id::create("tx_req");
            start_item(tx_req);
            
            tx_req.addr = 32'h00001000 + (i * 4);

            if (!tx_req.randomize() with {
                length == i;
                is_write == 1'b1; // Write operation to trigger TX
                auto_increment == 1'b1; // Increment address
                size == 2'b00; // Byte access
            }) begin
                `uvm_error("UART_TX_COV", "Failed to randomize TX request")
            end
            
            finish_item(tx_req);
            
            // Wait for transmission completion (approximate UART bit time * bits per frame)
            #(uart_axi4_test_pkg::BIT_TIME_NS * 10 * i);
            
            `uvm_info("UART_TX_COV", $sformatf("TX frame %0d: len=%0d, addr=0x%08X", 
                     i, tx_req.length, tx_req.addr), UVM_HIGH)
        end
        
        `uvm_info("UART_TX_COV", "UART TX coverage sequence completed", UVM_MEDIUM)
    endtask
endclass

//===============================================
// Dynamic Configuration Change Sequence
// Target: baud_div_config, timeout_config toggle improvement
//===============================================
class uart_config_change_sequence extends uvm_sequence #(uart_frame_transaction);
    `uvm_object_utils(uart_config_change_sequence)
    
    function new(string name = "uart_config_change_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction config_req;
        int baud_div_values[4];
        int timeout_values[4];
        int base_div;
        
        `uvm_info("CONFIG_CHANGE", "Starting dynamic configuration change sequence", UVM_MEDIUM)
        
        // Initialize baud rate configurations using package constants
        base_div = uart_axi4_test_pkg::CLK_FREQ_HZ / uart_axi4_test_pkg::BAUD_RATE;
        baud_div_values[0] = base_div;        // Nominal maximum baud
        baud_div_values[1] = base_div * 2;    // Half-rate configuration
        baud_div_values[2] = base_div * 4;    // Quarter-rate configuration
        baud_div_values[3] = base_div * 8;    // Eighth-rate configuration
        
        // Initialize timeout values
        timeout_values[0] = 500;
        timeout_values[1] = 1000;
        timeout_values[2] = 2000;
        timeout_values[3] = 4000;
        
        for (int i = 0; i < 4; i++) begin
            // Configure baud rate
            config_req = uart_frame_transaction::type_id::create("config_req");
            start_item(config_req);
            
            // Build data array with baud divisor
            config_req.data = new[2];
            config_req.data[0] = baud_div_values[i][7:0];
            config_req.data[1] = baud_div_values[i][15:8];
            
            config_req.addr = 32'h00001004; // Baud configuration register

            if (!config_req.randomize() with {
                length == 6; // SOF + CMD + ADDR(4) + DATA(2) + CRC
                is_write == 1'b1; // Write operation
                size == 2'b01; // Half-word access
            }) begin
                `uvm_error("CONFIG_CHANGE", "Failed to randomize baud config")
            end
            
            finish_item(config_req);
            
            `uvm_info("CONFIG_CHANGE", $sformatf("Baud config %0d: div=%0d", 
                     i, baud_div_values[i]), UVM_HIGH)
            
            // Test with new baud rate
            for (int j = 0; j < 10; j++) begin
                config_req = uart_frame_transaction::type_id::create("test_req");
                start_item(config_req);
                
                config_req.addr = 32'h00001000 + ((j % 9) * 4);
                config_req.is_write = 1'b1;

                if (!config_req.randomize() with {
                    length inside {[1:4]};
                }) begin
                    `uvm_warning("CONFIG_CHANGE", "Randomization failed for test request")
                end
                
                finish_item(config_req);
                #2000ns; // Allow time for configuration to take effect
            end
        end
        
        `uvm_info("CONFIG_CHANGE", "Dynamic configuration change sequence completed", UVM_MEDIUM)
    endtask
endclass