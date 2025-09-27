`timescale 1ns / 1ps

// Advanced Coverage Sequences for UART-AXI4 Bridge
// Specialized sequences designed to maximize coverage metrics
// Utilizes standardized uart_frame_transaction class features

import uvm_pkg::*;
import uart_axi4_test_pkg::*;
`include "uvm_macros.svh"

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
            
            if (!req.randomize() with {
                addr == 32'h00001000;
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
                        
                        if (!req.randomize() with {
                            is_write == rw;
                            auto_increment == inc;
                            size == sz;
                            length == len;
                            addr == 32'h00001000; // Safe address
                            error_inject == 1'b0;
                            data_randomization == 1'b1;
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
            
            if (!req.randomize() with {
                error_inject == 1'b1;
                is_write == 1'b1;
                addr == 32'h00001000;
                size inside {2'b00, 2'b01, 2'b10};
                length inside {4'h0, 4'h7, 4'hF};
                data_randomization == 1'b1;
            }) begin
                `uvm_error("COV_ERROR", "Randomization failed for CRC error test")
            end
            
            // Manually corrupt CRC after randomization
            req.crc = req.crc ^ 8'hFF; // Flip all bits to ensure CRC error
            
            finish_item(req);
            `uvm_info("COV_ERROR", $sformatf("CRC error injection: original_crc=0x%02X, corrupted_crc=0x%02X", 
                     req.crc ^ 8'hFF, req.crc), UVM_HIGH)
        end
        
        // Test 2: Invalid SOF patterns
        for (int i = 0; i < 5; i++) begin
            req = uart_frame_transaction::type_id::create("req");
            start_item(req);
            
            if (!req.randomize() with {
                sof inside {8'h00, 8'hFF, 8'hA5, 8'h3C}; // Invalid SOF values
                is_write == 1'b1;
                addr == 32'h00001000;
                error_inject == 1'b0;
                data_randomization == 1'b0;
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
            
            if (!req.randomize() with {
                size == 2'b11; // Invalid size field
                is_write == 1'b1;
                addr == 32'h00001000;
                error_inject == 1'b0;
                data_randomization == 1'b1;
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
                    
                    if (!req.randomize() with {
                        addr == boundary_addresses[i];
                        size == sz;
                        is_write == rw;
                        length inside {4'h0, 4'h1, 4'hE, 4'hF};
                        error_inject == 1'b0;
                        data_randomization == 1'b1;
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
        
        `uvm_info("COV_STATE", "Starting state transitions coverage sequence", UVM_MEDIUM)
        
        // Test rapid state transitions
        for (int i = 0; i < 20; i++) begin
            // Send valid transaction
            req = uart_frame_transaction::type_id::create("req");
            start_item(req);
            
            if (!req.randomize() with {
                addr inside {32'h00001000, 32'h00001004, 32'h00001008};
                is_write dist {1'b0 := 50, 1'b1 := 50};
                size inside {2'b00, 2'b01, 2'b10};
                length inside {4'h0, 4'h3, 4'h7, 4'hF};
                error_inject == 1'b0;
                data_randomization == 1'b1;
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
                
                if (!req_array[i].randomize() with {
                    addr == 32'h00001000 + (i * 4);
                    is_write == 1'b1;
                    size == 2'b10; // 32-bit for maximum data
                    length == 4'hF; // Maximum length
                    error_inject == 1'b0;
                    data_randomization == 1'b1;
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
                
                if (!req.randomize() with {
                    addr == 32'h00001000 + (j * 4);
                    is_write dist {1'b0 := 30, 1'b1 := 70};
                    size inside {2'b00, 2'b01, 2'b10};
                    length inside {4'h0, 4'h7, 4'hF};
                    error_inject == 1'b0;
                    data_randomization == 1'b1;
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
// UART TX Coverage Sequence
//===============================================
class uart_tx_coverage_sequence extends uvm_sequence #(uart_frame_transaction);
    `uvm_object_utils(uart_tx_coverage_sequence)
    
    function new(string name = "uart_tx_coverage_sequence");
        super.new(name);
    endfunction
    
    task body();
        uart_frame_transaction req;
        
        `uvm_info("UART_TX_COV", "Starting UART TX coverage sequence", UVM_MEDIUM)
        
        // Test with multiple frame sizes to trigger UART TX activity
        for (int frame_size = 1; frame_size <= 16; frame_size++) begin
            req = uart_frame_transaction::type_id::create("req");
            start_item(req);
            
            if (!req.randomize() with {
                length == frame_size - 1; // length field is 0-based
                is_write == 1'b0; // Write operation to trigger TX response
                addr == 32'h00001000; // Fixed address for simplicity
                size == 2'b10; // 32-bit access
            }) begin
                `uvm_error("UART_TX_COV", "Randomization failed for TX coverage test")
            end
            
            finish_item(req);
            
            // Wait for transmission completion - approximate UART bit time * bits per frame
            // 115200 bps = 8.68us per bit, frame overhead ~10 bits per byte
            #(434 * 10 * frame_size * 1ns); 
            
            `uvm_info("UART_TX_COV", $sformatf("TX test frame %0d: addr=0x%08X, size=%0d", 
                     frame_size, req.addr, req.size), UVM_HIGH)
        end
        
        // Additional burst write tests to maximize TX toggle activity
        for (int burst = 0; burst < 8; burst++) begin
            req = uart_frame_transaction::type_id::create("req");
            start_item(req);
            
            if (!req.randomize() with {
                length == 4'h4; // Fixed medium frame
                is_write == 1'b0; // Write operations
                addr == 32'h00001000;
                size == 2'b10; // 32-bit accesses
            }) begin
                `uvm_error("UART_TX_COV", "Randomization failed for TX burst test")
            end
            
            finish_item(req);
            
            // Shorter delay for burst operation
            #(434 * 10 * 8 * 1ns);
            
            `uvm_info("UART_TX_COV", $sformatf("TX burst %0d: addr=0x%08X", 
                     burst, req.addr), UVM_HIGH)
        end
        
        `uvm_info("UART_TX_COV", "UART TX coverage sequence completed", UVM_MEDIUM)
    endtask
    
endclass

//===============================================
// UART Config Change Coverage Sequence
//===============================================
class uart_config_change_sequence extends uvm_sequence #(uart_frame_transaction);
    `uvm_object_utils(uart_config_change_sequence)
    
    function new(string name = "uart_config_change_sequence");
        super.new(name);
    endfunction
    
    task body();
        uart_frame_transaction req;
        
        // Test different baud rate configurations
        int baud_div_values[] = {434, 217, 108, 54}; // 115200, 230400, 460800, 921600 bps
        int timeout_values[] = {500, 1000, 2000, 4000}; // Different timeout values
        
        `uvm_info("UART_CONFIG_COV", "Starting UART config change coverage sequence", UVM_MEDIUM)
        
        // Test baud rate configuration changes
        foreach (baud_div_values[i]) begin
            req = uart_frame_transaction::type_id::create("req");
            start_item(req);
            
            if (!req.randomize() with {
                addr == 32'h00001004;
                is_write == 1'b0; // Write operation
                size == 2'b01; // 16-bit access
                length == 4'h1; // 2 bytes data
            }) begin
                `uvm_error("UART_CONFIG_COV", "Randomization failed for baud config test")
            end
            
            // Set specific baud rate divisor
            req.data[0] = baud_div_values[i] & 8'hFF;        // Low byte
            req.data[1] = (baud_div_values[i] >> 8) & 8'hFF; // High byte
            
            finish_item(req);
            
            // Wait for configuration to take effect
            #(1000ns);
            
            // Test with new baud rate by sending test transactions
            for (int test_tx = 0; test_tx < 5; test_tx++) begin
                req = uart_frame_transaction::type_id::create("req");
                start_item(req);
                
                if (!req.randomize() with {
                    addr == 32'h00001000;
                    is_write == 1'b0;
                    size == 2'b10;
                    length == 4'h0;
                }) begin
                    `uvm_error("UART_CONFIG_COV", "Randomization failed for baud test transaction")
                end
                
                finish_item(req);
                
                // Adjusted timing for new baud rate
                #(baud_div_values[i] * 10 * 8 * 1ns);
            end
            
            `uvm_info("UART_CONFIG_COV", $sformatf("Tested baud divisor: %0d", baud_div_values[i]), UVM_HIGH)
        end
        
        // Test timeout configuration changes
        foreach (timeout_values[i]) begin
            req = uart_frame_transaction::type_id::create("req");
            start_item(req);
            
            if (!req.randomize() with {
                addr == 32'h00001008;
                is_write == 1'b0; // Write operation
                size == 2'b01; // 16-bit access
                length == 4'h1; // 2 bytes data
            }) begin
                `uvm_error("UART_CONFIG_COV", "Randomization failed for timeout config test")
            end
            
            // Set specific timeout value
            req.data[0] = timeout_values[i] & 8'hFF;        // Low byte
            req.data[1] = (timeout_values[i] >> 8) & 8'hFF; // High byte
            
            finish_item(req);
            
            // Wait for configuration to take effect
            #(500ns);
            
            // Test timeout behavior with delayed transactions
            req = uart_frame_transaction::type_id::create("req");
            start_item(req);
            
            if (!req.randomize() with {
                addr == 32'h00001010;
                is_write == 1'b1; // Read operation
                size == 2'b10;
                length == 4'h3; // 4 bytes
            }) begin
                `uvm_error("UART_CONFIG_COV", "Randomization failed for timeout test")
            end
            
            finish_item(req);
            
            // Wait longer than timeout to trigger timeout behavior
            #(timeout_values[i] * 100 * 1ns);
            
            `uvm_info("UART_CONFIG_COV", $sformatf("Tested timeout value: %0d", timeout_values[i]), UVM_HIGH)
        end
        
        `uvm_info("UART_CONFIG_COV", "UART config change coverage sequence completed", UVM_MEDIUM)
    endtask
    
endclass