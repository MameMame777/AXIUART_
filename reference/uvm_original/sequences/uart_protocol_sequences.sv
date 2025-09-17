/*
 * UART Protocol Test Sequences - Phase 2
 * Purpose: Comprehensive sequence library for UART communication protocol testing
 * Features: TX/RX data patterns, FIFO testing, flow control, error injection
 * Guidelines: All sequences test actual RTL DUT behavior
 */

`ifndef UART_PROTOCOL_SEQUENCES_SV
`define UART_PROTOCOL_SEQUENCES_SV

`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

// UART Protocol Transaction Class
class uart_protocol_transaction extends uvm_sequence_item;
    
    // Transaction types
    typedef enum {
        UART_TX_DATA,
        UART_RX_DATA, 
        AXI_REGISTER_ACCESS,
        UART_CONTROL
    } operation_type_e;
    
    typedef enum {
        READ,
        WRITE
    } read_write_e;
    
    typedef enum {
        RTS_CONTROL,
        CTS_CONTROL,
        BAUD_CONTROL
    } control_type_e;
    
    // Transaction fields
    rand operation_type_e operation;
    rand logic [7:0] data;
    rand logic [7:0] address;
    rand logic [31:0] reg_data;
    rand read_write_e read_write;
    rand control_type_e control_type;
    rand logic control_value;
    
    // Constraints
    constraint c_valid_data {
        data inside {[8'h00:8'hFF]};
    }
    
    constraint c_valid_address {
        address inside {8'h00, 8'h04, 8'h08, 8'h0C, 8'h10, 8'h14, 8'h18, 8'h1C};
    }
    
    // UVM automation macros
    `uvm_object_utils_begin(uart_protocol_transaction)
        `uvm_field_enum(operation_type_e, operation, UVM_ALL_ON)
        `uvm_field_int(data, UVM_ALL_ON)
        `uvm_field_int(address, UVM_ALL_ON)
        `uvm_field_int(reg_data, UVM_ALL_ON)
        `uvm_field_enum(read_write_e, read_write, UVM_ALL_ON)
        `uvm_field_enum(control_type_e, control_type, UVM_ALL_ON)
        `uvm_field_int(control_value, UVM_ALL_ON)
    `uvm_object_utils_end
    
    function new(string name = "uart_protocol_transaction");
        super.new(name);
    endfunction
    
endclass

// Base sequence for UART protocol testing
class uart_protocol_base_sequence extends uvm_sequence #(uart_protocol_transaction);
    `uvm_object_utils(uart_protocol_base_sequence)
    
    function new(string name = "uart_protocol_base_sequence");
        super.new(name);
    endfunction
    
    // Helper task for AXI register write
    virtual task axi_register_write(logic [7:0] addr, logic [31:0] data);
        uart_protocol_transaction tr;
        
        `uvm_create(tr)
        tr.operation = AXI_REGISTER_ACCESS;
        tr.address = addr;
        tr.reg_data = data;
        tr.read_write = WRITE;
        `uvm_send(tr)
        
        `uvm_info("SEQ", $sformatf("AXI Write: Addr=0x%02X, Data=0x%08X", addr, data), UVM_HIGH)
    endtask
    
    // Helper task for AXI register read
    virtual task axi_register_read(logic [7:0] addr);
        uart_protocol_transaction tr;
        
        `uvm_create(tr)
        tr.operation = AXI_REGISTER_ACCESS;
        tr.address = addr;
        tr.read_write = READ;
        `uvm_send(tr)
        
        `uvm_info("SEQ", $sformatf("AXI Read: Addr=0x%02X", addr), UVM_HIGH)
    endtask
    
    // Helper task for UART data transmission
    virtual task uart_send_data(logic [7:0] data_byte);
        uart_protocol_transaction tr;
        
        `uvm_create(tr)
        tr.operation = UART_TX_DATA;
        tr.data = data_byte;
        `uvm_send(tr)
        
        `uvm_info("SEQ", $sformatf("UART TX: Data=0x%02X", data_byte), UVM_HIGH)
    endtask
    
    // Helper task for UART data reception simulation
    virtual task uart_receive_data(logic [7:0] data_byte);
        uart_protocol_transaction tr;
        
        `uvm_create(tr)
        tr.operation = UART_RX_DATA;
        tr.data = data_byte;
        `uvm_send(tr)
        
        `uvm_info("SEQ", $sformatf("UART RX: Data=0x%02X", data_byte), UVM_HIGH)
    endtask
    
endclass

// Sequence 1: Basic UART Transmission Test
class uart_basic_transmission_seq extends uart_protocol_base_sequence;
    `uvm_object_utils(uart_basic_transmission_seq)
    
    function new(string name = "uart_basic_transmission_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        `uvm_info("BASIC_TX_SEQ", "=== Starting Basic UART Transmission Test ===", UVM_MEDIUM)
        
        // Step 1: Initialize UART
        `uvm_info("BASIC_TX_SEQ", "Initializing UART controller", UVM_MEDIUM)
        axi_register_write(8'h00, 32'h00000007); // Enable UART, TX, RX
        repeat(20) @(posedge uvm_test_top.clk);
        
        // Step 2: Send basic test patterns
        begin
            logic [7:0] test_patterns[] = {8'h00, 8'h55, 8'hAA, 8'hFF, 8'h0F, 8'hF0};
            
            `uvm_info("BASIC_TX_SEQ", "Sending basic test patterns", UVM_MEDIUM)
            foreach(test_patterns[i]) begin
                uart_send_data(test_patterns[i]);
                repeat(100) @(posedge uvm_test_top.clk); // Wait for transmission
                
                // Check status register
                axi_register_read(8'h04); // Status register
            end
        end
        
        // Step 3: Send ASCII characters
        `uvm_info("BASIC_TX_SEQ", "Sending ASCII character sequence", UVM_MEDIUM)
        for(int i = 8'h30; i <= 8'h39; i++) begin // '0' to '9'
            uart_send_data(i[7:0]);
            repeat(50) @(posedge uvm_test_top.clk);
        end
        
        `uvm_info("BASIC_TX_SEQ", "=== Basic UART Transmission Test Completed ===", UVM_MEDIUM)
    endtask
    
endclass

// Sequence 2: UART Data Pattern Test
class uart_data_pattern_seq extends uart_protocol_base_sequence;
    `uvm_object_utils(uart_data_pattern_seq)
    
    function new(string name = "uart_data_pattern_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        `uvm_info("DATA_PATTERN_SEQ", "=== Starting UART Data Pattern Test ===", UVM_MEDIUM)
        
        // Initialize UART
        axi_register_write(8'h00, 32'h00000007); // Enable UART, TX, RX
        repeat(20) @(posedge uvm_test_top.clk);
        
        // Test Pattern 1: Sequential increment
        `uvm_info("DATA_PATTERN_SEQ", "Testing sequential increment pattern", UVM_MEDIUM)
        for(int i = 0; i < 256; i++) begin
            uart_send_data(i[7:0]);
            if(i % 32 == 0) begin
                axi_register_read(8'h04); // Check status periodically
            end
            repeat(20) @(posedge uvm_test_top.clk);
        end
        
        // Test Pattern 2: Walking ones
        `uvm_info("DATA_PATTERN_SEQ", "Testing walking ones pattern", UVM_MEDIUM)
        for(int i = 0; i < 8; i++) begin
            uart_send_data(1 << i);
            repeat(50) @(posedge uvm_test_top.clk);
        end
        
        // Test Pattern 3: Walking zeros
        `uvm_info("DATA_PATTERN_SEQ", "Testing walking zeros pattern", UVM_MEDIUM)
        for(int i = 0; i < 8; i++) begin
            uart_send_data(~(1 << i));
            repeat(50) @(posedge uvm_test_top.clk);
        end
        
        // Test Pattern 4: Random data
        `uvm_info("DATA_PATTERN_SEQ", "Testing random data pattern", UVM_MEDIUM)
        for(int i = 0; i < 50; i++) begin
            logic [7:0] random_data = $random();
            uart_send_data(random_data);
            repeat(30) @(posedge uvm_test_top.clk);
        end
        
        `uvm_info("DATA_PATTERN_SEQ", "=== UART Data Pattern Test Completed ===", UVM_MEDIUM)
    endtask
    
endclass

// Sequence 3: FIFO Functionality Test
class uart_fifo_test_seq extends uart_protocol_base_sequence;
    `uvm_object_utils(uart_fifo_test_seq)
    
    function new(string name = "uart_fifo_test_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        `uvm_info("FIFO_TEST_SEQ", "=== Starting FIFO Functionality Test ===", UVM_MEDIUM)
        
        // Initialize UART
        axi_register_write(8'h00, 32'h00000007); // Enable UART, TX, RX
        repeat(20) @(posedge uvm_test_top.clk);
        
        // Test 1: Fill TX FIFO
        `uvm_info("FIFO_TEST_SEQ", "Testing TX FIFO fill", UVM_MEDIUM)
        for(int i = 0; i < 64; i++) begin // Fill entire 64-entry FIFO
            uart_send_data(8'hA0 + (i % 16));
            
            // Check FIFO status every 8 entries
            if(i % 8 == 0) begin
                axi_register_read(8'h1C); // FIFO config/status register
            end
            
            repeat(10) @(posedge uvm_test_top.clk);
        end
        
        // Test 2: Monitor FIFO emptying
        `uvm_info("FIFO_TEST_SEQ", "Monitoring TX FIFO emptying", UVM_MEDIUM)
        for(int i = 0; i < 20; i++) begin
            axi_register_read(8'h04); // Status register
            axi_register_read(8'h1C); // FIFO status
            repeat(200) @(posedge uvm_test_top.clk); // Wait for transmission
        end
        
        // Test 3: FIFO threshold testing
        `uvm_info("FIFO_TEST_SEQ", "Testing FIFO thresholds", UVM_MEDIUM)
        axi_register_write(8'h1C, 32'h00001010); // Set TX/RX thresholds
        repeat(20) @(posedge uvm_test_top.clk);
        
        // Fill to threshold
        for(int i = 0; i < 16; i++) begin
            uart_send_data(8'hB0 + i);
            repeat(10) @(posedge uvm_test_top.clk);
        end
        
        // Check interrupt status
        axi_register_read(8'h18); // Interrupt status
        
        `uvm_info("FIFO_TEST_SEQ", "=== FIFO Functionality Test Completed ===", UVM_MEDIUM)
    endtask
    
endclass

// Sequence 4: Flow Control Test
class uart_flow_control_seq extends uart_protocol_base_sequence;
    `uvm_object_utils(uart_flow_control_seq)
    
    function new(string name = "uart_flow_control_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_protocol_transaction tr;
        
        `uvm_info("FLOW_CTRL_SEQ", "=== Starting Flow Control Test ===", UVM_MEDIUM)
        
        // Initialize UART with flow control
        axi_register_write(8'h00, 32'h00000007); // Enable UART, TX, RX
        repeat(20) @(posedge uvm_test_top.clk);
        
        // Test 1: RTS/CTS handshaking
        `uvm_info("FLOW_CTRL_SEQ", "Testing RTS/CTS handshaking", UVM_MEDIUM)
        
        // Assert CTS (allow transmission)
        `uvm_create(tr)
        tr.operation = UART_CONTROL;
        tr.control_type = CTS_CONTROL;
        tr.control_value = 0; // Active low
        `uvm_send(tr)
        
        // Send data with CTS asserted
        for(int i = 0; i < 10; i++) begin
            uart_send_data(8'hC0 + i);
            repeat(50) @(posedge uvm_test_top.clk);
        end
        
        // Deassert CTS (block transmission)
        `uvm_create(tr)
        tr.operation = UART_CONTROL;
        tr.control_type = CTS_CONTROL;
        tr.control_value = 1; // Active low, so 1 = deasserted
        `uvm_send(tr)
        
        // Try to send data with CTS deasserted
        `uvm_info("FLOW_CTRL_SEQ", "Testing transmission with CTS deasserted", UVM_MEDIUM)
        uart_send_data(8'hDD);
        repeat(200) @(posedge uvm_test_top.clk);
        
        // Re-assert CTS and verify transmission resumes
        `uvm_create(tr)
        tr.operation = UART_CONTROL;
        tr.control_type = CTS_CONTROL;
        tr.control_value = 0;
        `uvm_send(tr)
        
        repeat(100) @(posedge uvm_test_top.clk);
        
        `uvm_info("FLOW_CTRL_SEQ", "=== Flow Control Test Completed ===", UVM_MEDIUM)
    endtask
    
endclass

// Sequence 5: Baud Rate Variation Test
class uart_baud_rate_seq extends uart_protocol_base_sequence;
    `uvm_object_utils(uart_baud_rate_seq)
    
    function new(string name = "uart_baud_rate_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        logic [31:0] baud_configs[] = {
            32'h0000043d, // 115200 baud
            32'h000032dc, // 9600 baud
            32'h000008ac, // 57600 baud
            32'h00001a0a  // 19200 baud
        };
        
        string baud_names[] = {"115200", "9600", "57600", "19200"};
        
        `uvm_info("BAUD_RATE_SEQ", "=== Starting Baud Rate Variation Test ===", UVM_MEDIUM)
        
        // Test each baud rate
        foreach(baud_configs[i]) begin
            `uvm_info("BAUD_RATE_SEQ", $sformatf("Testing baud rate: %s", baud_names[i]), UVM_MEDIUM)
            
            // Set baud rate
            axi_register_write(8'h10, baud_configs[i]);
            repeat(20) @(posedge uvm_test_top.clk);
            
            // Enable UART
            axi_register_write(8'h00, 32'h00000007);
            repeat(20) @(posedge uvm_test_top.clk);
            
            // Send test data at this baud rate
            for(int j = 0; j < 8; j++) begin
                uart_send_data(8'hE0 + j);
                repeat(500) @(posedge uvm_test_top.clk); // Extra wait for slower baud rates
            end
            
            // Read status
            axi_register_read(8'h04);
            axi_register_read(8'h10); // Verify baud register
            
            repeat(100) @(posedge uvm_test_top.clk);
        end
        
        `uvm_info("BAUD_RATE_SEQ", "=== Baud Rate Variation Test Completed ===", UVM_MEDIUM)
    endtask
    
endclass

// Sequence 6: Error Injection Test
class uart_error_injection_seq extends uart_protocol_base_sequence;
    `uvm_object_utils(uart_error_injection_seq)
    
    function new(string name = "uart_error_injection_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        `uvm_info("ERROR_INJ_SEQ", "=== Starting Error Injection Test ===", UVM_MEDIUM)
        
        // Initialize UART
        axi_register_write(8'h00, 32'h00000007);
        repeat(20) @(posedge uvm_test_top.clk);
        
        // Test 1: FIFO overflow simulation
        `uvm_info("ERROR_INJ_SEQ", "Testing FIFO overflow conditions", UVM_MEDIUM)
        
        // Fill FIFO beyond capacity (should handle gracefully)
        for(int i = 0; i < 80; i++) begin // More than 64-entry FIFO
            uart_send_data(8'hF0 + (i % 16));
            
            if(i % 10 == 0) begin
                axi_register_read(8'h04); // Check status for errors
            end
            
            repeat(5) @(posedge uvm_test_top.clk); // Fast fill
        end
        
        // Test 2: Invalid register access
        `uvm_info("ERROR_INJ_SEQ", "Testing invalid register access", UVM_MEDIUM)
        axi_register_write(8'hFF, 32'hDEADBEEF); // Invalid address
        axi_register_read(8'hFE); // Invalid address
        
        // Test 3: Rapid configuration changes
        `uvm_info("ERROR_INJ_SEQ", "Testing rapid configuration changes", UVM_MEDIUM)
        for(int i = 0; i < 10; i++) begin
            axi_register_write(8'h00, 32'h00000000); // Disable
            repeat(2) @(posedge uvm_test_top.clk);
            axi_register_write(8'h00, 32'h00000007); // Enable
            repeat(2) @(posedge uvm_test_top.clk);
            uart_send_data(8'hAB);
            repeat(20) @(posedge uvm_test_top.clk);
        end
        
        // Check final error status
        axi_register_read(8'h04); // Status register
        axi_register_read(8'h18); // Interrupt status
        
        `uvm_info("ERROR_INJ_SEQ", "=== Error Injection Test Completed ===", UVM_MEDIUM)
    endtask
    
endclass

// Sequence 7: Concurrent Operations Test
class uart_concurrent_ops_seq extends uart_protocol_base_sequence;
    `uvm_object_utils(uart_concurrent_ops_seq)
    
    function new(string name = "uart_concurrent_ops_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        `uvm_info("CONCURRENT_SEQ", "=== Starting Concurrent Operations Test ===", UVM_MEDIUM)
        
        // Initialize UART
        axi_register_write(8'h00, 32'h00000007);
        repeat(20) @(posedge uvm_test_top.clk);
        
        // Fork concurrent operations
        fork
            // Thread 1: Continuous TX data
            begin
                `uvm_info("CONCURRENT_SEQ", "Starting continuous TX thread", UVM_MEDIUM)
                for(int i = 0; i < 100; i++) begin
                    uart_send_data(8'h80 + (i % 32));
                    repeat(25) @(posedge uvm_test_top.clk);
                end
            end
            
            // Thread 2: Periodic status monitoring
            begin
                `uvm_info("CONCURRENT_SEQ", "Starting status monitoring thread", UVM_MEDIUM)
                for(int i = 0; i < 40; i++) begin
                    axi_register_read(8'h04); // Status
                    axi_register_read(8'h1C); // FIFO status
                    repeat(60) @(posedge uvm_test_top.clk);
                end
            end
            
            // Thread 3: Configuration changes
            begin
                `uvm_info("CONCURRENT_SEQ", "Starting configuration thread", UVM_MEDIUM)
                repeat(500) @(posedge uvm_test_top.clk);
                
                // Change interrupt enables
                axi_register_write(8'h14, 32'h0000000F); // Enable all interrupts
                repeat(200) @(posedge uvm_test_top.clk);
                
                axi_register_write(8'h14, 32'h00000000); // Disable interrupts
                repeat(200) @(posedge uvm_test_top.clk);
            end
            
        join
        
        // Final verification
        `uvm_info("CONCURRENT_SEQ", "Performing final verification", UVM_MEDIUM)
        axi_register_read(8'h04); // Final status
        axi_register_read(8'h18); // Final interrupt status
        
        `uvm_info("CONCURRENT_SEQ", "=== Concurrent Operations Test Completed ===", UVM_MEDIUM)
    endtask

endclass

`endif // UART_PROTOCOL_SEQUENCES_SV
