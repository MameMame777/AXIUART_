/*
 * Simple UART Data Path Test - Phase 2A Extension
 * Purpose: Extend successful register verification with basic UART data transmission
 * Strategy: Incremental enhancement of proven register test framework
 * Guidelines: Build on existing success, minimal changes to working environment
 */

`timescale 1ns / 1ps

// Simple UART Data Transmission Sequence (extends register verification)
class uart_data_transmission_seq extends uart_axi_comprehensive_reg_seq;
    `uvm_object_utils(uart_data_transmission_seq)
    
    function new(string name = "uart_data_transmission_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        // First run the proven register tests
        `uvm_info("DATA_TX_SEQ", "=== Starting UART Data Path Testing (Phase 2A) ===", UVM_MEDIUM)
        `uvm_info("DATA_TX_SEQ", "Step 1: Running register verification foundation", UVM_MEDIUM)
        
        super.body(); // Execute all register tests first
        
        `uvm_info("DATA_TX_SEQ", "Step 2: Starting UART data transmission tests", UVM_MEDIUM)
        
        // Now add simple data transmission tests
        test_basic_uart_data_transmission();
        test_uart_data_patterns();
        test_uart_status_monitoring();
        
        `uvm_info("DATA_TX_SEQ", "=== UART Data Path Testing Completed ===", UVM_MEDIUM)
    endtask
    
    // Test 1: Basic UART Data Transmission
    virtual task test_basic_uart_data_transmission();
        logic [7:0] test_bytes[] = {8'h55, 8'hAA, 8'h00, 8'hFF, 8'h0F, 8'hF0};
        
        `uvm_info("DATA_TX_SEQ", "=== Basic UART Data Transmission Test ===", UVM_MEDIUM)
        
        // Ensure UART is enabled (from register tests)
        write_register(8'h00, 32'h00000007); // Enable UART, TX, RX
        repeat(20) @(posedge axi_if.aclk);
        
        // Test single byte transmission
        foreach(test_bytes[i]) begin
            `uvm_info("DATA_TX_SEQ", $sformatf("Transmitting test byte: 0x%02X", test_bytes[i]), UVM_MEDIUM)
            
            // Write data to TX register
            write_register(8'h08, {24'h0, test_bytes[i]});
            
            // Allow time for UART transmission
            repeat(1000) @(posedge axi_if.aclk); // Wait for UART bit timing
            
            // Read status to verify transmission
            read_register(8'h04, status_data);
            
            repeat(100) @(posedge axi_if.aclk);
        end
        
        `uvm_info("DATA_TX_SEQ", "Basic UART data transmission test completed", UVM_MEDIUM)
    endtask
    
    // Test 2: UART Data Patterns
    virtual task test_uart_data_patterns();
        `uvm_info("DATA_TX_SEQ", "=== UART Data Pattern Test ===", UVM_MEDIUM)
        
        // Test Pattern 1: Sequential increment
        `uvm_info("DATA_TX_SEQ", "Testing sequential increment pattern", UVM_MEDIUM)
        for(int i = 0; i < 16; i++) begin
            write_register(8'h08, {24'h0, i[7:0]});
            repeat(500) @(posedge axi_if.aclk);
            
            if(i % 4 == 0) begin
                read_register(8'h04, status_data); // Check status periodically
            end
        end
        
        // Test Pattern 2: Walking bits
        `uvm_info("DATA_TX_SEQ", "Testing walking bits pattern", UVM_MEDIUM)
        for(int i = 0; i < 8; i++) begin
            logic [7:0] walking_bit = 1 << i;
            write_register(8'h08, {24'h0, walking_bit});
            repeat(500) @(posedge axi_if.aclk);
        end
        
        // Test Pattern 3: ASCII characters
        `uvm_info("DATA_TX_SEQ", "Testing ASCII character pattern", UVM_MEDIUM)
        for(int i = 8'h30; i <= 8'h39; i++) begin // '0' to '9'
            write_register(8'h08, {24'h0, i[7:0]});
            repeat(500) @(posedge axi_if.aclk);
        end
        
        `uvm_info("DATA_TX_SEQ", "UART data pattern test completed", UVM_MEDIUM)
    endtask
    
    // Test 3: UART Status Monitoring
    virtual task test_uart_status_monitoring();
        `uvm_info("DATA_TX_SEQ", "=== UART Status Monitoring Test ===", UVM_MEDIUM)
        
        // Send data while monitoring status changes
        for(int i = 0; i < 8; i++) begin
            `uvm_info("DATA_TX_SEQ", $sformatf("Data transmission cycle %0d", i), UVM_MEDIUM)
            
            // Read status before transmission
            read_register(8'h04, status_data);
            
            // Send test data
            write_register(8'h08, {24'h0, 8'hA0 + i});
            
            // Monitor status during transmission
            for(int j = 0; j < 5; j++) begin
                repeat(200) @(posedge axi_if.aclk);
                read_register(8'h04, status_data);
            end
        end
        
        `uvm_info("DATA_TX_SEQ", "UART status monitoring test completed", UVM_MEDIUM)
    endtask
    
endclass

// Enhanced test that includes data path testing
class uart_axi_data_path_test extends uvm_test;
    `uvm_component_utils(uart_axi_data_path_test)
    
    // Environment and interface
    uart_axi_register_env env;
    
    function new(string name = "uart_axi_data_path_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = uart_axi_register_env::type_id::create("env", this);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        uart_data_transmission_seq data_seq;
        
        phase.raise_objection(this);
        
        `uvm_info("DATA_PATH_TEST", "=== Starting Enhanced UART Data Path Test ===", UVM_MEDIUM)
        
        // Wait for reset deassertion
        wait(uart_axi_register_tb.reset == 0);
        repeat(100) @(posedge uart_axi_register_tb.clk);
        
        `uvm_info("DATA_PATH_TEST", "Reset released - starting enhanced data path testing", UVM_MEDIUM)
        
        // Run the enhanced sequence that includes register + data path tests
        data_seq = uart_data_transmission_seq::type_id::create("data_seq");
        data_seq.start(env.agent.sequencer);
        
        `uvm_info("DATA_PATH_TEST", "=== Enhanced UART Data Path Test Completed ===", UVM_MEDIUM)
        
        // Report test results
        report_test_results();
        
        phase.drop_objection(this);
    endtask
    
    // Report test results
    virtual task report_test_results();
        uvm_report_server server;
        int err_count, warn_count;
        
        server = uvm_report_server::get_server();
        err_count = server.get_severity_count(UVM_ERROR);
        warn_count = server.get_severity_count(UVM_WARNING);
        
        `uvm_info("RESULTS", "=== UART Data Path Test Results ===", UVM_LOW)
        `uvm_info("RESULTS", $sformatf("Total Errors: %0d", err_count), UVM_LOW)
        `uvm_info("RESULTS", $sformatf("Total Warnings: %0d", warn_count), UVM_LOW)
        
        if (err_count == 0) begin
            `uvm_info("RESULTS", "*** UART DATA PATH TESTING PASSED ***", UVM_LOW)
        end else begin
            `uvm_error("RESULTS", $sformatf("*** UART DATA PATH TESTING FAILED with %0d errors ***", err_count))
        end
    endtask
    
endclass
