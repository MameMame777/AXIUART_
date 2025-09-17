`include "uvm_macros.svh"
import uvm_pkg::*;
`include "uart_axi_register_sequences.sv"

`timescale 1ns / 1ps

// UART Data Path Extension Sequence - extends comprehensive register sequence
class uart_data_path_extension_seq extends uart_axi_comprehensive_reg_seq;
    `uvm_object_utils(uart_data_path_extension_seq)
    
    function new(string name = "uart_data_path_extension_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        `uvm_info("DATA_PATH_EXT", "=== Starting UART Data Path Extension ===", UVM_MEDIUM)
        
        // First run the complete proven register verification
        super.body();
        
        `uvm_info("DATA_PATH_EXT", "Register verification completed - adding data transmission tests", UVM_MEDIUM)
        
        // Extended testing phases
        run_basic_data_transmission();
        run_data_pattern_tests();
        run_status_monitoring();
        
        `uvm_info("DATA_PATH_EXT", "=== UART Data Path Extension Completed ===", UVM_MEDIUM)
    endtask
    
    // Basic UART data transmission test
    virtual task run_basic_data_transmission();
        bit [7:0] test_data[] = {8'h55, 8'hAA, 8'h00, 8'hFF, 8'h0F, 8'hF0};
        bit [31:0] status_data;
        
        `uvm_info("DATA_PATH_EXT", "Phase 1: Basic Data Transmission", UVM_MEDIUM)
        
        // Configure UART for reliable transmission
        write_register(8'h0C, 32'h000001A1); // Set baud rate divider (9600 baud)
        write_register(8'h00, 32'h00000007); // Enable UART, TX, RX
        #10us; // Configuration settling time
        
        // Transmit test data bytes
        foreach(test_data[i]) begin
            `uvm_info("DATA_PATH_EXT", $sformatf("Transmitting byte[%0d]: 0x%02X", i, test_data[i]), UVM_MEDIUM)
            
            write_register(8'h08, {24'h0, test_data[i]});
            #2ms; // Allow time for UART transmission (>1ms @ 9600 baud)
            
            // Check status after transmission
            read_register(8'h04, status_data);
            `uvm_info("DATA_PATH_EXT", $sformatf("Status post-TX: 0x%08X", status_data), UVM_MEDIUM)
            
            #500us; // Inter-byte delay
        end
        
        `uvm_info("DATA_PATH_EXT", "Basic data transmission completed", UVM_MEDIUM)
    endtask
    
    // Data pattern testing
    virtual task run_data_pattern_tests();
        bit [31:0] status_data;
        
        `uvm_info("DATA_PATH_EXT", "Phase 2: Data Pattern Testing", UVM_MEDIUM)
        
        // Pattern A: Sequential increment
        `uvm_info("DATA_PATH_EXT", "Testing sequential pattern (0x00-0x0F)", UVM_MEDIUM)
        for(int i = 0; i < 16; i++) begin
            write_register(8'h08, {24'h0, i[7:0]});
            #1500us;
            
            if(i % 4 == 0) begin
                read_register(8'h04, status_data);
                `uvm_info("DATA_PATH_EXT", $sformatf("Sequential[%0d]: Status=0x%08X", i, status_data), UVM_MEDIUM)
            end
        end
        
        // Pattern B: Walking bits
        `uvm_info("DATA_PATH_EXT", "Testing walking bits pattern", UVM_MEDIUM)
        for(int j = 0; j < 8; j++) begin
            bit [7:0] walking_bit = 1 << j;
            `uvm_info("DATA_PATH_EXT", $sformatf("Walking bit[%0d]: 0x%02X", j, walking_bit), UVM_MEDIUM)
            write_register(8'h08, {24'h0, walking_bit});
            #1500us;
        end
        
        // Pattern C: ASCII printable characters
        `uvm_info("DATA_PATH_EXT", "Testing ASCII pattern ('A'-'J')", UVM_MEDIUM)
        for(int k = 8'h41; k <= 8'h4A; k++) begin // 'A' to 'J'
            `uvm_info("DATA_PATH_EXT", $sformatf("ASCII[%c]: 0x%02X", k, k), UVM_MEDIUM)
            write_register(8'h08, {24'h0, k[7:0]});
            #1500us;
        end
        
        `uvm_info("DATA_PATH_EXT", "Data pattern testing completed", UVM_MEDIUM)
    endtask
    
    // Status monitoring during transmission
    virtual task run_status_monitoring();
        bit [31:0] status_data;
        
        `uvm_info("DATA_PATH_EXT", "Phase 3: Status Monitoring", UVM_MEDIUM)
        
        for(int cycle = 0; cycle < 6; cycle++) begin
            `uvm_info("DATA_PATH_EXT", $sformatf("Status monitoring cycle %0d", cycle), UVM_MEDIUM)
            
            // Pre-transmission status
            read_register(8'h04, status_data);
            `uvm_info("DATA_PATH_EXT", $sformatf("Pre-TX status: 0x%08X", status_data), UVM_MEDIUM)
            
            // Transmit data
            write_register(8'h08, {24'h0, 8'hB0 + cycle}); // Pattern 0xB0-0xB5
            
            // Monitor status during transmission
            #300us;
            read_register(8'h04, status_data);
            `uvm_info("DATA_PATH_EXT", $sformatf("Mid-TX status: 0x%08X", status_data), UVM_MEDIUM)
            
            #700us;
            read_register(8'h04, status_data);
            `uvm_info("DATA_PATH_EXT", $sformatf("Post-TX status: 0x%08X", status_data), UVM_MEDIUM)
            
            #1ms; // Cycle completion delay
        end
        
        `uvm_info("DATA_PATH_EXT", "Status monitoring completed", UVM_MEDIUM)
    endtask
    
endclass

// Test class that runs the data path extension
class uart_axi_data_path_test extends uvm_test;
    `uvm_component_utils(uart_axi_data_path_test)
    
    function new(string name = "uart_axi_data_path_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        uart_data_path_extension_seq data_ext_seq;
        uvm_sequencer_base found_sequencer;
        
        phase.raise_objection(this);
        
        `uvm_info("DATA_PATH_TEST", "=== Enhanced UART Data Path Test Started ===", UVM_LOW)
        
        // Wait for reset release
        #200ns;
        
        `uvm_info("DATA_PATH_TEST", "Finding sequencer for data path extension", UVM_LOW)
        
        // Find sequencer in the testbench hierarchy
        if (!uvm_config_db#(uvm_sequencer_base)::get(this, "", "sequencer", found_sequencer)) begin
            `uvm_warning("DATA_PATH_TEST", "No sequencer found in config DB, using virtual sequence approach")
        end
        
        // Execute extended sequence (register + data path)
        data_ext_seq = uart_data_path_extension_seq::type_id::create("data_ext_seq");
        
        if (found_sequencer != null) begin
            data_ext_seq.start(found_sequencer);
        end else begin
            // Alternative: Execute as virtual sequence with global scope
            `uvm_info("DATA_PATH_TEST", "Executing as virtual sequence", UVM_LOW)
            data_ext_seq.start(null);
        end
        
        `uvm_info("DATA_PATH_TEST", "=== Enhanced UART Data Path Test Completed ===", UVM_LOW)
        
        // Report results
        report_enhanced_results();
        
        phase.drop_objection(this);
    endtask
    
    // Enhanced result reporting
    virtual task report_enhanced_results();
        uvm_report_server server;
        int err_count, warn_count;
        
        server = uvm_report_server::get_server();
        err_count = server.get_severity_count(UVM_ERROR);
        warn_count = server.get_severity_count(UVM_WARNING);
        
        `uvm_info("ENHANCED_RESULTS", "=== UART Data Path Test Results ===", UVM_LOW)
        `uvm_info("ENHANCED_RESULTS", $sformatf("Errors: %0d, Warnings: %0d", err_count, warn_count), UVM_LOW)
        
        if (err_count == 0) begin
            `uvm_info("ENHANCED_RESULTS", "✅ UART DATA PATH TESTING PASSED", UVM_LOW)
        end else begin
            `uvm_error("ENHANCED_RESULTS", $sformatf("❌ UART DATA PATH TESTING FAILED (%0d errors)", err_count))
        end
    endtask
    
endclass
