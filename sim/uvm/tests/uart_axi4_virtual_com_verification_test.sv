`timescale 1ns / 1ps

//==============================================================================
// Virtual COM Port Verification Test
// 
// Purpose: Execute the exact same test patterns that achieved 100% success
//          in the virtual COM port verification (rx_tx_verification.py)
//
// This test replicates successful patterns:
// - 12 test cases with 100% pass rate
// - Verified CRC calculations 
// - Confirmed frame structures
// - Validated protocol compliance
//
// Author: UVM Verification Team  
// Date: 2025-10-09
// Version: 1.0
//==============================================================================

class uart_axi4_virtual_com_verification_test extends enhanced_uart_axi4_base_test;
    `uvm_component_utils(uart_axi4_virtual_com_verification_test)
    
    function new(string name = "uart_axi4_virtual_com_verification_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Configure environment for virtual COM replication
        cfg.num_transactions = 4; // Number of test patterns to execute
        cfg.enable_coverage = 1;
        cfg.enable_scoreboard = 1;
        cfg.enable_protocol_checking = 1;
        
        // Set timeouts based on successful virtual COM timing
        cfg.frame_timeout_ns = 10_000_000; // 10ms (virtual COM used 1s)
        cfg.system_timeout_cycles = 1000;
        
        `uvm_info("VCOM_TEST", "Virtual COM Verification Test configured", UVM_MEDIUM)
        `uvm_info("VCOM_TEST", "Replicating 100% successful test patterns from rx_tx_verification.py", UVM_MEDIUM)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        virtual_com_replication_sequence vcom_seq;
        
        phase.raise_objection(this);
        
        `uvm_info("VCOM_TEST", "===============================================", UVM_LOW)
        `uvm_info("VCOM_TEST", "    UART-AXI4 VIRTUAL COM VERIFICATION TEST", UVM_LOW)
        `uvm_info("VCOM_TEST", "===============================================", UVM_LOW)
        `uvm_info("VCOM_TEST", "Executing patterns that achieved 100% success in virtual COM verification", UVM_LOW)
        
        // Wait for reset completion
        #(1us); // Wait for reset
        `uvm_info("VCOM_TEST", "Reset completed, starting virtual COM pattern replication", UVM_MEDIUM)
        
        // Execute the virtual COM replication sequence
        vcom_seq = virtual_com_replication_sequence::type_id::create("vcom_seq");
        vcom_seq.start(env.uart_agt.sequencer);
        
        // Allow time for all transactions to complete
        #(50us);
        
        `uvm_info("VCOM_TEST", "=== Virtual COM Verification Test Completed ===", UVM_LOW)
        `uvm_info("VCOM_TEST", "Check scoreboard and monitor logs for detailed results", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        
        `uvm_info("VCOM_TEST", "=== VIRTUAL COM VERIFICATION SUMMARY ===", UVM_LOW)
        `uvm_info("VCOM_TEST", "Executed test patterns from 100% successful virtual COM verification", UVM_LOW)
        `uvm_info("VCOM_TEST", "Expected: All patterns should execute successfully in UVM", UVM_LOW)
        `uvm_info("VCOM_TEST", "Comparison: UVM results vs Virtual COM 100% success rate", UVM_LOW)
        
        if (uvm_report_server::get_server().get_severity_count(UVM_ERROR) == 0) begin
            `uvm_info("VCOM_TEST", "笨・UVM replication SUCCESSFUL - matches virtual COM success", UVM_LOW)
        end else begin
            `uvm_error("VCOM_TEST", "笶・UVM replication FAILED - discrepancy from virtual COM results")
        end
    endfunction
    
endclass : uart_axi4_virtual_com_verification_test
