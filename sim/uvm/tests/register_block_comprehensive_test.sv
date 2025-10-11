//==============================================================================
// Register Block Comprehensive Test
// 
// Purpose: Execute the comprehensive register test sequence to verify
//          all register functionality including write/read operations
//
// Author: UVM Verification Team
// Date: 2025-10-10
// Version: 1.0
//==============================================================================

`timescale 1ns / 1ps

class register_block_comprehensive_test extends enhanced_uart_axi4_base_test;
    `uvm_component_utils(register_block_comprehensive_test)
    
    function new(string name = "register_block_comprehensive_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        configure_test_specific_reporting();
        `uvm_info("TEST", "=== Register Block Comprehensive Test ===", UVM_LOW)
        `uvm_info("TEST", "Testing ALL register functions with write/read verification", UVM_LOW)
    endfunction

    virtual task run_phase(uvm_phase phase);
        register_block_comprehensive_sequence comp_seq;
        
        phase.raise_objection(this);
        
        `uvm_info("TEST", "Starting comprehensive register block testing", UVM_LOW)
        
        // Create and execute comprehensive sequence
        comp_seq = register_block_comprehensive_sequence::type_id::create("comp_seq");
        comp_seq.start(env.uart_agt.sequencer);
        
        `uvm_info("TEST", "=== Register Block Comprehensive Test Complete ===", UVM_LOW)
        
        phase.drop_objection(this);
    endtask

endclass : register_block_comprehensive_test
