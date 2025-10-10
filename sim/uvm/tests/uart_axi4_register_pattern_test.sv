`timescale 1ns / 1ps

// =============================================================================
// uart_axi4_register_pattern_test.sv
// Complete UART-AXI4-Lite Register Pattern Test
// 
// Purpose: Test complete data flow: UART -> Frame Parser -> AXI4-Lite Master -> Register Block
//          Verify register writes with all5, allA, allF patterns (NOT initial values)
// =============================================================================

class uart_axi4_register_pattern_test extends uart_axi4_base_test;

    `uvm_component_utils(uart_axi4_register_pattern_test)

    function new(string name = "uart_axi4_register_pattern_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        uart_axi4_register_pattern_sequence pattern_seq;
        
        phase.raise_objection(this);
        
        `uvm_info("TEST", "==================================================", UVM_LOW)
        `uvm_info("TEST", "COMPLETE UART-AXI4-REGISTER PATTERN VERIFICATION", UVM_LOW)
        `uvm_info("TEST", "Testing: UART -> Bridge -> AXI4 -> Register Block", UVM_LOW)
        `uvm_info("TEST", "Patterns: all5, allA, allF, custom (NOT initial values)", UVM_LOW)
        `uvm_info("TEST", "==================================================", UVM_LOW)
        
        // Create and run the pattern test sequence
        pattern_seq = uart_axi4_register_pattern_sequence::type_id::create("pattern_seq");
        pattern_seq.start(env.uart_agt.sequencer);
        
        `uvm_info("TEST", "==================================================", UVM_LOW)
        `uvm_info("TEST", "COMPLETE UART-AXI4-REGISTER PATTERN TEST FINISHED", UVM_LOW)
        `uvm_info("TEST", "==================================================", UVM_LOW)
        
        phase.drop_objection(this);
    endtask

endclass