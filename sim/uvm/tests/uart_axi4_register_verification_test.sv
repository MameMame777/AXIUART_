`timescale 1ns / 1ps

// =======================================================================
// Test Register Write/Read Verification Test
// 
// Purpose: Verify that register write operations actually update register values
//          and that subsequent reads return the written values
// 
// =======================================================================

class uart_axi4_register_verification_test extends enhanced_uart_axi4_base_test;

    `uvm_component_utils(uart_axi4_register_verification_test)

    function new(string name = "uart_axi4_register_verification_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        uart_axi4_register_simple_sequence reg_verify_seq;
        
        phase.raise_objection(this);
        
        `uvm_info("TEST", "=== Starting Register Write/Read Verification Test ===", UVM_LOW)
        
        // Create and run the simple sequence
        reg_verify_seq = uart_axi4_register_simple_sequence::type_id::create("reg_verify_seq");
        reg_verify_seq.start(env.uart_agt.sequencer);
        
        `uvm_info("TEST", "=== Register Write/Read Verification Test Complete ===", UVM_LOW)
        
        phase.drop_objection(this);
    endtask

endclass
