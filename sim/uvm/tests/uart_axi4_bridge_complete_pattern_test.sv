`timescale 1ns / 1ps

// =======================================================================
// UART-AXI4-Lite Bridge Complete Pattern Test
// 
// Purpose: Test complete UART->AXI4->Register data flow with all5/allA/allF patterns
//          Verify that register writes via UART actually update register values
//          and that subsequent reads return the written values (NOT initial values)
// =======================================================================

class uart_axi4_bridge_complete_pattern_test extends enhanced_uart_axi4_base_test;

    `uvm_component_utils(uart_axi4_bridge_complete_pattern_test)

    function new(string name = "uart_axi4_bridge_complete_pattern_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        uart_axi4_register_pattern_sequence pattern_seq;
        
        phase.raise_objection(this);
        
        `uvm_info("COMPLETE_PATTERN_TEST", "=== UART-AXI4-Bridge Complete Pattern Test START ===", UVM_LOW)
        
        // Wait for system initialization
        #50000ns;
        
        // Create and run the pattern test sequence
        pattern_seq = uart_axi4_register_pattern_sequence::type_id::create("pattern_seq");
        if (pattern_seq == null) begin
            `uvm_fatal("COMPLETE_PATTERN_TEST", "Failed to create uart_axi4_register_pattern_sequence")
        end
        
        `uvm_info("COMPLETE_PATTERN_TEST", "Starting UART-AXI4 Register Pattern Sequence...", UVM_LOW)
        pattern_seq.start(env.uart_agt.sequencer);
        
        // Additional wait for all transactions to complete
        #100000ns;
        
        `uvm_info("COMPLETE_PATTERN_TEST", "=== UART-AXI4-Bridge Complete Pattern Test COMPLETE ===", UVM_LOW)
        
        phase.drop_objection(this);
    endtask

endclass
