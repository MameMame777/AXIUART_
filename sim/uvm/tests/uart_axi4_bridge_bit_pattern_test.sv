`timescale 1ns / 1ps

// =======================================================================
// UART-AXI4 Bridge Bit Pattern Register Verification Test
// 
// Purpose: Verify complete UART→AXI4→Register data flow with bit patterns
//          that prove actual write/read functionality (all5, allA, allF)
// 
// This test verifies the COMPLETE data path:
// 1. UART RX receives frame
// 2. Frame Parser extracts AXI transaction
// 3. AXI4-Lite Master writes to register
// 4. Register stores value
// 5. AXI4-Lite Master reads from register  
// 6. Frame Builder constructs response
// 7. UART TX sends response
// =======================================================================

class uart_axi4_bridge_bit_pattern_test extends uart_axi4_base_test;

    `uvm_component_utils(uart_axi4_bridge_bit_pattern_test)

    function new(string name = "uart_axi4_bridge_bit_pattern_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        uart_axi4_register_bit_pattern_sequence bit_pattern_seq;
        
        phase.raise_objection(this);
        
        `uvm_info("TEST", "=== Starting UART-AXI Bridge Bit Pattern Register Test ===", UVM_LOW)
        `uvm_info("TEST", "Testing complete data flow: UART→Frame Parser→AXI Master→Register", UVM_LOW)
        `uvm_info("TEST", "Using bit validation patterns: all5, allA, allF", UVM_LOW)
        
        // Wait for system to stabilize
        #50000ns;
        
        // Create and run the bit pattern sequence
        bit_pattern_seq = uart_axi4_register_bit_pattern_sequence::type_id::create("bit_pattern_seq");
        bit_pattern_seq.start(env.uart_agt.sequencer);
        
        // Allow time for final transactions to complete
        #500000ns;
        
        `uvm_info("TEST", "=== UART-AXI Bridge Bit Pattern Register Test Complete ===", UVM_LOW)
        
        phase.drop_objection(this);
    endtask

endclass