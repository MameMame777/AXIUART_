`timescale 1ns / 1ps

//=============================================================================
// Register Sweep Toggle Coverage Test
// Purpose: Execute dedicated register access sequence to improve toggle coverage
// Target: Toggle Coverage 14% → 85%+
//=============================================================================

`ifndef AXIUART_REGISTER_TOGGLE_TEST_SV
`define AXIUART_REGISTER_TOGGLE_TEST_SV

import uvm_pkg::*;
import uart_axi4_test_pkg::*;

// Include register sweep sequence directly here to avoid redefinition
`include "../sequences/axiuart_register_sweep_sequence.sv"

class axiuart_register_toggle_test extends uart_axi4_base_test;
    `uvm_component_utils(axiuart_register_toggle_test)
    
    function new(string name = "axiuart_register_toggle_test", uvm_component parent = null);
        super.new(name, parent);
        `uvm_info("TOGGLE_TEST", "Register Toggle Coverage Test initialized", UVM_LOW)
    endfunction
    
    // Enhanced coverage configuration
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Force coverage collection enable
        cfg.enable_coverage = 1;
        cfg.enable_scoreboard = 1;
        cfg.enable_protocol_checking = 1;
        
        // Extended test parameters for comprehensive register access
        cfg.num_transactions = 500;  // Increased for better toggle coverage
        cfg.system_timeout_cycles = 5000;
        
        `uvm_info("TOGGLE_TEST", "Enhanced configuration for toggle coverage improvement", UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        axiuart_register_sweep_sequence reg_sweep_seq;
        
        phase.raise_objection(this);
        
        `uvm_info("TOGGLE_TEST", "=========================================", UVM_LOW)
        `uvm_info("TOGGLE_TEST", "    REGISTER TOGGLE COVERAGE TEST", UVM_LOW)
        `uvm_info("TOGGLE_TEST", "=========================================", UVM_LOW)
        `uvm_info("TOGGLE_TEST", "Target: Toggle Coverage 14% → 85%+", UVM_LOW)
        
        // Execute register sweep sequence
        reg_sweep_seq = axiuart_register_sweep_sequence::type_id::create("reg_sweep_seq");
        
        `uvm_info("TOGGLE_TEST", "Starting comprehensive register sweep...", UVM_LOW)
        reg_sweep_seq.start(env.uart_agt.sequencer);
        
        // Wait for completion
        #1000000;  // 1ms wait to ensure all operations complete
        
        `uvm_info("TOGGLE_TEST", "=== Register Toggle Test Completed ===", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass

`endif // AXIUART_REGISTER_TOGGLE_TEST_SV