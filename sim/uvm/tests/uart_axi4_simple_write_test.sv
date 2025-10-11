`timescale 1ns / 1ps

`include "uvm_macros.svh"
import uvm_pkg::*;
import uart_axi4_test_pkg::*;

// Simple Write-Only Test for UART-AXI4 Bridge
class uart_axi4_simple_write_test extends enhanced_uart_axi4_base_test;
    
    `uvm_component_utils(uart_axi4_simple_write_test)
    
    function new(string name = "uart_axi4_simple_write_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        uart_debug_simple_write_seq seq;  // Rename to avoid conflict
        
        phase.raise_objection(this);
        
        `uvm_info("SIMPLE_WRITE_TEST", "==============================================", UVM_LOW)
        `uvm_info("SIMPLE_WRITE_TEST", "     UART-AXI4 SIMPLE WRITE TEST", UVM_LOW)
        `uvm_info("SIMPLE_WRITE_TEST", "==============================================", UVM_LOW)
        `uvm_info("SIMPLE_WRITE_TEST", "Test focused on single write command", UVM_LOW)
        
        seq = uart_debug_simple_write_seq::type_id::create("seq");
        seq.start(env.uart_agt.sequencer);
        
        `uvm_info("SIMPLE_WRITE_TEST", "=== Simple Write Test Completed ===", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass

// NOTE: uart_debug_simple_write_seq is defined in sequences/debug_sequences.sv
// to avoid duplicate definition conflicts
