`timescale 1ns / 1ps

// Basic UART Test
// Tests the simplified AXIUART system with UART-only external interface

import uvm_pkg::*;
`include "uvm_macros.svh"

class uart_basic_test extends uvm_test;
    `uvm_component_utils(uart_basic_test)
    
    virtual uart_if uart_vif;
    
    function new(string name = "uart_basic_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if (!uvm_config_db#(virtual uart_if)::get(this, "", "uart_vif", uart_vif)) begin
            `uvm_fatal("CONFIG", "Cannot get uart_vif from config DB")
        end
    endfunction
    
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        `uvm_info("TEST", "Starting UART Basic Test", UVM_LOW)
        
        // Wait for reset deassertion
        wait(!uart_vif.rst);
        #1us;
        
        `uvm_info("TEST", "System reset deasserted", UVM_LOW)
        
        // Simple test - just check that UART TX is idle high
        if (uart_vif.uart_tx !== 1'b1) begin
            `uvm_error("TEST", "UART TX not idle high after reset")
        end else begin
            `uvm_info("TEST", "UART TX correctly idle high", UVM_LOW)
        end
        
        // Wait a bit more
        #10us;
        
        `uvm_info("TEST", "UART Basic Test completed", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass