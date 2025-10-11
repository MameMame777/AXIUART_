`timescale 1ns / 1ps

`include "uvm_macros.svh"
import uvm_pkg::*;
import uart_axi4_test_pkg::*;

// Debug Sequences - Used for diagnostic and debugging purposes
// Separate file to avoid circular dependencies

// Simple Write Sequence - Only ONE write command
class uart_debug_simple_write_seq extends uvm_sequence #(uart_frame_transaction);
    
    `uvm_object_utils(uart_debug_simple_write_seq)
    
    function new(string name = "uart_debug_simple_write_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction req;
        
        `uvm_info("DEBUG_WRITE_SEQ", "Starting single write transaction", UVM_LOW)
        
        // Create exactly one write transaction
        `uvm_create(req)
        
        // Set exact values - no randomization
        req.cmd = 8'h01;  // Write, 1 byte, no increment
        req.addr = 32'h1000;  // Base address
        req.data = new[1];
        req.data[0] = 8'h42;  // Predictable data
        
        `uvm_send(req)
        
        `uvm_info("DEBUG_WRITE_SEQ", $sformatf("Sent: CMD=0x%02X, ADDR=0x%08X, DATA=0x%02X", 
                  req.cmd, req.addr, req.data[0]), UVM_LOW)
                  
        `uvm_info("DEBUG_WRITE_SEQ", "Single write sequence completed", UVM_LOW)
    endtask
    
endclass