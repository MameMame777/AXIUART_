`timescale 1ns / 1ps

`include "uvm_macros.svh"
import uvm_pkg::*;
import uart_axi4_test_pkg::*;

// Debug Sequences - Used for diagnostic and debugging purposes
// Separate file to avoid circular dependencies

// Simple Write Sequence - Only ONE write command
class uart_debug_simple_write_seq extends uvm_sequence #(uart_frame_transaction);
    
    `uvm_object_utils(uart_debug_simple_write_seq)
    
    // UVM phase handle for objection management
    uvm_phase starting_phase;
    
    function new(string name = "uart_debug_simple_write_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction req;
        
        // NOTE: Objection management handled by calling test - do NOT raise here
        // This sequence is called from test's run_phase where objection is already raised
        
        `uvm_info("DEBUG_WRITE_SEQ", "[OK] ===== DEBUG_SEQ BODY ENTERED =====", UVM_LOW)
        `uvm_info("DEBUG_WRITE_SEQ", "Starting single write transaction", UVM_LOW)
        `uvm_info("DEBUG_WRITE_SEQ", $sformatf("Before create at time=%0t", $time), UVM_LOW)
        
        // Create exactly one write transaction
        req = uart_frame_transaction::type_id::create("req");
        
        `uvm_info("DEBUG_WRITE_SEQ", $sformatf("After create at time=%0t", $time), UVM_LOW)
        
        // Start the transaction (signals sequencer)
        `uvm_info("DEBUG_WRITE_SEQ", "[DIAGNOSTIC] About to call start_item()...", UVM_LOW);
        start_item(req);
        `uvm_info("DEBUG_WRITE_SEQ", "[OK] start_item() returned", UVM_LOW);
        
        `uvm_info("DEBUG_WRITE_SEQ", $sformatf("After start_item at time=%0t", $time), UVM_LOW)
        
        // ★ FIX: Only randomize rand fields, manually assign non-rand fields
        if (!req.randomize() with {
            sof == SOF_HOST_TO_DEVICE;  // 0xA5 - rand field
            cmd == 8'h00;               // Write command - rand field
        }) begin
            `uvm_fatal("DEBUG_WRITE_SEQ", "Transaction randomization failed")
        end
        
        // Manually assign non-rand fields AFTER randomization
        req.addr = 32'h1000;
        req.data = new[1];
        req.data[0] = 8'h42;
        
        `uvm_info("DEBUG_WRITE_SEQ", $sformatf("Before finish_item at time=%0t", $time), UVM_LOW)
        
        // Send transaction to driver
        finish_item(req);
        
        `uvm_info("DEBUG_WRITE_SEQ", $sformatf("After finish_item at time=%0t", $time), UVM_LOW)
        `uvm_info("DEBUG_WRITE_SEQ", $sformatf("Sent: CMD=0x%02X, ADDR=0x%08X, DATA=0x%02X", 
                  req.cmd, req.addr, req.data[0]), UVM_LOW)
                  
        `uvm_info("DEBUG_WRITE_SEQ", "Single write sequence completed", UVM_LOW)
        
        // NOTE: Objection dropped by calling test - do NOT drop here
    endtask
    
endclass