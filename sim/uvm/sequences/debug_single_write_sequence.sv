`timescale 1ns / 1ps

// Simple Write-Only debug test sequence
class simple_debug_write_sequence_20250923 extends uvm_sequence #(uart_frame_transaction);
    
    `uvm_object_utils(simple_debug_write_sequence_20250923)
    
    function new(string name = "simple_debug_write_sequence_20250923");
        super.new(name);
    endfunction
    
    virtual task body();
        // UVM Best Practice Pattern (from reference/uvm_original/sequences)
        // Direct field assignment - no randomization with inline constraints
        `uvm_create(req)
        
        // Set transaction fields directly (avoids DSIM constraint solver limitations)
        req.is_write       = 1'b1;
        req.auto_increment = 1'b0;
        req.size           = 2'b00;
        req.length         = 4'h0;
        req.expect_error   = 1'b1;
        req.addr           = 32'h0000_1000;
        
        // Allocate and initialize data array
        req.data = new[1];
        req.data[0] = 8'h42;
        
        `uvm_send(req)
        `uvm_info("DEBUG_SEQ", "Sequence completed successfully", UVM_LOW)
    endtask
    
endclass