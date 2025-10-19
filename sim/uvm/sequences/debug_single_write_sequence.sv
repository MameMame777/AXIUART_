`timescale 1ns / 1ps

// Simple Write-Only debug test sequence
class simple_debug_write_sequence_20250923 extends uvm_sequence #(uart_frame_transaction);
    
    `uvm_object_utils(simple_debug_write_sequence_20250923)
    
    function new(string name = "simple_debug_write_sequence_20250923");
        super.new(name);
    endfunction
    
    virtual task body();
        // Pre-allocate dynamic array before randomization (DSIM constraint solver limitation)
        `uvm_create(req)
        req.data = new[1];  // Pre-allocate before constraints
        
        // Apply constraints - use if/else instead of assert to handle failure gracefully
        if (!req.randomize() with {
            req.is_write       == 1'b1;
            req.auto_increment == 1'b0;
            req.size           == 2'b00;
            req.length         == 4'h0;
            req.expect_error   == 1'b1;
            req.addr           == 32'h0000_1000;
            req.data[0]        == 8'h42;  // Direct element constraint (no .size())
        }) begin
            // Randomization failed - set values manually as fallback
            `uvm_warning("DEBUG_SEQ", "Randomization with constraints failed, setting values manually")
            req.is_write = 1'b1;
            req.auto_increment = 1'b0;
            req.size = 2'b00;
            req.length = 4'h0;
            req.expect_error = 1'b1;
            req.addr = 32'h0000_1000;
            req.data[0] = 8'h42;
        end
        
        `uvm_send(req)
        `uvm_info("DEBUG_SEQ", "Sequence completed successfully", UVM_LOW)
    endtask
    
endclass