`timescale 1ns / 1ps

// Simple Write-Only debug test sequence
class simple_debug_write_sequence_20250923 extends uvm_sequence #(uart_frame_transaction);
    
    `uvm_object_utils(simple_debug_write_sequence_20250923)
    
    function new(string name = "simple_debug_write_sequence_20250923");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction req;
        
        `uvm_info("DEBUG_WRITE_SEQ_2023", "Starting SINGLE write transaction debug", UVM_MEDIUM)
        
        // Create exactly one write transaction
        `uvm_create(req)
        
        // Set exact values - no randomization
        req.cmd = 8'h01;  // Write, 1 byte, no increment
        req.addr = 32'h1000;  // Base address (REG_CONTROL)
        req.data = new[1];
        req.data[0] = 8'h42;  // Predictable data
        
        `uvm_send(req)
        
        `uvm_info("DEBUG_WRITE_SEQ_2023", $sformatf("Sent: CMD=0x%02X, ADDR=0x%08X, DATA=0x%02X", 
                  req.cmd, req.addr, req.data[0]), UVM_MEDIUM)
                  
        `uvm_info("DEBUG_WRITE_SEQ_2023", "SINGLE write sequence completed", UVM_MEDIUM)
    endtask
    
endclass