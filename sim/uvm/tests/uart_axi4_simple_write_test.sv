`timescale 1ns / 1ps

// Simple Write-Only Test for UART-AXI4 Bridge
class uart_axi4_simple_write_test extends uart_axi4_base_test;
    
    `uvm_component_utils(uart_axi4_simple_write_test)
    
    function new(string name = "uart_axi4_simple_write_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        uart_debug_write_seq seq;
        
        phase.raise_objection(this);
        
        `uvm_info("SIMPLE_WRITE_TEST", "==============================================", UVM_LOW)
        `uvm_info("SIMPLE_WRITE_TEST", "     UART-AXI4 SIMPLE WRITE TEST", UVM_LOW)
        `uvm_info("SIMPLE_WRITE_TEST", "==============================================", UVM_LOW)
        `uvm_info("SIMPLE_WRITE_TEST", "Test focused on single write command", UVM_LOW)
        
        seq = uart_debug_write_seq::type_id::create("debug_write_seq");
        seq.start(env.uart_agt.sequencer);
        
        `uvm_info("SIMPLE_WRITE_TEST", "=== Simple Write Test Completed ===", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass

// Simple Write Sequence - Only ONE write command
class uart_debug_write_seq extends uvm_sequence #(uart_frame_transaction);
    
    `uvm_object_utils(uart_debug_write_seq)
    
    function new(string name = "uart_debug_write_seq");
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