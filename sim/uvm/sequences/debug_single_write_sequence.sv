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

        // Create exactly one write transaction aligned with protocol encoding
        `uvm_create(req)

        req.is_write       = 1'b1;
        req.auto_increment = 1'b0;
        req.size           = 2'b00;   // 8-bit access
        req.length         = 4'h0;    // length=0 encodes one beat
        req.expect_error   = 1'b0;
        req.addr           = 32'h0000_1000;  // Base address (REG_CONTROL)

        req.data = new[1];
        req.data[0] = 8'h42;          // Predictable data payload

        req.build_cmd();
        req.calculate_crc();

        `uvm_send(req)
        
        `uvm_info("DEBUG_WRITE_SEQ_2023", $sformatf("Sent: CMD=0x%02X, ADDR=0x%08X, DATA=0x%02X", 
                  req.cmd, req.addr, req.data[0]), UVM_MEDIUM)
                  
        `uvm_info("DEBUG_WRITE_SEQ_2023", "SINGLE write sequence completed", UVM_MEDIUM)
    endtask
    
endclass