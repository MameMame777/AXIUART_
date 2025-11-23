`timescale 1ns / 1ps

class uart_reset_sequence extends uvm_sequence #(uart_frame_transaction);
    `uvm_object_utils(uart_reset_sequence)

    // Configuration parameter for reset duration (clock cycles)
    int reset_cycles = 100;

    function new(string name = "uart_reset_sequence");
        super.new(name);
    endfunction

    virtual task body();
        uart_frame_transaction req;
        
        `uvm_info(get_type_name(), $sformatf("Starting reset sequence with %0d cycles", reset_cycles), UVM_MEDIUM)
        
        req = uart_frame_transaction::type_id::create("reset_req");
        
        start_item(req);
        
        // Configure as reset transaction
        req.is_reset = 1;
        req.reset_cycles = this.reset_cycles;
        
        finish_item(req);
        
        `uvm_info(get_type_name(), $sformatf("Reset sequence completed (%0d cycles)", reset_cycles), UVM_MEDIUM)
    endtask

endclass
