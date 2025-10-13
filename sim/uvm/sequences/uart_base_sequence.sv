`timescale 1ns / 1ps

// UART UVM Base Sequence
// Updated for Phase 4 compliance
// Date: October 13, 2025
// Description: Base sequence for UART transactions with Phase 4 enhancements

`ifndef UART_BASE_SEQUENCE_SV
`define UART_BASE_SEQUENCE_SV

// Import UVM package and transaction type
import uvm_pkg::*;
`include "uvm_macros.svh"

class uart_base_sequence extends uvm_sequence #(uart_transaction);
    
    // UVM registration
    `uvm_object_utils(uart_base_sequence)
    
    // Constructor
    function new(string name = "uart_base_sequence");
        super.new(name);
    endfunction
    
    // Pre-body task for setup
    virtual task pre_body();
        if (get_starting_phase() != null) begin
            get_starting_phase().raise_objection(this);
        end
    endtask
    
    // Post-body task for cleanup
    virtual task post_body();
        if (get_starting_phase() != null) begin
            get_starting_phase().drop_objection(this);
        end
    endtask
    
    // Utility function to create and send basic UART transaction
    virtual task send_uart_transaction(
        input bit [31:0] address,
        input bit [31:0] data,
        input transaction_type_e trans_type = WRITE
    );
        uart_transaction req;
        
        req = uart_transaction::type_id::create("uart_req");
        if (!req.randomize() with {
            address == local::address;
            data == local::data;
            transaction_type == local::trans_type;
        }) begin
            `uvm_fatal(get_type_name(), "Failed to randomize uart_transaction")
        end
        
        start_item(req);
        finish_item(req);
    endtask
    
    // Utility function for basic register write
    virtual task write_register(
        input bit [31:0] reg_addr,
        input bit [31:0] reg_data
    );
        `uvm_info(get_type_name(), 
                  $sformatf("Writing 0x%08x to register 0x%08x", reg_data, reg_addr), 
                  UVM_HIGH)
        send_uart_transaction(reg_addr, reg_data, WRITE);
    endtask
    
    // Utility function for basic register read
    virtual task read_register(
        input bit [31:0] reg_addr
    );
        `uvm_info(get_type_name(), 
                  $sformatf("Reading from register 0x%08x", reg_addr), 
                  UVM_HIGH)
        send_uart_transaction(reg_addr, 32'h0, READ);
    endtask
    
    // Wait for specified duration with logging
    virtual task wait_cycles(input int num_cycles);
        `uvm_info(get_type_name(), 
                  $sformatf("Waiting for %0d cycles", num_cycles), 
                  UVM_HIGH)
        #(num_cycles * 10ns); // Assuming 100MHz clock
    endtask
    
endclass : uart_base_sequence

`endif // UART_BASE_SEQUENCE_SV