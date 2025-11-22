`timescale 1ns / 1ps

//==============================================================================
// UVM-compliant reset sequence
// Standard pattern: calls virtual interface reset_dut() task
// Reference: IEEE 1800.2-2020 Section 4.7 - Reset Handling
//==============================================================================

class uart_reset_seq extends uvm_sequence #(uvm_sequence_item);
    `uvm_object_utils(uart_reset_seq)
    
    // Virtual interface handle (set by test or env)
    virtual uart_if vif;
    
    function new(string name = "uart_reset_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        // Validate interface handle
        if (vif == null) begin
            `uvm_fatal("UART_RESET_SEQ", "Virtual interface not set - cannot execute reset")
        end
        
        `uvm_info("UART_RESET_SEQ", "========================================", UVM_LOW)
        `uvm_info("UART_RESET_SEQ", "  DUT RESET SEQUENCE STARTED", UVM_LOW)
        `uvm_info("UART_RESET_SEQ", "========================================", UVM_LOW)
        
        // Execute reset via interface task
        // This is the ONLY correct way to reset DUT in UVM
        vif.reset_dut();
        
        `uvm_info("UART_RESET_SEQ", "DUT reset sequence completed successfully", UVM_LOW)
        `uvm_info("UART_RESET_SEQ", "========================================", UVM_LOW)
    endtask
    
endclass : uart_reset_seq
