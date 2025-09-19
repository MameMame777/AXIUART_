`timescale 1ns / 1ps

// Minimal UART Agent for temporary compilation fix
class uart_agent extends uvm_agent;
    `uvm_component_utils(uart_agent)
    
    // Component handles
    uvm_sequencer#(uart_frame_transaction) sequencer;
    
    function new(string name = "uart_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Create sequencer
        sequencer = uvm_sequencer#(uart_frame_transaction)::type_id::create("sequencer", this);
        
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        // Connection phase implementation
    endfunction
    
endclass