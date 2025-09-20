`timescale 1ns / 1ps

// UART Protocol Active Communication Test
class uart_axi4_active_test extends uart_axi4_base_test;
    `uvm_component_utils(uart_axi4_active_test)
    
    function new(string name = "uart_axi4_active_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info(get_type_name(), "UART Active Communication Test build phase", UVM_MEDIUM)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        uart_protocol_active_sequence active_seq;
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "=== UART Active Communication Test Started ===", UVM_MEDIUM)
        
        // Wait for system initialization
        #1000ns; // System stabilization time
        
        // Create and start active UART communication sequence
        active_seq = uart_protocol_active_sequence::type_id::create("active_seq");
        active_seq.start(env.uart_agt.sequencer);
        
        // Wait for completion
        #10000ns;
        
        `uvm_info(get_type_name(), "=== UART Active Communication Test Completed ===", UVM_MEDIUM)
        
        phase.drop_objection(this);
    endtask
    
endclass