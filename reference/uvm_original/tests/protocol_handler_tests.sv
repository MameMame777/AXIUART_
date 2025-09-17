`timescale 1ns / 1ps

// Protocol Handler Specific Test Classes
// Purpose: Protocol handler verification tests in unified UVM environment
// Date: August 11, 2025

`ifndef PROTOCOL_HANDLER_TESTS_SV
`define PROTOCOL_HANDLER_TESTS_SV

// Protocol Handler Basic Test
class protocol_handler_basic_test extends uart_axi4_base_test;
    
    `uvm_component_utils(protocol_handler_basic_test)
    
    function new(string name = "protocol_handler_basic_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void configure_env(uart_axi4_env_config cfg);
        super.configure_env(cfg);
        cfg.timeout = 5ms;
        cfg.enable_protocol_coverage = 1;
        `uvm_info("PROTOCOL_TEST", "Configured for protocol handler basic test", UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        protocol_handler_basic_sequence seq;
        
        phase.raise_objection(this);
        
        `uvm_info("PROTOCOL_TEST", "Starting protocol handler basic test", UVM_LOW)
        
        seq = protocol_handler_basic_sequence::type_id::create("seq");
        seq.start(env.uart_agent.sequencer);
        
        `uvm_info("PROTOCOL_TEST", "Protocol handler basic test completed", UVM_LOW)
        phase.drop_objection(this);
    endtask

endclass : protocol_handler_basic_test

// Protocol Handler Command Test
class protocol_handler_command_test extends uart_axi4_base_test;
    
    `uvm_component_utils(protocol_handler_command_test)
    
    function new(string name = "protocol_handler_command_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void configure_env(uart_axi4_env_config cfg);
        super.configure_env(cfg);
        cfg.timeout = 10ms;
        cfg.enable_command_coverage = 1;
        `uvm_info("PROTOCOL_TEST", "Configured for protocol command test", UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        protocol_handler_command_sequence seq;
        
        phase.raise_objection(this);
        
        `uvm_info("PROTOCOL_TEST", "Starting protocol handler command test", UVM_LOW)
        
        seq = protocol_handler_command_sequence::type_id::create("seq");
        seq.start(env.uart_agent.sequencer);
        
        `uvm_info("PROTOCOL_TEST", "Protocol handler command test completed", UVM_LOW)
        phase.drop_objection(this);
    endtask

endclass : protocol_handler_command_test

// Protocol Handler Error Test
class protocol_handler_error_test extends uart_axi4_base_test;
    
    `uvm_component_utils(protocol_handler_error_test)
    
    function new(string name = "protocol_handler_error_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void configure_env(uart_axi4_env_config cfg);
        super.configure_env(cfg);
        cfg.timeout = 5ms;
        cfg.enable_error_injection = 1;
        `uvm_info("PROTOCOL_TEST", "Configured for protocol error test", UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        protocol_handler_error_sequence seq;
        
        phase.raise_objection(this);
        
        `uvm_info("PROTOCOL_TEST", "Starting protocol handler error test", UVM_LOW)
        
        seq = protocol_handler_error_sequence::type_id::create("seq");
        seq.start(env.uart_agent.sequencer);
        
        `uvm_info("PROTOCOL_TEST", "Protocol handler error test completed", UVM_LOW)
        phase.drop_objection(this);
    endtask

endclass : protocol_handler_error_test

`endif // PROTOCOL_HANDLER_TESTS_SV
