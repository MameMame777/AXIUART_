// Test Register Test Class
// Tests for newly added test registers (0x00001020-0x0000102C)
// Created: 2025-10-05

import test_register_sequences_pkg::*;

class uart_axi4_test_register_test extends uart_axi4_base_test;
    `uvm_component_utils(uart_axi4_test_register_test)
    
    function new(string name = "uart_axi4_test_register_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Set test-specific configuration
        uvm_config_db#(uvm_bitstream_t)::set(this, "*", "recording_detail", UVM_FULL);
        
        `uvm_info(get_type_name(), "Test Register Test Build Phase", UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        test_register_comprehensive_sequence test_seq;
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Starting Test Register Test", UVM_LOW)
        
        // Create and configure the test sequence
        test_seq = test_register_comprehensive_sequence::type_id::create("test_seq");
        
        // Start the sequence on the sequencer
        test_seq.start(env.uart_agt.sequencer);
        
        `uvm_info(get_type_name(), "Test Register Test Completed", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass