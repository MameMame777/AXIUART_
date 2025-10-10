`timescale 1ns / 1ps

class simple_register_test extends uart_axi4_base_test;
    
    `uvm_component_utils(simple_register_test)
    
    function new(string name = "simple_register_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Configure test for register verification
        cfg.num_transactions = 10;
        cfg.enable_protocol_checking = 1'b1;
        cfg.enable_axi_monitor = 1'b1;
        cfg.enable_coverage = 1'b1;
        cfg.enable_scoreboard = 1'b1;
        
        `uvm_info("SIMPLE_REG_TEST", "Simple register test configuration completed", UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        simple_test_register_sequence simple_seq;
        
        phase.raise_objection(this);
        
        `uvm_info("SIMPLE_REG_TEST", "=== SIMPLE REGISTER TEST ===", UVM_LOW)
        `uvm_info("SIMPLE_REG_TEST", "Testing specific register read/write operations", UVM_LOW)
        
        // Wait for reset and initialization
        super.run_phase(phase);
        
        `uvm_info("SIMPLE_REG_TEST", "Starting simple register verification sequence", UVM_LOW)
        
        // Execute simple register test sequence
        `uvm_create(simple_seq)
        simple_seq.start(env.uart_agt.sequencer);
        
        // Allow some time for responses to complete
        #50000;
        
        `uvm_info("SIMPLE_REG_TEST", "=== SIMPLE REGISTER TEST COMPLETED ===", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass