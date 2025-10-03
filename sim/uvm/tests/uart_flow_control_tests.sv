`timescale 1ns / 1ps

// Flow Control Test for RTS/CTS Hardware Flow Control
// Tests PMOD-compliant 4-wire UART implementation

class uart_flow_control_test extends uart_axi4_base_test;
    `uvm_component_utils(uart_flow_control_test)
    
    function new(string name = "uart_flow_control_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Set test-specific configuration
        uvm_config_db#(uvm_object_wrapper)::set(this, "env.uart_agent.uart_seqr.main_phase", 
                                                "default_sequence", uart_flow_control_stress_sequence::type_id::get());
    endfunction
    
    virtual task main_phase(uvm_phase phase);
        uart_rts_monitor_sequence rts_seq;
        uart_cts_flow_control_sequence cts_seq;
        
        phase.raise_objection(this);
        
        `uvm_info("FLOW_CONTROL_TEST", "Starting RTS/CTS flow control test", UVM_LOW);
        
        // Test 1: RTS Monitoring
        `uvm_info("FLOW_CONTROL_TEST", "=== Test 1: RTS Monitoring ===", UVM_LOW);
        rts_seq = uart_rts_monitor_sequence::type_id::create("rts_seq");
        rts_seq.start(env.uart_agt.sequencer);
        
        // Wait for FIFO to drain
        #50000ns;
        
        // Test 2: CTS Flow Control
        `uvm_info("FLOW_CONTROL_TEST", "=== Test 2: CTS Flow Control ===", UVM_LOW);
        cts_seq = uart_cts_flow_control_sequence::type_id::create("cts_seq");
        cts_seq.start(env.uart_agt.sequencer);
        
        // Final stabilization time
        #20000ns;
        
        `uvm_info("FLOW_CONTROL_TEST", "RTS/CTS flow control test completed", UVM_LOW);
        
        phase.drop_objection(this);
    endtask
    
    virtual function void final_phase(uvm_phase phase);
        super.final_phase(phase);
        
        // Print flow control test summary
        `uvm_info("FLOW_CONTROL_TEST", "=== Flow Control Test Summary ===", UVM_LOW);
        `uvm_info("FLOW_CONTROL_TEST", "1. RTS monitoring functionality tested", UVM_LOW);
        `uvm_info("FLOW_CONTROL_TEST", "2. CTS flow control behavior tested", UVM_LOW);
        `uvm_info("FLOW_CONTROL_TEST", "Check waveforms for RTS/CTS signal timing", UVM_LOW);
    endfunction
endclass

// Quick RTS test for basic functionality
class uart_rts_basic_test extends uart_axi4_base_test;
    `uvm_component_utils(uart_rts_basic_test)
    
    function new(string name = "uart_rts_basic_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual task main_phase(uvm_phase phase);
        uart_rts_monitor_sequence rts_seq;
        
        phase.raise_objection(this);
        
        `uvm_info("RTS_BASIC_TEST", "Starting basic RTS test", UVM_LOW);
        
        rts_seq = uart_rts_monitor_sequence::type_id::create("rts_seq");
        rts_seq.start(env.uart_agt.sequencer);
        
        // Allow time for monitoring
        #30000ns;
        
        `uvm_info("RTS_BASIC_TEST", "Basic RTS test completed", UVM_LOW);
        
        phase.drop_objection(this);
    endtask
endclass

// CTS stress test
class uart_cts_stress_test extends uart_axi4_base_test;
    `uvm_component_utils(uart_cts_stress_test)
    
    function new(string name = "uart_cts_stress_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual task main_phase(uvm_phase phase);
        uart_flow_control_stress_sequence stress_seq;
        
        phase.raise_objection(this);
        
        `uvm_info("CTS_STRESS_TEST", "Starting CTS stress test", UVM_LOW);
        
        stress_seq = uart_flow_control_stress_sequence::type_id::create("stress_seq");
        stress_seq.num_transactions = 50;  // Increased load
        stress_seq.start(env.uart_agt.sequencer);
        
        // Extended monitoring time
        #100000ns;
        
        `uvm_info("CTS_STRESS_TEST", "CTS stress test completed", UVM_LOW);
        
        phase.drop_objection(this);
    endtask
endclass