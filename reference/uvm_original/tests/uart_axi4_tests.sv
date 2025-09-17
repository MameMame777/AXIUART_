// UART-AXI4 Bridge Specific Test Classes
// Target Board: Zybo Z7-20
// Date: July 26, 2025
// Description: Specific test classes for different test scenarios

`ifndef UART_AXI4_TESTS_SV
`define UART_AXI4_TESTS_SV

// Basic functionality test
class uart_axi4_basic_test extends uart_axi4_base_test;
    
    `uvm_component_utils(uart_axi4_basic_test)
    
    function new(string name = "uart_axi4_basic_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void configure_env(uart_axi4_env_config cfg);
        cfg.configure_for_basic_test();
        cfg.timeout = 2ms;
        `uvm_info("BASIC_TEST", "Configured for basic functionality test", UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        basic_func_sequence seq;
        
        phase.raise_objection(this);
        
        `uvm_info("BASIC_TEST", "Starting basic functionality test", UVM_LOW)
        
        seq = basic_func_sequence::type_id::create("basic_seq");
        seq.start(env.axi_agent.sequencer);
        
        `uvm_info("BASIC_TEST", "Basic functionality test completed", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass

// Loopback test
class uart_axi4_loopback_test extends uart_axi4_base_test;
    
    `uvm_component_utils(uart_axi4_loopback_test)
    
    function new(string name = "uart_axi4_loopback_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void configure_env(uart_axi4_env_config cfg);
        cfg.configure_for_basic_test();
        cfg.timeout = 5ms;
        cfg.has_scoreboard = 1;
        `uvm_info("LOOPBACK_TEST", "Configured for loopback test", UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        uart_loopback_sequence seq;
        
        phase.raise_objection(this);
        
        `uvm_info("LOOPBACK_TEST", "Starting UART loopback test", UVM_LOW)
        
        seq = uart_loopback_sequence::type_id::create("loopback_seq");
        seq.start(env.axi_agent.sequencer);
        
        `uvm_info("LOOPBACK_TEST", "UART loopback test completed", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass

// Error injection test
class uart_axi4_error_test extends uart_axi4_base_test;
    
    `uvm_component_utils(uart_axi4_error_test)
    
    function new(string name = "uart_axi4_error_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void configure_env(uart_axi4_env_config cfg);
        cfg.configure_for_error_test();
        cfg.timeout = 10ms;
        cfg.max_errors = 100; // Allow more errors for error injection test
        `uvm_info("ERROR_TEST", "Configured for error injection test", UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        error_injection_sequence seq;
        
        phase.raise_objection(this);
        
        `uvm_info("ERROR_TEST", "Starting error injection test", UVM_LOW)
        
        seq = error_injection_sequence::type_id::create("error_seq");
        seq.start(env.axi_agent.sequencer);
        
        `uvm_info("ERROR_TEST", "Error injection test completed", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass

// Performance test
class uart_axi4_performance_test extends uart_axi4_base_test;
    
    `uvm_component_utils(uart_axi4_performance_test)
    
    function new(string name = "uart_axi4_performance_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void configure_env(uart_axi4_env_config cfg);
        cfg.configure_for_performance_test();
        cfg.timeout = 100ms; // Longer timeout for performance test
        cfg.enable_debug_prints = 0; // Reduce verbosity for performance
        `uvm_info("PERF_TEST", "Configured for performance test", UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        performance_test_sequence seq;
        
        phase.raise_objection(this);
        
        `uvm_info("PERF_TEST", "Starting performance test", UVM_LOW)
        
        seq = performance_test_sequence::type_id::create("perf_seq");
        seq.start(env.axi_agent.sequencer);
        
        `uvm_info("PERF_TEST", "Performance test completed", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass

// UART physical layer test
class uart_axi4_physical_test extends uart_axi4_base_test;
    
    `uvm_component_utils(uart_axi4_physical_test)
    
    function new(string name = "uart_axi4_physical_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void configure_env(uart_axi4_env_config cfg);
        cfg.configure_for_basic_test();
        cfg.timeout = 20ms;
        cfg.uart_flow_control_enable = 1;
        `uvm_info("PHY_TEST", "Configured for physical layer test", UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        uart_physical_sequence seq;
        
        phase.raise_objection(this);
        
        `uvm_info("PHY_TEST", "Starting UART physical layer test", UVM_LOW)
        
        seq = uart_physical_sequence::type_id::create("phy_seq");
        seq.start(env.uart_agent_inst.sequencer);
        
        `uvm_info("PHY_TEST", "UART physical layer test completed", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass

// Comprehensive test combining multiple scenarios
class uart_axi4_comprehensive_test extends uart_axi4_base_test;
    
    `uvm_component_utils(uart_axi4_comprehensive_test)
    
    function new(string name = "uart_axi4_comprehensive_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void configure_env(uart_axi4_env_config cfg);
        cfg.configure_for_basic_test();
        cfg.has_scoreboard = 1;
        cfg.has_coverage = 1;
        cfg.timeout = 50ms;
        cfg.max_errors = 20;
        `uvm_info("COMP_TEST", "Configured for comprehensive test", UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        basic_func_sequence basic_seq;
        uart_loopback_sequence loopback_seq;
        error_injection_sequence error_seq;
        uart_physical_sequence phy_seq;
        
        phase.raise_objection(this);
        
        `uvm_info("COMP_TEST", "Starting comprehensive test", UVM_LOW)
        
        // Run tests sequentially
        `uvm_info("COMP_TEST", "Phase 1: Basic functionality", UVM_LOW)
        basic_seq = basic_func_sequence::type_id::create("basic_seq");
        basic_seq.start(env.axi_agent.sequencer);
        
        #1us; // Gap between tests
        
        `uvm_info("COMP_TEST", "Phase 2: Loopback test", UVM_LOW)
        loopback_seq = uart_loopback_sequence::type_id::create("loopback_seq");
        loopback_seq.start(env.axi_agent.sequencer);
        
        #1us;
        
        `uvm_info("COMP_TEST", "Phase 3: Error injection", UVM_LOW)
        error_seq = error_injection_sequence::type_id::create("error_seq");
        error_seq.start(env.axi_agent.sequencer);
        
        #1us;
        
        `uvm_info("COMP_TEST", "Phase 4: Physical layer test", UVM_LOW)
        phy_seq = uart_physical_sequence::type_id::create("phy_seq");
        phy_seq.start(env.uart_agent_inst.sequencer);
        
        `uvm_info("COMP_TEST", "Comprehensive test completed", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass

// Coordinated test with parallel AXI and UART operations
class uart_axi4_coordinated_test extends uart_axi4_base_test;
    
    `uvm_component_utils(uart_axi4_coordinated_test)
    
    function new(string name = "uart_axi4_coordinated_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void configure_env(uart_axi4_env_config cfg);
        cfg.configure_for_basic_test();
        cfg.has_scoreboard = 1;
        cfg.timeout = 30ms;
        `uvm_info("COORD_TEST", "Configured for coordinated test", UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        uart_axi_coordination_sequence coord_seq;
        
        phase.raise_objection(this);
        
        `uvm_info("COORD_TEST", "Starting coordinated AXI-UART test", UVM_LOW)
        
        coord_seq = uart_axi_coordination_sequence::type_id::create("coord_seq");
        coord_seq.start(env.axi_agent.sequencer);
        
        `uvm_info("COORD_TEST", "Coordinated test completed", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass

`endif // UART_AXI4_TESTS_SV
