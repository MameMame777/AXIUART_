// UART-AXI4 Bridge Base Test
// Target Board: Zybo Z7-20
// Date: July 26, 2025
// Description: Base UVM test class for UART-AXI4 bridge

`ifndef UART_AXI4_BASE_TEST_SV
`define UART_AXI4_BASE_TEST_SV

class uart_axi4_base_test extends uvm_test;
    
    // Environment instance
    uart_axi4_env env;
    
    // Environment configuration
    uart_axi4_env_config env_cfg;
    
    // Virtual interfaces
    virtual axi4_lite_if axi_vif;
    virtual uart_if uart_vif;
    
    // UVM registration
    `uvm_component_utils(uart_axi4_base_test)
    
    // Constructor
    function new(string name = "uart_axi4_base_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get virtual interfaces
        if (!uvm_config_db#(virtual axi4_lite_if)::get(this, "", "vif", axi_vif)) begin
            `uvm_fatal("BASE_TEST", "AXI4-Lite virtual interface not found")
        end
        
        if (!uvm_config_db#(virtual uart_if)::get(this, "", "vif", uart_vif)) begin
            `uvm_fatal("BASE_TEST", "UART virtual interface not found")
        end
        
        // Create environment configuration
        env_cfg = uart_axi4_env_config::type_id::create("env_cfg");
        configure_env(env_cfg);
        
        // Validate configuration
        if (!env_cfg.is_valid()) begin
            `uvm_fatal("BASE_TEST", "Environment configuration is invalid")
        end
        
        // Set configuration in database
        uvm_config_db#(uart_axi4_env_config)::set(this, "*", "env_cfg", env_cfg);
        
        // Set virtual interfaces for agents
        uvm_config_db#(virtual axi4_lite_if)::set(this, "env.axi_agent*", "vif", axi_vif);
        uvm_config_db#(virtual uart_if)::set(this, "env.uart_agent_inst*", "vif", uart_vif);
        
        // Create environment
        env = uart_axi4_env::type_id::create("env", this);
        
        // Set test timeout
        uvm_config_db#(time)::set(this, "*", "timeout", env_cfg.timeout);
        
        `uvm_info("BASE_TEST", "Base test build phase completed", UVM_MEDIUM)
    endfunction
    
    // Virtual function to configure environment (override in derived tests)
    virtual function void configure_env(uart_axi4_env_config cfg);
        // Default configuration - can be overridden
        cfg.configure_for_basic_test();
        `uvm_info("BASE_TEST", "Using default environment configuration", UVM_MEDIUM)
    endfunction
    
    // End of elaboration phase
    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        
        // Print test information
        `uvm_info("BASE_TEST", "=== Test Configuration ===", UVM_LOW)
        `uvm_info("BASE_TEST", $sformatf("Test: %s", get_name()), UVM_LOW)
        `uvm_info("BASE_TEST", $sformatf("Timeout: %0t", env_cfg.timeout), UVM_LOW)
        `uvm_info("BASE_TEST", $sformatf("Max errors: %0d", env_cfg.max_errors), UVM_LOW)
        `uvm_info("BASE_TEST", $sformatf("Has scoreboard: %b", env_cfg.has_scoreboard), UVM_LOW)
        `uvm_info("BASE_TEST", $sformatf("Has coverage: %b", env_cfg.has_coverage), UVM_LOW)
        `uvm_info("BASE_TEST", "=========================", UVM_LOW)
        
        // Print topology if enabled
        if (env_cfg.print_topology) begin
            `uvm_info("BASE_TEST", "Test topology:", UVM_LOW)
            this.print();
        end
    endfunction
    
    // Start of simulation phase
    virtual function void start_of_simulation_phase(uvm_phase phase);
        super.start_of_simulation_phase(phase);
        
        // Enable MXD waveform dump
        `ifdef DSIM
            $dumpfile("uart_axi4_test.mxd");
            $dumpvars(0, this);
            `uvm_info("BASE_TEST", "MXD waveform dump enabled for test", UVM_LOW)
        `endif
        
        `uvm_info("BASE_TEST", "Test simulation started", UVM_LOW)
    endfunction
    
    // Run phase - override in derived tests
    virtual task run_phase(uvm_phase phase);
        `uvm_info("BASE_TEST", "Base test run phase - no sequences executed", UVM_LOW)
        
        // Base test doesn't run any sequences
        // Derived tests should override this method
        phase.raise_objection(this);
        #100ns; // Minimal runtime
        phase.drop_objection(this);
    endtask
    
    // Check phase
    virtual function void check_phase(uvm_phase phase);
        super.check_phase(phase);
        
        // Check for test completion status
        if (env.scoreboard != null) begin
            if (env.scoreboard.mismatches > 0) begin
                `uvm_error("BASE_TEST", $sformatf("Test failed with %0d mismatches", env.scoreboard.mismatches))
            end
        end
    endfunction
    
    // Report phase
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        
        `uvm_info("BASE_TEST", "=== Test Summary ===", UVM_LOW)
        `uvm_info("BASE_TEST", $sformatf("Test: %s", get_name()), UVM_LOW)
        
        // Report environment status
        if (env != null) begin
            env.report_phase(phase);
        end
        
        `uvm_info("BASE_TEST", "==================", UVM_LOW)
    endfunction
    
    // Final phase
    virtual function void final_phase(uvm_phase phase);
        super.final_phase(phase);
        
        `uvm_info("BASE_TEST", $sformatf("Test %s completed", get_name()), UVM_LOW)
    endfunction

endclass

`endif // UART_AXI4_BASE_TEST_SV
