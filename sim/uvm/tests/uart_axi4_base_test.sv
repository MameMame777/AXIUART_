`timescale 1ns / 1ps


import uvm_pkg::*;
import uart_axi4_test_pkg::*;  // Import our test package

// Base Test Class for AXIUART_Top System UVM Testbench
class uart_axi4_base_test extends uvm_test;
    
    `uvm_component_utils(uart_axi4_base_test)
    
    // Test environment
    uart_axi4_env env;
    uart_axi4_env_config cfg;

    // Scenario-driven debug configuration
    string test_scenario = "default";
    bit scenario_enable_wave_dump = 1'b1;
    
    // Virtual interfaces
    virtual uart_if uart_vif;
    virtual bridge_status_if bridge_status_vif;
    virtual axi4_lite_if axi_vif;
    
    function new(string name = "uart_axi4_base_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Create configuration object
        cfg = uart_axi4_env_config::type_id::create("cfg", this);
        configure_test();
        
        // Get virtual interfaces from testbench top
        if (!uvm_config_db#(virtual uart_if)::get(this, "", "uart_vif", uart_vif)) begin
            `uvm_fatal("BASE_TEST", "Failed to get UART virtual interface")
        end
        
        if (!uvm_config_db#(virtual bridge_status_if)::get(this, "", "bridge_status_vif", bridge_status_vif)) begin
            `uvm_fatal("BASE_TEST", "Failed to get bridge status virtual interface")
        end
        
        if (!uvm_config_db#(virtual axi4_lite_if)::get(this, "", "axi_vif", axi_vif)) begin
            if (cfg.enable_axi_monitor) begin
                `uvm_fatal("BASE_TEST", "AXI monitor enabled but AXI virtual interface not provided")
            end else begin
                `uvm_warning("BASE_TEST", "AXI virtual interface not provided; AXI monitoring disabled")
            end
        end else begin
            `uvm_info("BASE_TEST", "=== AXI VIRTUAL INTERFACE SUCCESSFULLY RETRIEVED ===", UVM_HIGH)
            `uvm_info("BASE_TEST", $sformatf("AXI VIF null check: %s", (axi_vif == null) ? "NULL" : "NOT NULL"), UVM_HIGH)
        end
        
        // Set interfaces in configuration
        cfg.uart_vif = uart_vif;
        cfg.bridge_status_vif = bridge_status_vif;
        cfg.axi_vif = axi_vif;
        
        // Set configuration in database
        uvm_config_db#(uart_axi4_env_config)::set(this, "*", "cfg", cfg);
        uvm_config_db#(virtual uart_if)::set(this, "*", "vif", uart_vif);
        uvm_config_db#(virtual bridge_status_if)::set(this, "*", "bridge_status_vif", bridge_status_vif);
        if (axi_vif != null) begin
            uvm_config_db#(virtual axi4_lite_if)::set(this, "*", "axi_vif", axi_vif);
        end
        
        // Create environment - re-enabled
        env = uart_axi4_env::type_id::create("env", this);
        
        // Fetch scenario controls propagated by the testbench top
        if (!uvm_config_db#(string)::get(this, "", "test_scenario", test_scenario)) begin
            test_scenario = "default";
        end
        if (!uvm_config_db#(bit)::get(this, "", "scenario_enable_wave_dump", scenario_enable_wave_dump)) begin
            scenario_enable_wave_dump = 1'b1;
        end

        `uvm_info("BASE_TEST", $sformatf("Test scenario selected: '%s' (wave dump %s)",
            test_scenario,
            scenario_enable_wave_dump ? "enabled" : "disabled"), UVM_MEDIUM)

        `uvm_info("BASE_TEST", "Base test build phase completed", UVM_LOW)
    endfunction
    
    virtual function void configure_test();
        // Default configuration
        cfg.uart_agent_is_active = UVM_ACTIVE;
        cfg.axi_agent_is_active = UVM_PASSIVE;
        
        // UART configuration
    cfg.clk_freq_hz = 125_000_000;  // 125MHz system clock
        cfg.baud_rate = uart_axi4_test_pkg::BAUD_RATE;  // Align with DUT baud rate from shared package

    // Recompute dependent timing values after updating the baud rate
    cfg.calculate_timing();
    cfg.frame_timeout_ns = cfg.byte_time_ns * 32;            // Guard for multi-byte frames
        
        // Timing configuration  
        cfg.min_idle_cycles = 5;
        cfg.max_idle_cycles = 20;
        
        // Test control
        cfg.enable_coverage = 1;
        cfg.enable_scoreboard = 1;
        cfg.enable_protocol_checking = 1;
        cfg.enable_driver_runtime_logs = 1'b1;  // TEMPORARY: Enable for debugging timeout issue
        cfg.enable_scoreboard_runtime_logs = 1'b0;
        cfg.driver_runtime_verbosity = UVM_LOW;
        cfg.scoreboard_runtime_verbosity = UVM_LOW;
        
        // System monitoring (AXIUART_Top specific)
        cfg.enable_system_status_monitoring = 1;
        cfg.enable_axi_monitor = 1;
        cfg.bridge_status_verbosity = UVM_MEDIUM;
        
        `uvm_info("BASE_TEST", "Test configuration completed", UVM_MEDIUM)
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        `uvm_info("BASE_TEST", "Base test connect phase completed", UVM_MEDIUM)
    endfunction
    
    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        
        // Print test topology
        `uvm_info("BASE_TEST", "=== Test Topology ===", UVM_LOW)
        uvm_top.print_topology();
        
        // Print configuration
        `uvm_info("BASE_TEST", "=== Test Configuration ===", UVM_LOW)
        cfg.print();
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        // Base run phase - can be overridden by derived tests
        // If derived test overrides this, the base implementation won't run
        
        `uvm_info("BASE_TEST", "Base test run phase started", UVM_LOW)
        
        // Only raise objection if not already raised by derived class
        if (phase.get_objection().get_objection_count(this) == 0) begin
            phase.raise_objection(this, "Base test run phase");
            
            // Wait for reset to complete
            wait (uart_axi4_tb_top.rst_n == 1'b1);
            repeat (10) @(posedge uart_axi4_tb_top.clk);
            
            `uvm_info("BASE_TEST", "Reset completed, test ready", UVM_MEDIUM)

            if (scenario_enable_wave_dump) begin
                if (test_scenario == "scenario1") begin
                    `uvm_info("BASE_TEST", "Scenario1 debug hooks active", UVM_HIGH)
                end else if (test_scenario == "scenario2") begin
                    `uvm_info("BASE_TEST", "Scenario2 debug hooks active", UVM_HIGH)
                end
            end else begin
                `uvm_info("BASE_TEST", "Waveform dump disabled for this scenario", UVM_MEDIUM)
            end
            
            // Basic test completion
            repeat (100) @(posedge uart_axi4_tb_top.clk);
            
            phase.drop_objection(this, "Base test run phase completed");
        end else begin
            `uvm_info("BASE_TEST", "Objection already raised by derived test - skipping base run", UVM_MEDIUM)
        end
    endtask
    
    virtual function void extract_phase(uvm_phase phase);
        super.extract_phase(phase);
        
        `uvm_info("BASE_TEST", "Extracting test results", UVM_MEDIUM)
        
        // Extract coverage information if available
        // Temporarily commented out due to env being disabled
        // if (env.coverage != null) begin
        //     `uvm_info("BASE_TEST", $sformatf("Functional Coverage: %.2f%%", 
        //               env.coverage.get_coverage()), UVM_LOW)
        // end
    endfunction
    
    virtual function void check_phase(uvm_phase phase);
        super.check_phase(phase);
        
        // Check for any remaining objections - safely
        if (phase != null && phase.get_objection() != null) begin
            if (phase.get_objection().get_objection_count(this) > 0) begin
                `uvm_warning("BASE_TEST", "Test completed with active objections")
            end
        end
        
        `uvm_info("BASE_TEST", "Test check phase completed", UVM_MEDIUM)
    endfunction
    
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        
        // Report test statistics
        `uvm_info("BASE_TEST", "=== TEST REPORT ===", UVM_LOW)
        
        // Temporarily commented out due to env being disabled
        // if (env.scoreboard != null) begin
        //     env.scoreboard.report();
        // end
        
        // Check for UVM errors
        if (uvm_report_server::get_server().get_severity_count(UVM_ERROR) > 0) begin
            `uvm_info("BASE_TEST", "*** TEST FAILED - UVM ERRORS DETECTED ***", UVM_LOW)
        end else if (uvm_report_server::get_server().get_severity_count(UVM_FATAL) > 0) begin
            `uvm_info("BASE_TEST", "*** TEST FAILED - UVM FATAL ERRORS DETECTED ***", UVM_LOW)
        end else begin
            `uvm_info("BASE_TEST", "*** NO UVM ERRORS DETECTED ***", UVM_LOW)
        end
    endfunction
    
    virtual function void final_phase(uvm_phase phase);
        super.final_phase(phase);
        
        `uvm_info("BASE_TEST", "Base test final phase", UVM_MEDIUM)
        
        // Final cleanup and summary
        `uvm_info("BASE_TEST", "=== TEST COMPLETED ===", UVM_LOW)
    endfunction
    
endclass