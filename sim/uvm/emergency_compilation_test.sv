`timescale 1ns / 1ps

//=============================================================================
// Emergency Compilation Test
// Tests if emergency files can be compiled and instantiated
//=============================================================================

import uvm_pkg::*;
`include "uvm_macros.svh"

import uart_axi4_test_pkg::*;

class emergency_compilation_test extends uvm_test;
    `uvm_component_utils(emergency_compilation_test)

    emergency_reliable_scoreboard scoreboard;
    uart_axi4_env env;
    uart_axi4_env_config cfg;

    function new(string name = "emergency_compilation_test", uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        `uvm_info("COMPILE_TEST", "Building emergency compilation test environment", UVM_LOW)
        
        // Create configuration
        cfg = uart_axi4_env_config::type_id::create("cfg");
        uvm_config_db#(uart_axi4_env_config)::set(this, "*", "config", cfg);
        
        // Create environment
        env = uart_axi4_env::type_id::create("env", this);
        
        // Create emergency scoreboard
        scoreboard = emergency_reliable_scoreboard::type_id::create("scoreboard", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        `uvm_info("COMPILE_TEST", "Connecting emergency components", UVM_LOW)
        
        // Connect emergency scoreboard to monitor
        if (env.axi_monitor != null && scoreboard != null) begin
            env.axi_monitor.analysis_port.connect(scoreboard.axi_analysis_imp);
        end
        if (env.uart_agt != null && scoreboard != null) begin
            env.uart_agt.monitor.analysis_port.connect(scoreboard.uart_analysis_imp);
        end
    endfunction

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        `uvm_info("COMPILE_TEST", "Starting emergency compilation test", UVM_LOW)
        
        // Test scoreboard instantiation
        if (scoreboard != null) begin
            `uvm_info("COMPILE_TEST", "✅ Emergency scoreboard instantiated successfully", UVM_LOW)
        end else begin
            `uvm_error("COMPILE_TEST", "❌ Emergency scoreboard instantiation failed")
        end
        
        // Test scoreboard methods
        scoreboard.print_reliability_statistics();
        
        `uvm_info("COMPILE_TEST", "✅ Emergency compilation test completed successfully", UVM_LOW)
        
        #100ns;
        phase.drop_objection(this);
    endtask

endclass