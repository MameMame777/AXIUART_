`timescale 1ns / 1ps

// Phase 3: Scoreboard Integration Test
// Created: October 11, 2025
// Purpose: Test the integrated Scoreboard and Correlation Engine

class uart_axi4_scoreboard_test extends enhanced_uart_axi4_base_test;
    `uvm_component_utils(uart_axi4_scoreboard_test)

    function new(string name = "uart_axi4_scoreboard_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Enable scoreboard correlation and reporting
        uvm_config_db#(int)::set(this, "*", "enable_scoreboard", 1);
        uvm_config_db#(int)::set(this, "*", "enable_correlation", 1);
        
        `uvm_info("SCOREBOARD_TEST", "Scoreboard integration test configured", UVM_MEDIUM)
    endfunction

    task run_phase(uvm_phase phase);
        uart_axi4_basic_sequence seq;
        
        phase.raise_objection(this);
        
        `uvm_info("SCOREBOARD_TEST", "Starting Scoreboard integration test", UVM_LOW)
        
        // Create and run a basic sequence to generate transactions
        seq = uart_axi4_basic_sequence::type_id::create("seq");
        
        seq.start(env.uart_agt.sequencer);
        
        // Allow some time for correlation processing
        #1000ns;
        
        `uvm_info("SCOREBOARD_TEST", "Scoreboard integration test completed", UVM_LOW)
        
        phase.drop_objection(this);
    endtask

    function void final_phase(uvm_phase phase);
        super.final_phase(phase);
        
        // Report scoreboard statistics
        `uvm_info("SCOREBOARD_TEST", "=== Scoreboard Integration Test Results ===", UVM_LOW)
        
        // The environment's scoreboard should report correlation results
        if (env.phase3_scoreboard != null) begin
            `uvm_info("SCOREBOARD_TEST", "Phase 3 Scoreboard instance found and active", UVM_LOW)
        end else begin
            `uvm_info("SCOREBOARD_TEST", "Phase 3 Scoreboard instance not found (correlation may be disabled)", UVM_MEDIUM)
        end
    endfunction

endclass