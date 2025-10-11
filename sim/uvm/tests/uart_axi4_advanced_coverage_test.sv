`timescale 1ns / 1ps

// Advanced Coverage Test for UART-AXI4 Bridge
// Comprehensive test designed to maximize toggle, functional, and expression coverage
// Utilizes standardized uart_frame_transaction class with error injection and data randomization

import uvm_pkg::*;
import uart_axi4_test_pkg::*;
`include "uvm_macros.svh"

class uart_axi4_advanced_coverage_test extends enhanced_uart_axi4_base_test;
    `uvm_component_utils(uart_axi4_advanced_coverage_test)
    
    // Coverage sequences
    coverage_corner_cases_sequence corner_seq;
    coverage_error_injection_sequence error_inject_seq;
    coverage_boundary_values_sequence boundary_seq;
    coverage_state_transitions_sequence state_seq;
    coverage_fifo_stress_sequence fifo_seq;
    coverage_timing_variations_sequence timing_seq;
    uart_tx_coverage_sequence uart_tx_seq;
    uart_config_change_sequence config_change_seq;
    
    function new(string name = "uart_axi4_advanced_coverage_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void configure_test();
        super.configure_test();
        
        // Configuration for maximum coverage
        cfg.enable_coverage = 1;
        cfg.enable_scoreboard = 1;
        cfg.enable_protocol_checking = 1;
        
        `uvm_info("ADV_COV_TEST", "Advanced coverage test configuration applied", UVM_MEDIUM)
    endfunction
    
    virtual task main_phase(uvm_phase phase);
        phase.raise_objection(this, "Advanced coverage test main phase");
        
        `uvm_info("ADV_COV_TEST", "===========================================", UVM_LOW)
        `uvm_info("ADV_COV_TEST", "Starting Advanced Coverage Test Suite", UVM_LOW)
        `uvm_info("ADV_COV_TEST", "===========================================", UVM_LOW)
        
        // Wait for reset to complete
        wait (uart_axi4_tb_top.dut.rst == 1'b0);
        repeat (10) @(posedge uart_axi4_tb_top.dut.clk);
        
        // Phase 1: Corner Cases Coverage
        run_corner_cases_phase(phase);
        
        // Phase 2: Error Injection Coverage  
        run_error_injection_phase(phase);
        
        // Phase 3: Boundary Values Coverage
        run_boundary_values_phase(phase);
        
        // Phase 4: State Transition Coverage
        run_state_transitions_phase(phase);
        
        // Phase 5: FIFO Stress Coverage
        run_fifo_stress_phase(phase);
        
        // Phase 6: Timing Variations Coverage
        run_timing_variations_phase(phase);
        
        // Phase 7: UART TX Coverage (NEW)
        run_uart_tx_coverage_phase(phase);
        
        // Phase 8: Config Change Coverage (NEW)
        run_config_change_coverage_phase(phase);
        
        // Final coverage report
        report_coverage_statistics();
        
        // Wait for system stabilization
        repeat (1000) @(posedge uart_axi4_tb_top.dut.clk);
        
        phase.drop_objection(this, "Advanced coverage test completed");
    endtask
    
    // Phase 1: Corner Cases Coverage
    task run_corner_cases_phase(uvm_phase phase);
        `uvm_info("ADV_COV_TEST", "Phase 1: Corner Cases Coverage Testing", UVM_LOW)
        
        corner_seq = coverage_corner_cases_sequence::type_id::create("corner_seq");
        
        fork
            corner_seq.start(env.uart_agt.sequencer);
        join
        
        repeat (500) @(posedge uart_axi4_tb_top.dut.clk); // Phase separation
        `uvm_info("ADV_COV_TEST", "Phase 1 completed", UVM_MEDIUM)
    endtask
    
    // Phase 2: Error Injection Coverage
    task run_error_injection_phase(uvm_phase phase);
        `uvm_info("ADV_COV_TEST", "Phase 2: Error Injection Coverage Testing", UVM_LOW)
        
        error_inject_seq = coverage_error_injection_sequence::type_id::create("error_inject_seq");
        
        fork
            error_inject_seq.start(env.uart_agt.sequencer);
        join
        
        repeat (500) @(posedge uart_axi4_tb_top.dut.clk);
        `uvm_info("ADV_COV_TEST", "Phase 2 completed", UVM_MEDIUM)
    endtask
    
    // Phase 3: Boundary Values Coverage
    task run_boundary_values_phase(uvm_phase phase);
        `uvm_info("ADV_COV_TEST", "Phase 3: Boundary Values Coverage Testing", UVM_LOW)
        
        boundary_seq = coverage_boundary_values_sequence::type_id::create("boundary_seq");
        
        fork
            boundary_seq.start(env.uart_agt.sequencer);
        join
        
        repeat (500) @(posedge uart_axi4_tb_top.dut.clk);
        `uvm_info("ADV_COV_TEST", "Phase 3 completed", UVM_MEDIUM)
    endtask
    
    // Phase 4: State Transition Coverage
    task run_state_transitions_phase(uvm_phase phase);
        `uvm_info("ADV_COV_TEST", "Phase 4: State Transition Coverage Testing", UVM_LOW)
        
        state_seq = coverage_state_transitions_sequence::type_id::create("state_seq");
        
        fork
            state_seq.start(env.uart_agt.sequencer);
        join
        
        repeat (500) @(posedge uart_axi4_tb_top.dut.clk);
        `uvm_info("ADV_COV_TEST", "Phase 4 completed", UVM_MEDIUM)
    endtask
    
    // Phase 5: FIFO Stress Coverage
    task run_fifo_stress_phase(uvm_phase phase);
        `uvm_info("ADV_COV_TEST", "Phase 5: FIFO Stress Coverage Testing", UVM_LOW)
        
        fifo_seq = coverage_fifo_stress_sequence::type_id::create("fifo_seq");
        
        fork
            fifo_seq.start(env.uart_agt.sequencer);
        join
        
        repeat (500) @(posedge uart_axi4_tb_top.dut.clk);
        `uvm_info("ADV_COV_TEST", "Phase 5 completed", UVM_MEDIUM)
    endtask
    
    // Phase 6: Timing Variations Coverage
    task run_timing_variations_phase(uvm_phase phase);
        `uvm_info("ADV_COV_TEST", "Phase 6: Timing Variations Coverage Testing", UVM_LOW)
        
        timing_seq = coverage_timing_variations_sequence::type_id::create("timing_seq");
        
        fork
            timing_seq.start(env.uart_agt.sequencer);
        join
        
        repeat (500) @(posedge uart_axi4_tb_top.dut.clk);
        `uvm_info("ADV_COV_TEST", "Phase 6 completed", UVM_MEDIUM)
    endtask
    
    // Phase 7: UART TX Coverage (NEW)
    task run_uart_tx_coverage_phase(uvm_phase phase);
        `uvm_info("ADV_COV_TEST", "Phase 7: UART TX Coverage Testing", UVM_LOW)
        
        uart_tx_seq = uart_tx_coverage_sequence::type_id::create("uart_tx_seq");
        
        fork
            uart_tx_seq.start(env.uart_agt.sequencer);
        join
        
        repeat (500) @(posedge uart_axi4_tb_top.dut.clk);
        `uvm_info("ADV_COV_TEST", "Phase 7 completed", UVM_MEDIUM)
    endtask
    
    // Phase 8: Config Change Coverage (NEW)
    task run_config_change_coverage_phase(uvm_phase phase);
        `uvm_info("ADV_COV_TEST", "Phase 8: Config Change Coverage Testing", UVM_LOW)
        
        config_change_seq = uart_config_change_sequence::type_id::create("config_change_seq");
        
        fork
            config_change_seq.start(env.uart_agt.sequencer);
        join
        
        repeat (500) @(posedge uart_axi4_tb_top.dut.clk);
        `uvm_info("ADV_COV_TEST", "Phase 8 completed", UVM_MEDIUM)
    endtask

    // Coverage reporting
    task report_coverage_statistics();
        `uvm_info("ADV_COV_TEST", "===========================================", UVM_LOW)
        `uvm_info("ADV_COV_TEST", "Advanced Coverage Test Results Summary", UVM_LOW)
        `uvm_info("ADV_COV_TEST", "===========================================", UVM_LOW)
        
        // Coverage will be reported by dsim's coverage analysis
        `uvm_info("ADV_COV_TEST", "Coverage report generated in metrics.db", UVM_LOW)
        `uvm_info("ADV_COV_TEST", "Use: dcreport.exe metrics.db -out_dir coverage_report", UVM_LOW)
    endtask
    
endclass

