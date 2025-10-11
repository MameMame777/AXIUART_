`timescale 1ns / 1ps

//=============================================================================
// Extended Basic Test for Toggle Coverage Enhancement
// Purpose: Execute multiple basic test iterations to improve toggle coverage
// Strategy: Multiple runs of working basic test pattern
//=============================================================================

`ifndef EXTENDED_BASIC_TEST_SV
`define EXTENDED_BASIC_TEST_SV

import uvm_pkg::*;
import uart_axi4_test_pkg::*;

class extended_basic_test extends enhanced_uart_axi4_base_test;
    `uvm_component_utils(extended_basic_test)
    
    function new(string name = "extended_basic_test", uvm_component parent = null);
        super.new(name, parent);
        `uvm_info("EXTENDED_BASIC", "Extended Basic Test for Toggle Coverage initialized", UVM_LOW)
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        configure_test_specific_reporting();
        
        // Enhanced configuration for extended testing
        cfg.enable_coverage = 1;
        cfg.enable_scoreboard = 1;
        cfg.enable_protocol_checking = 1;
        cfg.num_transactions = 1000;  // More transactions
        cfg.system_timeout_cycles = 10000;
        
        `uvm_info("EXTENDED_BASIC", "Enhanced configuration for toggle coverage", UVM_LOW)
    endfunction
    
    // Extended test sequence
    virtual task main_phase(uvm_phase phase);
        simple_debug_write_sequence_20250923 debug_seq;
        
        `uvm_info("EXTENDED_BASIC", "================================================", UVM_LOW)
        `uvm_info("EXTENDED_BASIC", "     EXTENDED BASIC TEST FOR TOGGLE COVERAGE", UVM_LOW)
        `uvm_info("EXTENDED_BASIC", "================================================", UVM_LOW)
        `uvm_info("EXTENDED_BASIC", "Target: Improve Toggle Coverage 14% 竊・30%+", UVM_LOW)

        phase.raise_objection(this, "Extended basic test running");

        // Wait for reset to complete
        wait (uart_axi4_tb_top.dut.rst == 1'b0);
        repeat (10) @(posedge uart_axi4_tb_top.dut.clk);
        
        // Execute multiple iterations for toggle coverage
        for (int iteration = 0; iteration < 50; iteration++) begin
            `uvm_info("EXTENDED_BASIC", $sformatf("=== Iteration %0d/50 ===", iteration+1), UVM_MEDIUM)
            
            debug_seq = simple_debug_write_sequence_20250923::type_id::create("debug_seq");
            debug_seq.start(env.uart_agt.sequencer);
            
            // Variable wait time to create different timing patterns
            repeat (50 + (iteration % 100)) @(posedge uart_axi4_tb_top.dut.clk);
            
            if ((iteration + 1) % 10 == 0) begin
                `uvm_info("EXTENDED_BASIC", $sformatf("Completed %0d iterations", iteration+1), UVM_LOW)
            end
        end
        
        // Final system stabilization
        repeat (2000) @(posedge uart_axi4_tb_top.dut.clk);
        `uvm_info("EXTENDED_BASIC", "=== Extended Basic Test Completed ===", UVM_LOW)

        phase.drop_objection(this, "Extended basic test completed");
    endtask

endclass

`endif // EXTENDED_BASIC_TEST_SV
