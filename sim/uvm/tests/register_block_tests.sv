`timescale 1ns / 1ps

`include "uvm_macros.svh"
import uvm_pkg::*;
import uart_axi4_test_pkg::*;

// Register validation tests leveraging UART stimulus (Phase 4 Day 1)

// Base class providing shared utilities for UART-driven register tests
class register_validation_base_test extends uart_axi4_base_test;
    `uvm_component_utils(register_validation_base_test)

    function new(string name = "register_validation_base_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Wait for DUT reset deassertion and provide settling time
    task automatic wait_for_reset_release();
        wait (uart_axi4_tb_top.rst_n == 1'b1);
        repeat (50) @(posedge uart_axi4_tb_top.clk);
    endtask
endclass

// Day 1 Morning: Comprehensive register access campaign
class register_comprehensive_test extends register_validation_base_test;
    `uvm_component_utils(register_comprehensive_test)

    function new(string name = "register_comprehensive_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
    register_comprehensive_access_sequence access_seq;
    register_alignment_sequence alignment_seq;
        register_disable_window_campaign_sequence disable_seq;
        uart_axi4_error_sequence error_seq;

        phase.raise_objection(this, "Executing register comprehensive access sequence");

        wait_for_reset_release();

        access_seq = register_comprehensive_access_sequence::type_id::create("access_seq");
        if (env == null || env.uart_agt == null || env.uart_agt.sequencer == null) begin
            `uvm_fatal(get_type_name(), "UART agent sequencer is not available")
        end

        access_seq.start(env.uart_agt.sequencer);

    alignment_seq = register_alignment_sequence::type_id::create("alignment_seq");
    alignment_seq.start(env.uart_agt.sequencer);

        disable_seq = register_disable_window_campaign_sequence::type_id::create("disable_seq");
        disable_seq.start(env.uart_agt.sequencer);

        error_seq = uart_axi4_error_sequence::type_id::create("error_seq");
        error_seq.start(env.uart_agt.sequencer);

        // Allow post-sequence settling for coverage sampling
        repeat (2000) @(posedge uart_axi4_tb_top.clk);

        phase.drop_objection(this, "Register comprehensive sequence completed");
    endtask
endclass

// Day 1 Afternoon: Read/write pattern coverage exercise
class register_rw_pattern_test extends register_validation_base_test;
    `uvm_component_utils(register_rw_pattern_test)

    function new(string name = "register_rw_pattern_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        register_rw_pattern_sequence pattern_seq;

        phase.raise_objection(this, "Executing register read/write pattern sequence");

        wait_for_reset_release();

        pattern_seq = register_rw_pattern_sequence::type_id::create("pattern_seq");
        if (env == null || env.uart_agt == null || env.uart_agt.sequencer == null) begin
            `uvm_fatal(get_type_name(), "UART agent sequencer is not available")
        end

        pattern_seq.start(env.uart_agt.sequencer);

        // Allow scoreboard and coverage components to capture responses
        repeat (1500) @(posedge uart_axi4_tb_top.clk);

        phase.drop_objection(this, "Register read/write pattern sequence completed");
    endtask
endclass
