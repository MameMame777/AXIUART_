`timescale 1ns / 1ps

// UART-AXI4 Scoreboard with Correlation Engine integration
// Created: October 11, 2025
// Purpose: Scoreboard for UART-AXI4 bridge verification

// Note: correlation_engine.sv is included via package, not directly

class scoreboard extends uvm_component;
    `uvm_component_utils(scoreboard)

    correlation_engine corr_eng;

    function new(string name = "scoreboard", uvm_component parent = null);
        super.new(name, parent);
        corr_eng = correlation_engine::type_id::create("corr_eng", this);
    endfunction

    // Add UART frame to correlation engine
    function void add_uart_frame(uart_frame_transaction frame);
        corr_eng.add_uart_frame(frame);
    endfunction

    // Add AXI transaction to correlation engine
    function void add_axi_transaction(axi4_lite_transaction trans);
        corr_eng.add_axi_transaction(trans);
    endfunction

    // Perform correlation and report results
    function void correlate_and_report();
        corr_eng.correlate();
        corr_eng.clear();
    endfunction

endclass
