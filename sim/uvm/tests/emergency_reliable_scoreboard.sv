`timescale 1ns / 1ps

import uvm_pkg::*;
`include "uvm_macros.svh"

// Lightweight scoreboard used when the full environment cannot be constructed.
class emergency_reliable_scoreboard extends uvm_component;
    `uvm_component_utils(emergency_reliable_scoreboard)

    // Basic reliability bookkeeping
    realtime last_update_time;
    real reliability_percentage;
    int total_transactions;
    int total_errors;

    function new(string name = "emergency_reliable_scoreboard", uvm_component parent = null);
        super.new(name, parent);
        reset_metrics();
    endfunction

    // Clear captured statistics so reruns start cleanly.
    virtual function void reset_metrics();
        reliability_percentage = 100.0;
        total_transactions = 0;
        total_errors = 0;
        last_update_time = 0.0;
    endfunction

    // Record a transaction outcome and update the reliability estimate.
    virtual function void record_transaction(bit error_seen);
        total_transactions++;
        if (error_seen) begin
            total_errors++;
        end

        if (total_transactions > 0) begin
            reliability_percentage = 100.0 * (total_transactions - total_errors) / total_transactions;
        end else begin
            reliability_percentage = 100.0;
        end

        last_update_time = $realtime;
    endfunction

    // Provide a concise snapshot for test level logging.
    virtual function void report_status(string id = "EMERGENCY_SCOREBOARD");
        `uvm_info(id,
            $sformatf("Reliability=%0.2f%% transactions=%0d errors=%0d",
                      reliability_percentage, total_transactions, total_errors),
            UVM_LOW)
    endfunction
endclass : emergency_reliable_scoreboard
