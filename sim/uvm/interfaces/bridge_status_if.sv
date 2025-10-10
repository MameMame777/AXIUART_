`timescale 1ns / 1ps

// Bridge status interface for simulation-only monitoring
interface bridge_status_if (
    input logic clk
);
    logic rst_n;
    logic bridge_busy;
    logic [7:0] bridge_error;
    logic system_ready;

    modport monitor (
        input clk,
        input rst_n,
        input bridge_busy,
        input bridge_error,
        input system_ready
    );
endinterface
