`timescale 1ns / 1ps

// Bridge status interface for simulation-only monitoring
interface bridge_status_if (
    input logic clk
);
    logic rst_n;
    logic bridge_busy;
    logic [7:0] bridge_error;
    logic system_ready;
    
    // Additional signals for enhanced DUT monitoring
    logic [2:0] parser_state;
    logic [2:0] bridge_state;
    logic internal_valid;
    logic response_ready;

    modport monitor (
        input clk,
        input rst_n,
        input bridge_busy,
        input bridge_error,
        input system_ready,
        input parser_state,
        input bridge_state,
        input internal_valid,
        input response_ready
    );
endinterface
