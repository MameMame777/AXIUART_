/*
 * UART-AXI4 Configuration Class
 * Purpose: Configuration for UART-AXI4 bridge testing
 */

`timescale 1ns / 1ps

`include "uvm_macros.svh"
import uvm_pkg::*;

`ifndef UART_AXI_CONFIG_SV
`define UART_AXI_CONFIG_SV

class uart_axi_config extends uvm_object;
    `uvm_object_utils(uart_axi_config)
    
    // Timing configuration
    time axi_clk_period = 10ns;
    time uart_clk_period = 100ns;
    time reset_duration = 100ns;
    
    // UART configuration
    int baud_rate = 115_200;
    int data_bits = 8;
    int stop_bits = 1;
    string parity = "NONE";
    
    // AXI configuration
    bit [31:0] base_address = 32'h0000_0000;
    
    // Test configuration
    int num_transactions = 10;
    int timeout_cycles = 1000;
    
    function new(string name = "uart_axi_config");
        super.new(name);
    endfunction
endclass

`endif // UART_AXI_CONFIG_SV
