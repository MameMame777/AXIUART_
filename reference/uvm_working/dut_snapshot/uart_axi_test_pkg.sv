// UART-AXI Test Package
// Purpose: Clean, minimal test package
// Date: August 11, 2025

`timescale 1ns / 1ps

package uart_axi_test_pkg;

    // UVM imports
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // Include test
    `include "uart_axi_basic_test.sv"

endpackage
