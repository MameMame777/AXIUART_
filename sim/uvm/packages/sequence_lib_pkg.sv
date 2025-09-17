`timescale 1ns / 1ps

// Test Package containing all sequences and tests
package sequence_lib_pkg;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // Import other packages
    import uart_axi4_test_pkg::*;
    
    // Include sequence files
    `include "../sequences/basic_func_sequence.sv"
    `include "../sequences/error_injection_sequence.sv" 
    `include "../sequences/performance_test_sequence.sv"
    
endpackage