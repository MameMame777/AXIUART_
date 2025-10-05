`timescale 1ns/1ps

//================================================================
// Test Register Sequences Package
//================================================================
// This package contains UVM sequences specifically designed for 
// test register validation and protocol debugging
//================================================================

package test_register_sequences_pkg;
    import uvm_pkg::*;
    import uart_axi4_test_pkg::*;
    
    `include "uvm_macros.svh"
    
    // Include test register sequences
    `include "test_register_sequences.sv"
    
endpackage : test_register_sequences_pkg