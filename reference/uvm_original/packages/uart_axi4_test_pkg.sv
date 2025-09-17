`timescale 1ns / 1ps

// UART-AXI4 Bridge Test Package
// Purpose: Unified test package following UVM best practices
// Date: August 11, 2025

`ifndef UART_AXI4_TEST_PKG_SV
`define UART_AXI4_TEST_PKG_SV

package uart_axi4_test_pkg;

    // UVM imports
    `include "uvm_macros.svh"
    import uvm_pkg::*;
    
    // Project package imports
    import axi4_lite_pkg::*;
    import uart_agent_pkg::*;
    import axi4_lite_agent_pkg::*;
    
    // Include test environment components
    `include "../env/uart_axi4_env_config.sv"
    `include "../env/uart_axi4_env.sv"
    `include "../env/uart_axi4_scoreboard.sv"
    `include "../env/uart_axi4_coverage.sv"
    
    // Include sequence library
    `include "../sequences/basic_func_sequence.sv"
    `include "../sequences/error_injection_sequence.sv" 
    `include "../sequences/performance_test_sequence.sv"
    // `include "../sequences/protocol_handler_sequences.sv"  // Commented out - separate package
    
    // Include base test class
    `include "../tests/uart_axi4_base_test.sv"
    
    // Include specific test classes
    `include "../tests/uart_axi4_tests.sv"
    `include "../tests/protocol_handler_tests.sv"

endpackage : uart_axi4_test_pkg

`endif // UART_AXI4_TEST_PKG_SV