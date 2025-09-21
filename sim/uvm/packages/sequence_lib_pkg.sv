`timescale 1ns / 1ps

// Test Package containing all sequences and tests
package sequence_lib_pkg;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // Status constants for UART protocol
    typedef enum bit [7:0] {
        STATUS_OK           = 8'h00,
        STATUS_CRC_ERROR    = 8'h01,
        STATUS_ADDR_ALIGN   = 8'h02,
        STATUS_TIMEOUT      = 8'h03,
        STATUS_INVALID_CMD  = 8'h04
    } status_e;

    // UART Protocol Constants - Import from main package
    // These constants are defined in uart_axi4_test_pkg

    // Import main package for transaction types
    import uart_axi4_test_pkg::*;

endpackage