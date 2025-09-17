// Sequence Library Package
// Target Board: Zybo Z7-20
// Date: July 26, 2025
// Description: Complete sequence library for UART-AXI4 bridge testing

`ifndef SEQUENCE_LIB_PKG_SV
`define SEQUENCE_LIB_PKG_SV

package sequence_lib_pkg;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // Import agent packages
    import axi4_lite_agent_pkg::*;
    import uart_agent_pkg::*;
    
    // Include all sequence files
    `include "axi4_lite_base_sequence.sv"
    `include "uart_base_sequence.sv"
    `include "basic_func_sequence.sv"
    `include "uart_loopback_sequence.sv"
    `include "error_injection_sequence.sv"
    `include "performance_test_sequence.sv"
    `include "uart_physical_sequence.sv"

endpackage

`endif // SEQUENCE_LIB_PKG_SV
