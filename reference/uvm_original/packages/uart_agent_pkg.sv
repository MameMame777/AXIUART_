// UART UVM Agent Package
// Target Board: Zybo Z7-20
// Date: July 26, 2025
// Description: UVM agent package for UART interface

`ifndef UART_AGENT_PKG_SV
`define UART_AGENT_PKG_SV

package uart_agent_pkg;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // UART Protocol Parameters
    parameter int UART_DATA_WIDTH = 8;
    parameter int UART_BAUD_RATE = 115200;
    parameter int UART_CLK_FREQ = 125000000;
    parameter int UART_CLK_DIV = UART_CLK_FREQ / UART_BAUD_RATE;
    
    // UART Frame Parameters
    parameter int START_BITS = 1;
    parameter int DATA_BITS = 8;
    parameter int STOP_BITS = 1;
    parameter int PARITY_BITS = 0;  // No parity
    parameter int FRAME_BITS = START_BITS + DATA_BITS + STOP_BITS + PARITY_BITS;
    
    // Include UART agent files
    `include "../agents/uart/uart_transaction.sv"
    `include "../agents/uart/uart_driver.sv"
    `include "../agents/uart/uart_monitor.sv"
    `include "../agents/uart/uart_sequencer.sv"
    `include "../agents/uart/uart_agent.sv"

endpackage

`endif // UART_AGENT_PKG_SV
