// UART UVM Sequencer
// Target Board: Zybo Z7-20
// Date: July 26, 2025
// Description: UVM sequencer for UART interface

`ifndef UART_SEQUENCER_SV
`define UART_SEQUENCER_SV

class uart_sequencer extends uvm_sequencer #(uart_transaction);
    
    // UVM registration
    `uvm_component_utils(uart_sequencer)
    
    // Constructor
    function new(string name = "uart_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass

`endif // UART_SEQUENCER_SV
