// AXI4-Lite UVM Sequencer
// Target Board: Zybo Z7-20
// Date: July 26, 2025
// Description: UVM sequencer for AXI4-Lite interface

`ifndef AXI4_LITE_SEQUENCER_SV
`define AXI4_LITE_SEQUENCER_SV

class axi4_lite_sequencer extends uvm_sequencer #(axi4_lite_transaction);
    
    // UVM registration
    `uvm_component_utils(axi4_lite_sequencer)
    
    // Constructor
    function new(string name = "axi4_lite_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass

`endif // AXI4_LITE_SEQUENCER_SV
