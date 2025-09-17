// AXI4-Lite UVM Agent Package
// Target Board: Zybo Z7-20
// Date: July 26, 2025
// Description: UVM agent for AXI4-Lite interface verification

`ifndef AXI4_LITE_AGENT_PKG_SV
`define AXI4_LITE_AGENT_PKG_SV

package axi4_lite_agent_pkg;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // Import design packages
    import axi4_lite_pkg::*;
    
    // Parameters
    parameter int ADDR_WIDTH = 8;
    parameter int DATA_WIDTH = 32;
    
    // Include UVM components
    `include "../agents/axi4_lite/axi4_lite_transaction.sv"
    `include "../agents/axi4_lite/axi4_lite_sequencer.sv"
    `include "../agents/axi4_lite/axi4_lite_driver.sv"
    `include "../agents/axi4_lite/axi4_lite_monitor.sv"
    `include "../agents/axi4_lite/axi4_lite_agent.sv"
    
endpackage

`endif // AXI4_LITE_AGENT_PKG_SV
