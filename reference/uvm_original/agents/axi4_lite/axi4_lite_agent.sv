// AXI4-Lite UVM Agent
// Target Board: Zybo Z7-20
// Date: July 26, 2025
// Description: UVM agent for AXI4-Lite interface

`ifndef AXI4_LITE_AGENT_SV
`define AXI4_LITE_AGENT_SV

class axi4_lite_agent extends uvm_agent;
    
    // Agent components
    axi4_lite_sequencer sequencer;
    axi4_lite_driver    driver;
    axi4_lite_monitor   monitor;
    
    // Configuration
    bit is_active = 1;
    
    // UVM registration
    `uvm_component_utils(axi4_lite_agent)
    
    // Constructor
    function new(string name = "axi4_lite_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        if (!uvm_config_db#(bit)::get(this, "", "is_active", is_active)) begin
            `uvm_info("AXI4_LITE_AGENT", "Using default is_active = 1", UVM_LOW)
        end
        
        // Create monitor (always needed)
        monitor = axi4_lite_monitor::type_id::create("monitor", this);
        
        // Create driver and sequencer only if active
        if (is_active == UVM_ACTIVE) begin
            sequencer = axi4_lite_sequencer::type_id::create("sequencer", this);
            driver = axi4_lite_driver::type_id::create("driver", this);
        end
    endfunction
    
    // Connect phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect driver and sequencer if active
        if (is_active == UVM_ACTIVE) begin
            driver.seq_item_port.connect(sequencer.seq_item_export);
        end
    endfunction

endclass

`endif // AXI4_LITE_AGENT_SV
