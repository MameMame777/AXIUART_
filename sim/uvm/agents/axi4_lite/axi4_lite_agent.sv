`timescale 1ns / 1ps

// AXI4-Lite Agent for UART-AXI4 Bridge UVM Testbench
class axi4_lite_agent extends uvm_agent;
    
    `uvm_component_utils(axi4_lite_agent)
    
    // Configuration
    uart_axi4_env_config cfg;
    
    // Components
    axi4_lite_monitor monitor;
    axi4_lite_driver driver;
    uvm_sequencer #(axi4_lite_transaction) sequencer;
    
    // Analysis port
    uvm_analysis_port #(axi4_lite_transaction) ap;
    
    function new(string name = "axi4_lite_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        if (!uvm_config_db#(uart_axi4_env_config)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("AXI4_LITE_AGENT", "Failed to get configuration object")
        end
        
        // Create monitor (always present for coverage and checking)
        monitor = axi4_lite_monitor::type_id::create("monitor", this);
        
        // Create driver and sequencer only if agent is active
        if (cfg.axi_agent_is_active == UVM_ACTIVE) begin
            driver = axi4_lite_driver::type_id::create("driver", this);
            sequencer = uvm_sequencer#(axi4_lite_transaction)::type_id::create("sequencer", this);
        end
        
        // Set up analysis port
        ap = new("ap", this);
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect monitor analysis port
        monitor.item_collected_port.connect(ap);
        
        // Connect driver and sequencer if active
        if (cfg.axi_agent_is_active == UVM_ACTIVE) begin
            driver.seq_item_port.connect(sequencer.seq_item_export);
        end
    endfunction
    
endclass