`timescale 1ns / 1ps

// UART Agent for UART-AXI4 Bridge UVM Testbench
class uart_agent extends uvm_agent;
    
    `uvm_component_utils(uart_agent)
    
    // Components
    uart_driver driver;
    uart_monitor monitor;
    uvm_sequencer #(uart_frame_transaction) sequencer;
    
    // Configuration
    uart_axi4_env_config cfg;
    
    function new(string name = "uart_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        if (!uvm_config_db#(uart_axi4_env_config)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("UART_AGENT", "Failed to get configuration object")
        end
        
        // Create monitor (always present)
        monitor = uart_monitor::type_id::create("monitor", this);
        uvm_config_db#(uart_axi4_env_config)::set(this, "monitor", "cfg", cfg);
        
        // Create driver and sequencer only if agent is active
        if (cfg.uart_agent_is_active) begin
            driver = uart_driver::type_id::create("driver", this);
            sequencer = uvm_sequencer#(uart_frame_transaction)::type_id::create("sequencer", this);
            
            uvm_config_db#(uart_axi4_env_config)::set(this, "driver", "cfg", cfg);
        end
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect driver to sequencer if active
        if (cfg.uart_agent_is_active && driver != null && sequencer != null) begin
            driver.seq_item_port.connect(sequencer.seq_item_export);
        end
    endfunction

endclass