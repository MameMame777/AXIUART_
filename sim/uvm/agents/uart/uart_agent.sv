`timescale 1ns / 1ps

// UART Agent for UART-AXI4 Bridge UVM Testbench
class uart_agent extends uvm_agent;
    
    `uvm_component_utils(uart_agent)
    
    // Components
    uart_driver driver;
    uart_monitor monitor;
    uvm_sequencer #(uart_frame_transaction) sequencer;
    uvm_tlm_analysis_fifo#(uart_frame_transaction) monitor_tx_fifo;
    
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
        `uvm_info("UART_AGENT_DBG", $sformatf("Monitor created: %s", (monitor == null) ? "NULL" : monitor.get_full_name()), UVM_LOW)
        
        // Create driver and sequencer only if agent is active
        if (cfg.uart_agent_is_active) begin
            driver = uart_driver::type_id::create("driver", this);
            sequencer = uvm_sequencer#(uart_frame_transaction)::type_id::create("sequencer", this);
            
            uvm_config_db#(uart_axi4_env_config)::set(this, "driver", "cfg", cfg);
            monitor_tx_fifo = new("monitor_tx_fifo", this);
                `uvm_info("UART_AGENT_FIFO", $sformatf("Created monitor_tx_fifo (registered as tx_response_fifo) monitor_tx_fifo==%s", (monitor_tx_fifo==null) ? "NULL" : "NOT_NULL"), UVM_LOW)
            `uvm_info("UART_AGENT_DBG", $sformatf("Created monitor_tx_fifo (non-null=%0d) obj=%0p", (monitor_tx_fifo != null) ? 1 : 0, monitor_tx_fifo), UVM_LOW)
            uvm_config_db#(uvm_tlm_analysis_fifo#(uart_frame_transaction))::set(this,
                                                                               "driver",
                                                                               "tx_response_fifo",
                                                                               monitor_tx_fifo);
        end
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect driver to sequencer if active
        if (cfg.uart_agent_is_active && driver != null && sequencer != null) begin
            `uvm_info("UART_AGENT_DBG", $sformatf("connect_phase: driver=%s sequencer=%s monitor=%s monitor_tx_fifo_nonnull=%0d",
                                                driver.get_full_name(),
                                                sequencer.get_full_name(),
                                                (monitor == null) ? "NULL" : monitor.get_full_name(),
                                                (monitor_tx_fifo != null) ? 1 : 0), UVM_LOW)
            driver.seq_item_port.connect(sequencer.seq_item_export);
            if (monitor_tx_fifo != null) begin
                monitor.item_collected_port.connect(monitor_tx_fifo.analysis_export);
                `uvm_info("UART_AGENT_DBG", "Connected monitor.item_collected_port to monitor_tx_fifo.analysis_export", UVM_LOW)
                    `uvm_info("UART_AGENT_CONNECT", $sformatf("Connect phase: monitor.item_collected_port=%s monitor_tx_fifo=%s", (monitor.item_collected_port==null)?"NULL":"NOT_NULL", (monitor_tx_fifo==null)?"NULL":"NOT_NULL"), UVM_LOW)
            end else begin
                `uvm_info("UART_AGENT_DBG", "monitor_tx_fifo is NULL in connect_phase; no connection made", UVM_LOW)
            end
        end
    endfunction

endclass