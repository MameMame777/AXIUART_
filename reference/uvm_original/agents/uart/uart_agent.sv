// UART UVM Agent
// Target Board: Zybo Z7-20
// Date: July 26, 2025
// Description: UVM agent for UART interface

`ifndef UART_AGENT_SV
`define UART_AGENT_SV

class uart_agent extends uvm_agent;
    
    // Agent components
    uart_sequencer sequencer;
    uart_driver    driver;
    uart_monitor   monitor;
    
    // Configuration
    bit is_active = 1;
    
    // Analysis ports (forwarded from monitor)
    uvm_analysis_port #(uart_transaction) tx_ap;
    uvm_analysis_port #(uart_transaction) rx_ap;
    
    // UVM registration
    `uvm_component_utils(uart_agent)
    
    // Constructor
    function new(string name = "uart_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        if (!uvm_config_db#(bit)::get(this, "", "is_active", is_active)) begin
            `uvm_info("UART_AGENT", "Using default is_active = 1", UVM_LOW)
        end
        
        // Create monitor (always needed)
        monitor = uart_monitor::type_id::create("monitor", this);
        
        // Create analysis ports
        tx_ap = new("tx_ap", this);
        rx_ap = new("rx_ap", this);
        
        // Create driver and sequencer only if active
        if (is_active == UVM_ACTIVE) begin
            sequencer = uart_sequencer::type_id::create("sequencer", this);
            driver = uart_driver::type_id::create("driver", this);
        end
    endfunction
    
    // Connect phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect driver and sequencer if active
        if (is_active == UVM_ACTIVE) begin
            driver.seq_item_port.connect(sequencer.seq_item_export);
        end
        
        // Forward monitor analysis ports
        monitor.tx_ap.connect(tx_ap);
        monitor.rx_ap.connect(rx_ap);
    endfunction

endclass

`endif // UART_AGENT_SV
