// UART-AXI4 Bridge UVM Environment
// Target Board: Zybo Z7-20
// Date: July 26, 2025
// Description: UVM environment for UART-AXI4 bridge testing

`ifndef UART_AXI4_ENV_SV
`define UART_AXI4_ENV_SV

class uart_axi4_env extends uvm_env;
    
    // Agent instances
    axi4_lite_agent axi_agent;
    uart_agent      uart_agent_inst;
    
    // Scoreboard for checking
    uart_axi4_scoreboard scoreboard;
    
    // Coverage collector
    uart_axi4_coverage coverage;
    
    // Configuration object
    uart_axi4_env_config env_cfg;
    
    // UVM registration
    `uvm_component_utils(uart_axi4_env)
    
    // Constructor
    function new(string name = "uart_axi4_env", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get environment configuration
        if (!uvm_config_db#(uart_axi4_env_config)::get(this, "", "env_cfg", env_cfg)) begin
            `uvm_info("ENV", "No env_cfg found, creating default configuration", UVM_LOW)
            env_cfg = uart_axi4_env_config::type_id::create("env_cfg");
        end
        
        // Configure agents
        uvm_config_db#(bit)::set(this, "axi_agent", "is_active", env_cfg.axi_agent_active);
        uvm_config_db#(bit)::set(this, "uart_agent_inst", "is_active", env_cfg.uart_agent_active);
        
        // Create agents
        axi_agent = axi4_lite_agent::type_id::create("axi_agent", this);
        uart_agent_inst = uart_agent::type_id::create("uart_agent_inst", this);
        
        // Create scoreboard if enabled
        if (env_cfg.has_scoreboard) begin
            scoreboard = uart_axi4_scoreboard::type_id::create("scoreboard", this);
        end
        
        // Create coverage collector if enabled
        if (env_cfg.has_coverage) begin
            coverage = uart_axi4_coverage::type_id::create("coverage", this);
        end
        
        `uvm_info("ENV", "Environment build phase completed", UVM_MEDIUM)
    endfunction
    
    // Connect phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect agents to scoreboard
        if (env_cfg.has_scoreboard) begin
            axi_agent.monitor.ap.connect(scoreboard.axi_export);
            uart_agent_inst.tx_ap.connect(scoreboard.uart_tx_export);
            uart_agent_inst.rx_ap.connect(scoreboard.uart_rx_export);
        end
        
        // Connect agents to coverage collector
        if (env_cfg.has_coverage) begin
            axi_agent.monitor.ap.connect(coverage.axi_export);
            uart_agent_inst.tx_ap.connect(coverage.uart_tx_export);
            uart_agent_inst.rx_ap.connect(coverage.uart_rx_export);
        end
        
        `uvm_info("ENV", "Environment connect phase completed", UVM_MEDIUM)
    endfunction
    
    // End of elaboration phase
    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        
        // Print topology
        if (env_cfg.print_topology) begin
            `uvm_info("ENV", "=== Environment Topology ===", UVM_LOW)
            this.print();
            `uvm_info("ENV", "===========================", UVM_LOW)
        end
    endfunction
    
    // Start of simulation phase
    virtual function void start_of_simulation_phase(uvm_phase phase);
        super.start_of_simulation_phase(phase);
        
        // Enable MXD waveform dump
        `ifdef DSIM
            $dumpfile("uart_axi4_env.mxd");
            $dumpvars(0, this);
            `uvm_info("ENV", "MXD waveform dump enabled for environment", UVM_LOW)
        `endif
        
        `uvm_info("ENV", "Environment simulation started", UVM_LOW)
    endfunction
    
    // Report phase
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        
        `uvm_info("ENV", "=== Environment Test Summary ===", UVM_LOW)
        
        if (env_cfg.has_scoreboard) begin
            scoreboard.report_status();
        end
        
        if (env_cfg.has_coverage) begin
            coverage.report_coverage();
        end
        
        `uvm_info("ENV", "===============================", UVM_LOW)
    endfunction

endclass

`endif // UART_AXI4_ENV_SV
