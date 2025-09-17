`timescale 1ns / 1ps

// UVM Environment for UART-AXI4 Bridge
class uart_axi4_env extends uvm_env;
    
    `uvm_component_utils(uart_axi4_env)
    
    // Configuration
    uart_axi4_env_config cfg;
    
    // Agents
    uart_agent uart_agt;
    axi4_lite_agent axi_agt;
    
    // Analysis components
    uart_axi4_scoreboard scoreboard;
    uart_axi4_coverage coverage;
    
    function new(string name = "uart_axi4_env", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        if (!uvm_config_db#(uart_axi4_env_config)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("ENV", "Failed to get configuration object")
        end
        
        // Create agents
        uart_agt = uart_agent::type_id::create("uart_agt", this);
        axi_agt = axi4_lite_agent::type_id::create("axi_agt", this);
        
        // Set agent configurations
        uvm_config_db#(uart_axi4_env_config)::set(this, "uart_agt*", "cfg", cfg);
        uvm_config_db#(uart_axi4_env_config)::set(this, "axi_agt*", "cfg", cfg);
        
        // Create analysis components
        if (cfg.enable_scoreboard) begin
            scoreboard = uart_axi4_scoreboard::type_id::create("scoreboard", this);
            uvm_config_db#(uart_axi4_env_config)::set(this, "scoreboard", "cfg", cfg);
        end
        
        if (cfg.enable_coverage) begin
            coverage = uart_axi4_coverage::type_id::create("coverage", this);
            uvm_config_db#(uart_axi4_env_config)::set(this, "coverage", "cfg", cfg);
        end
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect agents to scoreboard
        if (cfg.enable_scoreboard && scoreboard != null) begin
            uart_agt.monitor.analysis_port.connect(scoreboard.uart_analysis_imp);
            axi_agt.monitor.analysis_port.connect(scoreboard.axi_analysis_imp);
        end
        
        // Connect UART agent to coverage
        if (cfg.enable_coverage && coverage != null) begin
            uart_agt.monitor.analysis_port.connect(coverage.analysis_export);
        end
    endfunction

endclass