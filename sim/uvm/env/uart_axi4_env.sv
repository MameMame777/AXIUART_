`timescale 1ns / 1ps

// UVM Environment for AXIUART_Top System Verification
class uart_axi4_env extends uvm_env;
    
    `uvm_component_utils(uart_axi4_env)
    
    // Configuration
    uart_axi4_env_config cfg;
    
    // Agents - UART only for AXIUART_Top (no external AXI interface)
    uart_agent uart_agt;
    // Note: AXI agent disabled - AXIUART_Top uses internal AXI interface only
    
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
        
        // Create agents - UART only for AXIUART_Top system
        uart_agt = uart_agent::type_id::create("uart_agt", this);
        // Note: No AXI agent needed - AXIUART_Top uses internal AXI only
        
        // Set agent configurations
        uvm_config_db#(uart_axi4_env_config)::set(this, "uart_agt*", "cfg", cfg);
        
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
        
        // Connect UART agent to scoreboard
        if (cfg.enable_scoreboard && scoreboard != null && uart_agt.monitor != null) begin
            uart_agt.monitor.analysis_port.connect(scoreboard.uart_analysis_imp);
            `uvm_info("ENV", "Connected UART monitor to scoreboard", UVM_LOW)
        end
        
        // Connect UART agent to coverage
        if (cfg.enable_coverage && coverage != null && uart_agt.monitor != null) begin
            uart_agt.monitor.analysis_port.connect(coverage.analysis_export);
            `uvm_info("ENV", "Connected UART monitor to coverage collector", UVM_LOW)
        end
    endfunction

endclass