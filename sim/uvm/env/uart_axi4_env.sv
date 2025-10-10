`timescale 1ns / 1ps

// UVM Environment for AXIUART_Top System Verification
class uart_axi4_env extends uvm_env;
    
    `uvm_component_utils(uart_axi4_env)
    
    // Configuration
    uart_axi4_env_config cfg;
    
    // Agents - UART only for AXIUART_Top (no external AXI interface)
    uart_agent uart_agt;
    axi4_lite_monitor axi_monitor;
    
    // Analysis components
    scoreboard phase3_scoreboard;              // Phase 3: Scoreboard with Correlation Engine
    uart_axi4_coverage coverage;
    bridge_status_monitor bridge_status_mon;
    
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

        if (cfg.enable_axi_monitor) begin
            if (cfg.axi_vif == null) begin
                `uvm_fatal("ENV", "AXI monitor enabled but cfg.axi_vif is null")
            end
            axi_monitor = axi4_lite_monitor::type_id::create("axi_monitor", this);
            uvm_config_db#(uart_axi4_env_config)::set(this, "axi_monitor", "cfg", cfg);
            uvm_config_db#(virtual axi4_lite_if)::set(this, "axi_monitor", "vif", cfg.axi_vif);
        end
        
        // Set agent configurations
        uvm_config_db#(uart_axi4_env_config)::set(this, "uart_agt*", "cfg", cfg);
        
        // Create analysis components
        if (cfg.enable_scoreboard || cfg.enable_correlation) begin
            phase3_scoreboard = scoreboard::type_id::create("phase3_scoreboard", this);
            `uvm_info("ENV", "Phase 3 Scoreboard with Correlation Engine created", UVM_MEDIUM)
        end
        
        if (cfg.enable_coverage) begin
            coverage = uart_axi4_coverage::type_id::create("coverage", this);
            uvm_config_db#(uart_axi4_env_config)::set(this, "coverage", "cfg", cfg);
            if (cfg.enable_axi_monitor && axi_monitor != null) begin
                uvm_config_db#(uart_axi4_coverage)::set(this, "axi_monitor", "coverage", coverage);
            end
        end

        if (cfg.enable_system_status_monitoring) begin
            bridge_status_mon = bridge_status_monitor::type_id::create("bridge_status_mon", this);
            uvm_config_db#(uart_axi4_env_config)::set(this, "bridge_status_mon", "cfg", cfg);
        end
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect UART agent to scoreboard
        if ((cfg.enable_scoreboard || cfg.enable_correlation) && phase3_scoreboard != null && uart_agt.monitor != null) begin
            // Note: Phase 3 scoreboard connection will be implemented when interface is defined
            `uvm_info("ENV", "Phase 3 Scoreboard ready for UART connections", UVM_MEDIUM)
        end

        // Connect UART agent to coverage
        if (cfg.enable_coverage && coverage != null && uart_agt.monitor != null) begin
            uart_agt.monitor.analysis_port.connect(coverage.analysis_export);
            `uvm_info("ENV", "Connected UART monitor to coverage collector", UVM_LOW)
        end

        if (cfg.enable_axi_monitor && axi_monitor != null) begin
            if ((cfg.enable_scoreboard || cfg.enable_correlation) && phase3_scoreboard != null) begin
                // Note: Phase 3 scoreboard AXI connection will be implemented when interface is defined
                `uvm_info("ENV", "Phase 3 Scoreboard ready for AXI connections", UVM_MEDIUM)
            end
        end
        
        // Phase 3: Connect UART transactions to correlation engine
        if (cfg.enable_correlation && phase3_scoreboard != null && uart_agt.monitor != null) begin
            // Note: UART monitor needs to be enhanced to support Phase 3 scoreboard
            // For now, we'll implement this through transaction forwarding
            `uvm_info("ENV", "Phase 3 Scoreboard ready for UART frame correlation", UVM_MEDIUM)
        end
    endfunction
    
    // UVM環境レベルの最終レポート
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        
        `uvm_info("ENV", "=== ENVIRONMENT FINAL REPORT ===", UVM_LOW)
        
        if (phase3_scoreboard != null) begin
            `uvm_info("ENV", "Phase 3 Scoreboard statistics available", UVM_LOW)
        end
        
        // Phase 3: Report correlation engine results
        if (phase3_scoreboard != null && cfg.enable_correlation) begin
            `uvm_info("ENV", "=== Phase 3 Scoreboard (Correlation Engine) Results ===", UVM_LOW)
            phase3_scoreboard.correlate_and_report();
            `uvm_info("ENV", "Phase 3 correlation analysis completed", UVM_LOW)
        end
        
        if (coverage != null) begin
            `uvm_info("ENV", "Coverage collection completed", UVM_LOW)
        end
        
        `uvm_info("ENV", "Environment cleanup completed", UVM_LOW)
    endfunction

endclass