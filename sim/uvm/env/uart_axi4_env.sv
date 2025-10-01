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
    uart_axi4_scoreboard scoreboard;
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
        if (cfg.enable_scoreboard) begin
            scoreboard = uart_axi4_scoreboard::type_id::create("scoreboard", this);
            uvm_config_db#(uart_axi4_env_config)::set(this, "scoreboard", "cfg", cfg);
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
        if (cfg.enable_scoreboard && scoreboard != null && uart_agt.monitor != null) begin
            uart_agt.monitor.analysis_port.connect(scoreboard.uart_analysis_imp);
            `uvm_info("ENV", "Connected UART monitor to scoreboard", UVM_LOW)
        end
        
        if (cfg.enable_scoreboard && scoreboard != null && cfg.uart_agent_is_active &&
            uart_agt.driver != null) begin
            uart_agt.driver.tx_request_ap.connect(scoreboard.uart_expected_analysis_imp);
            `uvm_info("ENV", "Connected UART driver to scoreboard metadata stream", UVM_LOW)
        end

        // Connect UART agent to coverage
        if (cfg.enable_coverage && coverage != null && uart_agt.monitor != null) begin
            uart_agt.monitor.analysis_port.connect(coverage.analysis_export);
            `uvm_info("ENV", "Connected UART monitor to coverage collector", UVM_LOW)
        end

        if (cfg.enable_axi_monitor && axi_monitor != null) begin
            if (cfg.enable_scoreboard && scoreboard != null) begin
                axi_monitor.analysis_port.connect(scoreboard.axi_analysis_imp);
                `uvm_info("ENV", "Connected AXI monitor to scoreboard", UVM_LOW)
            end

        end
    endfunction
    
    // UVM環境レベルの最終レポート
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        
        `uvm_info("ENV", "=== ENVIRONMENT FINAL REPORT ===", UVM_LOW)
        
        if (scoreboard != null) begin
            `uvm_info("ENV", $sformatf("Scoreboard Statistics:"), UVM_LOW)
            `uvm_info("ENV", $sformatf("  - Successful matches: %0d", scoreboard.match_count), UVM_LOW)
            `uvm_info("ENV", $sformatf("  - Mismatches found:   %0d", scoreboard.mismatch_count), UVM_LOW)
        end
        
        if (coverage != null) begin
            `uvm_info("ENV", "Coverage collection completed", UVM_LOW)
        end
        
        `uvm_info("ENV", "Environment cleanup completed", UVM_LOW)
    endfunction

endclass