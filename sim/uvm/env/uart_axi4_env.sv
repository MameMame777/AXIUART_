`timescale 1ns / 1ps

// UVM Environment for AXIUART_Top System Verification
class uart_axi4_env extends uvm_env;
    
    `uvm_component_utils(uart_axi4_env)
    
    // Configuration
    uart_axi4_env_config cfg;
    bit scoreboard_active;
    bit coverage_active;
    bit axi_monitor_active;
    bit status_monitor_active;
    
    // Agents - UART only for AXIUART_Top (no external AXI interface)
    uart_agent uart_agt;
    axi4_lite_monitor axi_monitor;
    uart_uvm_loopback_model loopback_model;
    
    // Analysis components
    uart_axi4_scoreboard phase3_scoreboard;              // Phase 3: Scoreboard with Correlation Engine
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

        scoreboard_active = (cfg.enable_scoreboard || cfg.enable_correlation);
        coverage_active = cfg.enable_coverage;
        axi_monitor_active = cfg.enable_axi_monitor;
        status_monitor_active = cfg.enable_system_status_monitoring;

        if (cfg.enable_uvm_loopback_mode) begin
            if (cfg.loopback_disable_scoreboard) begin
                scoreboard_active = 1'b0;
            end
            if (cfg.loopback_disable_coverage) begin
                coverage_active = 1'b0;
            end
            if (cfg.loopback_disable_axi_monitor) begin
                axi_monitor_active = 1'b0;
            end
        end
        
        // Create agents - UART only for AXIUART_Top system
        uart_agt = uart_agent::type_id::create("uart_agt", this);

        if (axi_monitor_active) begin
            if (cfg.axi_vif == null) begin
                `uvm_fatal("ENV", "AXI monitor enabled but cfg.axi_vif is null")
            end
            `uvm_info("ENV", "=== CREATING AXI MONITOR ===", UVM_HIGH)
            axi_monitor = axi4_lite_monitor::type_id::create("axi_monitor", this);
            `uvm_info("ENV", "=== AXI MONITOR CREATED SUCCESSFULLY ===", UVM_HIGH)
            uvm_config_db#(uart_axi4_env_config)::set(this, "axi_monitor", "cfg", cfg);
            uvm_config_db#(virtual axi4_lite_if)::set(this, "axi_monitor", "vif", cfg.axi_vif);
            `uvm_info("ENV", "=== AXI MONITOR CONFIG SET ===", UVM_HIGH)
        end
        
        // Set agent configurations
        uvm_config_db#(uart_axi4_env_config)::set(this, "uart_agt*", "cfg", cfg);

        if (cfg.enable_uvm_loopback_mode) begin
            loopback_model = uart_uvm_loopback_model::type_id::create("loopback_model", this);
            if (loopback_model == null) begin
                `uvm_fatal("ENV", "Failed to create loopback model while loopback mode enabled")
            end
            uvm_config_db#(uart_axi4_env_config)::set(this, "loopback_model", "cfg", cfg);
            uvm_config_db#(virtual uart_if)::set(this, "loopback_model", "vif", cfg.uart_vif);
        end
        
        // Create analysis components
        if (scoreboard_active) begin
            phase3_scoreboard = uart_axi4_scoreboard::type_id::create("phase3_scoreboard", this);
            `uvm_info("ENV", "Phase 3 Scoreboard with Correlation Engine created", UVM_MEDIUM)
        end
        
        if (coverage_active) begin
            coverage = uart_axi4_coverage::type_id::create("coverage", this);
            uvm_config_db#(uart_axi4_env_config)::set(this, "coverage", "cfg", cfg);
            if (axi_monitor_active && axi_monitor != null) begin
                uvm_config_db#(uart_axi4_coverage)::set(this, "axi_monitor", "coverage", coverage);
            end
        end

        if (status_monitor_active) begin
            bridge_status_mon = bridge_status_monitor::type_id::create("bridge_status_mon", this);
            uvm_config_db#(uart_axi4_env_config)::set(this, "bridge_status_mon", "cfg", cfg);
        end
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        if (scoreboard_active) begin
            connect_scoreboard_streams();
        end

        if (coverage_active) begin
            connect_coverage_streams();
        end

        if (axi_monitor_active) begin
            connect_axi_streams();
        end

        if (cfg.enable_correlation && phase3_scoreboard != null && uart_agt.monitor != null) begin
            `uvm_info("ENV", "Phase 3 Scoreboard ready for UART frame correlation", UVM_MEDIUM)
        end

        if (cfg.enable_uvm_loopback_mode) begin
            if (loopback_model == null) begin
                `uvm_fatal("ENV", "Loopback model not constructed but loopback mode enabled")
            end
            if (uart_agt == null || uart_agt.driver == null) begin
                `uvm_fatal("ENV", "Loopback mode requires UART agent driver instance")
            end
            uart_agt.driver.tx_request_ap.connect(loopback_model.request_export);
            `uvm_info("ENV", "Connected UART driver request port to loopback model", UVM_LOW)
        end
    endfunction
    
    // UVM環境レベルの最終レポート
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info("ENV", "Environment cleanup completed", UVM_LOW)
    endfunction

    protected function void connect_scoreboard_streams();
        if (phase3_scoreboard == null) begin
            `uvm_fatal("ENV", "Scoreboard requested but phase3_scoreboard handle is null")
        end

        if (uart_agt == null) begin
            `uvm_fatal("ENV", "UART agent not constructed; cannot connect scoreboard streams")
        end

        if (uart_agt.monitor == null) begin
            `uvm_fatal("ENV", "UART monitor not available; scoreboard correlation path cannot be established")
        end

        uart_agt.monitor.analysis_port.connect(phase3_scoreboard.uart_analysis_imp);
        `uvm_info("ENV", "Connected UART monitor to Phase 3 Scoreboard (analysis_imp)", UVM_LOW)

        if (uart_agt.driver == null) begin
            `uvm_fatal("ENV", "UART driver not constructed; scoreboard cannot receive metadata")
        end

        uart_agt.driver.tx_request_ap.connect(phase3_scoreboard.uart_expected_analysis_imp);
        `uvm_info("ENV", "Connected UART driver request port to scoreboard metadata input", UVM_LOW)
    endfunction

    protected function void connect_coverage_streams();
        if (coverage == null) begin
            `uvm_fatal("ENV", "Coverage requested but coverage component is null")
        end

        if (uart_agt == null || uart_agt.monitor == null) begin
            `uvm_fatal("ENV", "UART monitor not available; coverage cannot consume transactions")
        end

        uart_agt.monitor.analysis_port.connect(coverage.analysis_export);
        `uvm_info("ENV", "Connected UART monitor to coverage collector", UVM_LOW)
    endfunction

    protected function void connect_axi_streams();
        if (axi_monitor == null) begin
            `uvm_fatal("ENV", "AXI monitor requested but handle is null")
        end

        if (scoreboard_active && phase3_scoreboard != null) begin
            axi_monitor.analysis_port.connect(phase3_scoreboard.axi_analysis_imp);
            `uvm_info("ENV", "Connected AXI monitor to Phase 3 Scoreboard (analysis_imp)", UVM_LOW)
        end

        if (coverage_active && coverage != null) begin
            // Coverage registration handled in build via config_db when needed
            `uvm_info("ENV", "AXI monitor coverage hooks active", UVM_LOW)
        end
    endfunction

endclass