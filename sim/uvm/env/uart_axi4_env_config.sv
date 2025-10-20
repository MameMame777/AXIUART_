`timescale 1ns / 1ps

// UVM Environment Configuration for UART-AXI4 Bridge
class uart_axi4_env_config extends uvm_object;
    
    // Clock and timing parameters
    int clk_freq_hz = 125_000_000;
    // Debug acceleration: temporarily increase baud_rate to speed simulation
    // Reset to 115200 for final runs
    int baud_rate = 10000000; // 10 MHz (fast mode for debug)
    int bit_time_ns = 100; // approx 1e9 / 10e6
    int byte_time_ns = 1000; // bit_time_ns * 10
    
    // Test control parameters
    bit enable_coverage = 1'b1;
    bit enable_scoreboard = 1'b1;
    bit enable_correlation = 1'b1;         // Phase 3: Enable correlation engine
    bit enable_protocol_checking = 1'b1;
    bit enable_axi_monitor = 1'b1;
    bit enable_error_injection = 1'b0;     // Phase 4: Error injection testing
    bit enable_bridge_control_testing = 1'b0; // Phase 4: Bridge control testing
    bit enable_driver_runtime_logs = 1'b1;   // Core driver logging (controlled per test)
    bit enable_driver_debug_logs = 1'b0;    // Detailed driver logging for debug sessions
    bit enable_scoreboard_runtime_logs = 1'b1; // Core scoreboard logging (controlled per test)
    bit enable_scoreboard_metadata_logs = 1'b0; // Detailed scoreboard metadata logging
    int driver_runtime_verbosity = UVM_MEDIUM;   // Driver runtime log level when enabled
    int driver_debug_verbosity = UVM_HIGH;  // Driver debug log level when enabled
    int scoreboard_runtime_verbosity = UVM_LOW; // Scoreboard runtime log level when enabled
    int scoreboard_metadata_verbosity = UVM_HIGH; // Scoreboard metadata log level when enabled
    real coverage_warning_threshold = 80.0; // Minimum total coverage required before raising a warning
    
    // Agent configurations - Modified for AXIUART_Top
    bit uart_agent_is_active = 1'b1;
    bit axi_agent_is_active = 1'b0; // Disabled - AXIUART_Top uses internal AXI only
    
    // System status monitoring
    bit enable_system_status_monitoring = 1'b1;
    int bridge_status_verbosity = UVM_LOW;
    
    // Virtual interfaces
    virtual uart_if uart_vif;
    virtual bridge_status_if bridge_status_vif;
    virtual axi4_lite_if axi_vif;
    // AXIUART_Top exposes internal AXI via virtual interface for monitoring
    
    // UART protocol parameters
    int min_uart_response_delay = 1;
    int max_uart_response_delay = 10;
    
    // Timeout values
    int frame_timeout_ns = 1_000_000; // 1ms
    int system_timeout_cycles = 1000;
    int axi_timeout_cycles = 1000;
    
    // Test stimulus parameters
    int num_transactions = 100;
    int min_idle_cycles = 2;
    int max_idle_cycles = 10;
    
    `uvm_object_utils_begin(uart_axi4_env_config)
        `uvm_field_int(clk_freq_hz, UVM_ALL_ON)
        `uvm_field_int(baud_rate, UVM_ALL_ON)
        `uvm_field_int(bit_time_ns, UVM_ALL_ON)
        `uvm_field_int(byte_time_ns, UVM_ALL_ON)
        `uvm_field_int(enable_coverage, UVM_ALL_ON)
        `uvm_field_int(enable_scoreboard, UVM_ALL_ON)
        `uvm_field_int(enable_correlation, UVM_ALL_ON)      // Phase 3: Correlation Engine
        `uvm_field_int(enable_protocol_checking, UVM_ALL_ON)
        `uvm_field_int(enable_axi_monitor, UVM_ALL_ON)
        `uvm_field_int(enable_error_injection, UVM_ALL_ON)       // Phase 4: Error injection
        `uvm_field_int(enable_bridge_control_testing, UVM_ALL_ON) // Phase 4: Bridge control
    `uvm_field_int(enable_driver_runtime_logs, UVM_ALL_ON)
    `uvm_field_int(enable_driver_debug_logs, UVM_ALL_ON)
    `uvm_field_int(enable_scoreboard_runtime_logs, UVM_ALL_ON)
    `uvm_field_int(enable_scoreboard_metadata_logs, UVM_ALL_ON)
    `uvm_field_int(driver_runtime_verbosity, UVM_ALL_ON)
        `uvm_field_int(driver_debug_verbosity, UVM_ALL_ON)
    `uvm_field_int(scoreboard_runtime_verbosity, UVM_ALL_ON)
        `uvm_field_int(scoreboard_metadata_verbosity, UVM_ALL_ON)
        `uvm_field_int(uart_agent_is_active, UVM_ALL_ON)
        `uvm_field_int(axi_agent_is_active, UVM_ALL_ON)
        `uvm_field_int(enable_system_status_monitoring, UVM_ALL_ON)
        `uvm_field_int(bridge_status_verbosity, UVM_ALL_ON)
        `uvm_field_int(frame_timeout_ns, UVM_ALL_ON)
        `uvm_field_int(system_timeout_cycles, UVM_ALL_ON)
        `uvm_field_int(axi_timeout_cycles, UVM_ALL_ON)
        `uvm_field_int(num_transactions, UVM_ALL_ON)
        `uvm_field_int(min_idle_cycles, UVM_ALL_ON)
    `uvm_field_int(max_idle_cycles, UVM_ALL_ON)
    `uvm_field_real(coverage_warning_threshold, UVM_ALL_ON)
    `uvm_object_utils_end
    
    function new(string name = "uart_axi4_env_config");
        super.new(name);
    endfunction
    
    // Calculate timing values based on baud rate
    function void calculate_timing();
        bit_time_ns = 1_000_000_000 / baud_rate;
        byte_time_ns = bit_time_ns * 10;
        frame_timeout_ns = byte_time_ns * 10; // 10 byte times
    endfunction
    
endclass