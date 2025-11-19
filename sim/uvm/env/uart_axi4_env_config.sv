`timescale 1ns / 1ps

// UVM Environment Configuration for UART-AXI4 Bridge
class uart_axi4_env_config extends uvm_object;
    
    // Clock and timing parameters
    int clk_freq_hz = CLK_FREQ_HZ;
    // Baud rate must match DUT parameterization (Uart_Axi4_Bridge.BAUD_RATE)
    int baud_rate = 9_600;
    int bit_time_ns;
    int byte_time_ns;
    
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
    bit enable_uvm_loopback_mode = 1'b0;       // Loopback mode (driver/monitor only)
    bit loopback_disable_scoreboard = 1'b1;    // Disable scoreboard when loopback active
    bit loopback_disable_coverage = 1'b1;      // Disable coverage when loopback active
    bit loopback_disable_axi_monitor = 1'b1;   // Disable AXI monitor when loopback active
    
    // Virtual interfaces
    virtual uart_if uart_vif;
    virtual bridge_status_if bridge_status_vif;
    virtual axi4_lite_if axi_vif;
    // AXIUART_Top exposes internal AXI via virtual interface for monitoring
    
    // UART protocol parameters
    int min_uart_response_delay = 1;
    int max_uart_response_delay = 10;
    
    // Timeout values (increased for extended debug runs)
    int frame_timeout_ns = 200_000; // 200us (temporary debug increase)
    int system_timeout_cycles = 1000;
    int axi_timeout_cycles = 1000;
    bit enable_simulation_watchdog = 1'b1;
    bit lock_simulation_timeout = 1'b1;
    int simulation_timeout_multiplier = 4096;
    longint unsigned simulation_timeout_min_ns = 5_000_000;
    longint unsigned simulation_timeout_override_ns = 0;
    
    // Test stimulus parameters
    int num_transactions = 100;
    int min_idle_cycles = 2;
    int max_idle_cycles = 10;
    int bit_time_cycles;
    int half_bit_cycles;
    
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
        `uvm_field_int(enable_uvm_loopback_mode, UVM_ALL_ON)
        `uvm_field_int(loopback_disable_scoreboard, UVM_ALL_ON)
        `uvm_field_int(loopback_disable_coverage, UVM_ALL_ON)
        `uvm_field_int(loopback_disable_axi_monitor, UVM_ALL_ON)
        `uvm_field_int(frame_timeout_ns, UVM_ALL_ON)
        `uvm_field_int(system_timeout_cycles, UVM_ALL_ON)
        `uvm_field_int(axi_timeout_cycles, UVM_ALL_ON)
        `uvm_field_int(enable_simulation_watchdog, UVM_ALL_ON)
        `uvm_field_int(lock_simulation_timeout, UVM_ALL_ON)
        `uvm_field_int(simulation_timeout_multiplier, UVM_ALL_ON)
        `uvm_field_int(simulation_timeout_min_ns, UVM_ALL_ON)
        `uvm_field_int(simulation_timeout_override_ns, UVM_ALL_ON)
        `uvm_field_int(num_transactions, UVM_ALL_ON)
        `uvm_field_int(min_idle_cycles, UVM_ALL_ON)
    `uvm_field_int(max_idle_cycles, UVM_ALL_ON)
    `uvm_field_int(bit_time_cycles, UVM_ALL_ON)
    `uvm_field_int(half_bit_cycles, UVM_ALL_ON)
    `uvm_field_real(coverage_warning_threshold, UVM_ALL_ON)
    `uvm_object_utils_end
    
    function new(string name = "uart_axi4_env_config");
        super.new(name);
        baud_rate = BAUD_RATE;
        calculate_timing();
    endfunction
    
    // Calculate timing values based on baud rate
    function void calculate_timing();
        if (baud_rate <= 0) begin
            bit_time_ns = 0;
            byte_time_ns = 0;
            bit_time_cycles = 1;
        end else begin
            bit_time_ns = 1_000_000_000 / baud_rate;
            byte_time_ns = bit_time_ns * 10;
            bit_time_cycles = (clk_freq_hz / baud_rate);
            if (bit_time_cycles < 1) begin
                bit_time_cycles = 1;
            end
        end

        half_bit_cycles = (bit_time_cycles + 1) >> 1;
        if (half_bit_cycles < 1) begin
            half_bit_cycles = 1;
        end

        frame_timeout_ns = (byte_time_ns != 0) ? byte_time_ns * 10 : frame_timeout_ns;

        if (byte_time_ns > 0) begin
            longint unsigned recommended_min;
            recommended_min = longint'(byte_time_ns) * 256;
            if ((simulation_timeout_min_ns == 0) || (simulation_timeout_min_ns < recommended_min)) begin
                simulation_timeout_min_ns = recommended_min;
            end
        end
    endfunction

    function int get_bit_time_cycles();
        return (bit_time_cycles > 0) ? bit_time_cycles : 1;
    endfunction

    function int get_half_bit_cycles();
        return (half_bit_cycles > 0) ? half_bit_cycles : 1;
    endfunction

    function time get_bit_period();
        return bit_time_ns;
    endfunction

    function time get_byte_period();
        return byte_time_ns;
    endfunction

    // Resolve the absolute simulation watchdog timeout based on configured thresholds
    function time get_simulation_watchdog_timeout();
        longint unsigned base_timeout;
        longint unsigned resolved_timeout;
        longint unsigned minimum_timeout;

        if (!enable_simulation_watchdog) begin
            return 0;
        end

        if (simulation_timeout_override_ns != 0) begin
            return time'(simulation_timeout_override_ns);
        end

        base_timeout = (frame_timeout_ns > 0) ? longint'(frame_timeout_ns) : 0;
        if ((base_timeout == 0) && (byte_time_ns > 0)) begin
            base_timeout = longint'(byte_time_ns) * 10;
        end
        if (base_timeout == 0) begin
            base_timeout = 1_000_000; // Fallback to 1ms if timing data is unavailable
        end

        resolved_timeout = base_timeout;
        if (simulation_timeout_multiplier > 1) begin
            resolved_timeout = base_timeout * simulation_timeout_multiplier;
        end

        minimum_timeout = simulation_timeout_min_ns;
        if ((minimum_timeout != 0) && (resolved_timeout < minimum_timeout)) begin
            resolved_timeout = minimum_timeout;
        end

        return time'(resolved_timeout);
    endfunction
    
endclass