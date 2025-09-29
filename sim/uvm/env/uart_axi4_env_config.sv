`timescale 1ns / 1ps

// UVM Environment Configuration for UART-AXI4 Bridge
class uart_axi4_env_config extends uvm_object;
    
    // Clock and timing parameters
    int clk_freq_hz = 50_000_000;
    int baud_rate = 115200;
    int bit_time_ns = 8680; // 1/115200 * 1e9
    int byte_time_ns = 86800; // bit_time_ns * 10
    
    // Test control parameters
    bit enable_coverage = 1'b1;
    bit enable_scoreboard = 1'b1;
    bit enable_protocol_checking = 1'b1;
    bit enable_axi_monitor = 1'b1;
    
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
        `uvm_field_int(enable_protocol_checking, UVM_ALL_ON)
        `uvm_field_int(enable_axi_monitor, UVM_ALL_ON)
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