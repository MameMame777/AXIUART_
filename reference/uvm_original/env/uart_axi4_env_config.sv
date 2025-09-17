// UART-AXI4 Bridge Environment Configuration
// Target Board: Zybo Z7-20
// Date: July 26, 2025
// Description: Configuration class for UVM environment

`ifndef UART_AXI4_ENV_CONFIG_SV
`define UART_AXI4_ENV_CONFIG_SV

class uart_axi4_env_config extends uvm_object;
    
    // Agent configuration
    bit axi_agent_active = 1;
    bit uart_agent_active = 1;
    
    // Environment features
    bit has_scoreboard = 1;
    bit has_coverage = 1;
    bit print_topology = 1;
    
    // Test configuration
    int max_errors = 10;
    time timeout = 10ms;
    
    // Debug configuration
    bit enable_debug_prints = 1;
    bit enable_waveform_dump = 1;
    
    // UART-specific configuration
    int uart_baud_rate = 115200;
    bit uart_flow_control_enable = 1;
    int uart_fifo_threshold_tx = 32;
    int uart_fifo_threshold_rx = 16;
    
    // AXI4-Lite configuration
    bit [31:0] axi_base_address = 32'h43C00000;
    int axi_data_width = 32;
    int axi_addr_width = 32;
    
    // UVM registration
    `uvm_object_utils_begin(uart_axi4_env_config)
        `uvm_field_int(axi_agent_active, UVM_DEFAULT)
        `uvm_field_int(uart_agent_active, UVM_DEFAULT)
        `uvm_field_int(has_scoreboard, UVM_DEFAULT)
        `uvm_field_int(has_coverage, UVM_DEFAULT)
        `uvm_field_int(print_topology, UVM_DEFAULT)
        `uvm_field_int(max_errors, UVM_DEFAULT)
        `uvm_field_int(timeout, UVM_DEFAULT)
        `uvm_field_int(enable_debug_prints, UVM_DEFAULT)
        `uvm_field_int(enable_waveform_dump, UVM_DEFAULT)
        `uvm_field_int(uart_baud_rate, UVM_DEFAULT)
        `uvm_field_int(uart_flow_control_enable, UVM_DEFAULT)
        `uvm_field_int(uart_fifo_threshold_tx, UVM_DEFAULT)
        `uvm_field_int(uart_fifo_threshold_rx, UVM_DEFAULT)
        `uvm_field_int(axi_base_address, UVM_DEFAULT | UVM_HEX)
        `uvm_field_int(axi_data_width, UVM_DEFAULT)
        `uvm_field_int(axi_addr_width, UVM_DEFAULT)
    `uvm_object_utils_end
    
    // Constructor
    function new(string name = "uart_axi4_env_config");
        super.new(name);
    endfunction
    
    // Validation function
    virtual function bit is_valid();
        if (uart_baud_rate <= 0) begin
            `uvm_error("ENV_CFG", "Invalid UART baud rate")
            return 0;
        end
        
        if (uart_fifo_threshold_tx > 64 || uart_fifo_threshold_rx > 64) begin
            `uvm_error("ENV_CFG", "FIFO threshold exceeds maximum capacity")
            return 0;
        end
        
        if (axi_data_width != 32) begin
            `uvm_error("ENV_CFG", "Only 32-bit AXI4-Lite data width supported")
            return 0;
        end
        
        return 1;
    endfunction
    
    // Configure for different test types
    function void configure_for_basic_test();
        has_scoreboard = 1;
        has_coverage = 0;
        enable_debug_prints = 1;
        max_errors = 5;
        timeout = 1ms;
    endfunction
    
    function void configure_for_performance_test();
        has_scoreboard = 0;
        has_coverage = 1;
        enable_debug_prints = 0;
        max_errors = 100;
        timeout = 50ms;
    endfunction
    
    function void configure_for_error_test();
        has_scoreboard = 1;
        has_coverage = 1;
        enable_debug_prints = 1;
        max_errors = 50;
        timeout = 5ms;
    endfunction

endclass

`endif // UART_AXI4_ENV_CONFIG_SV
