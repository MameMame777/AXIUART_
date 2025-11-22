`timescale 1ns / 1ps

// UART interface definition for UART-AXI4 Bridge
// Provides signals for UART communication and UVM monitoring
// UVM-compliant reset control: interface owns reset signal generation
interface uart_if (
    input logic clk
);

    // Reset signals (driven by interface reset_dut() task)
    logic rst;      // Active-high reset (for DUT)
    logic rst_n;    // Active-low reset (for DUT)

    // Basic UART signals
    logic uart_tx;
    logic uart_rx;
    
    // Hardware flow control signals
    logic uart_rts_n;    // Request to Send (active low) - FPGA output
    logic uart_cts_n;    // Clear to Send (active low) - FPGA input
    
    // Additional signals for UVM monitoring and control
    logic tx_busy;
    logic rx_valid;
    logic [7:0] rx_data;
    logic rx_error;
    
    // Baud rate control
    logic [15:0] baud_divisor;
    
    // System status signals (from AXIUART_Top)
    logic        system_busy;
    logic [7:0]  system_error;
    logic        system_ready;
    
    // Frame timing for monitoring
    logic frame_start;
    logic frame_end;
    logic frame_complete;   // Added for enhanced scoreboard
    logic byte_received;
    logic byte_transmitted;
    
    // Frame processing monitoring fields
    logic frame_processing_active;
    logic [7:0] current_command;
    logic [31:0] current_address;
    logic [7:0] current_data_length;
    logic [63:0] current_payload;  // Support up to 8 bytes
    logic [7:0] current_crc;
    
    // ========================================================================
    // Monitor Clocking Block (UVM Best Practice)
    // ========================================================================
    // Provides proper setup/hold timing for monitor sampling
    // Input sampling occurs 1 time step before clock edge
    clocking monitor_cb @(posedge clk);
        default input #1step output #0;
        input uart_tx, uart_rx, uart_rts_n, uart_cts_n;
        input tx_busy, rx_valid, rx_data, rx_error;
        input frame_start, frame_end, frame_complete;
        input byte_received, byte_transmitted;
        input frame_processing_active, current_command, current_address;
        input current_data_length, current_payload, current_crc;
    endclocking

    // Testbench-only overrides (loopback mode and diagnostics)
    logic tb_uart_tx_override;
    logic tb_uart_tx_override_en;
    logic tb_loopback_active;
    
    // ========================================================================
    // Driver Clocking Block (UVM Best Practice)
    // ========================================================================
    // Provides proper timing alignment for UART signal generation
    clocking driver_cb @(posedge clk);
        output uart_rx;
        output uart_cts_n;
        input  uart_tx;
        input  uart_rts_n;
        input  tx_busy;
        input  rx_valid;
        input  rx_data;
        input  rx_error;
    endclocking
    
    // Driver modport - for UVM driver (active agent)
    modport driver (
        clocking driver_cb,
        output uart_rx,
        input  uart_tx,
        input  uart_rts_n,      // Monitor RTS output from DUT
        output uart_cts_n,      // Control CTS input to DUT
        output baud_divisor,
        input  tx_busy,
        input  rx_valid,
        input  rx_data,
        input  rx_error
    );
    
    // Monitor modport - for UVM monitor
    modport monitor (
        clocking monitor_cb,
        input uart_tx,
        input uart_rx,
        input uart_rts_n,       // Monitor RTS signal
        input uart_cts_n,       // Monitor CTS signal
        input baud_divisor,
        input tx_busy,
        input rx_valid,
        input rx_data,
        input rx_error,
        input frame_start,
        input frame_end,
        input frame_complete,
        input byte_received,
        input byte_transmitted,
        input system_busy,
        input system_error,
        input system_ready,
        input frame_processing_active,
        input current_command,
        input current_address,
        input current_data_length,
        input current_payload,
        input current_crc
    );
    
    // DUT modport - for connecting to RTL
    modport dut (
        input  uart_rx,
        output uart_tx,
        output uart_rts_n,      // RTS output from DUT
        input  uart_cts_n,      // CTS input to DUT
        output tx_busy,
        output rx_valid,
        output rx_data,
        output rx_error,
        output frame_start,
        output frame_end,
        output frame_complete,
        output byte_received,
        output byte_transmitted,
        input  system_busy,
        input  system_error,
        input  system_ready,
        output frame_processing_active,
        output current_command,
        output current_address,
        output current_data_length,
        output current_payload,
        output current_crc
    );

    // Helper tasks for timing calculations
    function automatic int get_bit_period_ns(input int baud_rate);
        return 1_000_000_000 / baud_rate;
    endfunction

    function automatic int get_byte_period_ns(input int baud_rate);
        return get_bit_period_ns(baud_rate) * 10; // 8 data + 1 start + 1 stop
    endfunction

    // ========================================================================
    // UVM-compliant reset control task
    // Standard pattern: interface owns reset generation, UVM calls this task
    // Reference: IEEE 1800.2-2020 UVM User Guide Section 4.7
    // ========================================================================
    task automatic reset_dut();
        $display("[UART_IF @ %0t] reset_dut() task started, clk=%b", $time, clk);
        
        // Assert reset (active-high for rst, active-low for rst_n)
        rst   = 1'b1;
        rst_n = 1'b0;
        $display("[UART_IF @ %0t] Reset asserted, waiting for 100 clock edges...", $time);
        
        // Hold reset for sufficient duration (800ns = 100 cycles @ 125MHz)
        repeat(100) @(posedge clk);
        $display("[UART_IF @ %0t] 100 cycles elapsed, de-asserting reset...", $time);
        
        // De-assert reset
        rst   = 1'b0;
        rst_n = 1'b1;
        
        // Stabilization period (50 cycles)
        repeat(50) @(posedge clk);
        
        // Interface cannot use UVM macros - use $display instead
        $display("[UART_IF @ %0t] DUT reset completed", $time);
    endtask : reset_dut
    
    // Initialize reset signals at time 0 (before UVM phases start)
    initial begin
        rst   = 1'b1;  // Start in reset
        rst_n = 1'b0;
    end

endinterface
