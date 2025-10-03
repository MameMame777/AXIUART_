`timescale 1ns / 1ps

// UART interface definition for UART-AXI4 Bridge
// Provides signals for UART communication and UVM monitoring
interface uart_if (
    input logic clk,
    input logic rst
);

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
    logic byte_received;
    logic byte_transmitted;
    
    // Driver modport - for UVM driver (active agent)
    modport driver (
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
        input byte_received,
        input byte_transmitted,
        input system_busy,
        input system_error,
        input system_ready
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
        output byte_received,
        output byte_transmitted,
        input  system_busy,
        input  system_error,
        input  system_ready
    );

    // Helper tasks for timing calculations
    function automatic int get_bit_period_ns(input int baud_rate);
        return 1_000_000_000 / baud_rate;
    endfunction

    function automatic int get_byte_period_ns(input int baud_rate);
        return get_bit_period_ns(baud_rate) * 10; // 8 data + 1 start + 1 stop
    endfunction

endinterface