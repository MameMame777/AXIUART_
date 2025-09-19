`timescale 1ns / 1ps

// AXIUART Top-Level Integration Module
// Complete system integrating UART-AXI4 bridge with register block
module AXIUART_Top #(
    parameter int CLK_FREQ_HZ = 50_000_000,     // System clock frequency
    parameter int BAUD_RATE = 115200,           // UART baud rate
    parameter int AXI_TIMEOUT = 1000,           // AXI timeout in clock cycles
    parameter int UART_OVERSAMPLE = 16,         // UART oversampling factor
    parameter int RX_FIFO_DEPTH = 64,           // RX FIFO depth
    parameter int TX_FIFO_DEPTH = 64,           // TX FIFO depth
    parameter int MAX_LEN = 16,                 // Maximum LEN field value
    parameter int REG_BASE_ADDR = 32'h0000_1000 // Register block base address
)(
    // Clock and reset
    input  logic        clk,
    input  logic        rst,
    
    // UART interface (external connections)
    input  logic        uart_rx,
    output logic        uart_tx,
    
    // System status outputs
    output logic        system_busy,
    output logic [7:0]  system_error,
    output logic        system_ready
);

    // Internal AXI4-Lite interface connecting UART bridge to register block
    axi4_lite_if #(
        .ADDR_WIDTH(32),
        .DATA_WIDTH(32)
    ) axi_internal (
        .clk(clk),
        .rst(rst)
    );
    
    // Bridge control and status signals
    logic        bridge_enable;
    logic        bridge_reset_stats;
    logic [7:0]  baud_div_config;
    logic [7:0]  timeout_config;
    logic [3:0]  debug_mode;
    
    logic        bridge_busy;
    logic [7:0]  bridge_error_code;
    logic [15:0] tx_count;
    logic [15:0] rx_count;
    logic [7:0]  fifo_status;
    
    // Internal reset logic
    logic internal_rst;
    assign internal_rst = rst || ~bridge_enable;
    
    // UART-AXI4 Bridge instantiation
    Uart_Axi4_Bridge #(
        .CLK_FREQ_HZ(CLK_FREQ_HZ),
        .BAUD_RATE(BAUD_RATE),
        .AXI_TIMEOUT(AXI_TIMEOUT),
        .UART_OVERSAMPLE(UART_OVERSAMPLE),
        .RX_FIFO_DEPTH(RX_FIFO_DEPTH),
        .TX_FIFO_DEPTH(TX_FIFO_DEPTH),
        .MAX_LEN(MAX_LEN)
    ) uart_bridge_inst (
        .clk(clk),
        .rst(internal_rst),
        .uart_rx(uart_rx),
        .uart_tx(uart_tx),
        .axi(axi_internal),  // 内部レジスタブロックに直接接続
        
        // Status monitoring connections
        .bridge_busy(bridge_busy),
        .bridge_error_code(bridge_error_code),
        .tx_transaction_count(tx_count),
        .rx_transaction_count(rx_count),
        .fifo_status_flags(fifo_status),
        .reset_statistics(bridge_reset_stats)
    );
    
    // Register Block instantiation - UART bridgeからのみアクセス可能
    Register_Block #(
        .ADDR_WIDTH(32),
        .DATA_WIDTH(32),
        .BASE_ADDR(REG_BASE_ADDR)
    ) register_block_inst (
        .clk(clk),
        .rst(rst),
        .axi(axi_internal.slave),  // UARTブリッジからの内部アクセス
        
        // Control outputs
        .bridge_enable(bridge_enable),
        .bridge_reset_stats(bridge_reset_stats),
        .baud_div_config(baud_div_config),
        .timeout_config(timeout_config),
        .debug_mode(debug_mode),
        
        // Status inputs
        .bridge_busy(bridge_busy),
        .error_code(bridge_error_code),
        .tx_count(tx_count),
        .rx_count(rx_count),
        .fifo_status(fifo_status)
    );
    
    // AXI4-Lite Address Router and Interconnect
    // Implements proper AXI handshaking and response multiplexing
    
    // Address decode signals
    // System status outputs (simplified)
    assign system_busy = bridge_busy;
    assign system_error = (bridge_error_code != 8'h00);
    assign system_ready = !system_busy && !system_error;

endmodule
