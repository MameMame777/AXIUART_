// USB-UART-AXI4 Bridge Top Level Module
// Target Board: Zybo Z7-20
// Date: July 26, 2025
// Description: Complete USB-UART-AXI4 bridge integrating all subsystems

`timescale 1ns / 1ps

import axi4_lite_pkg::*;

module Uart_Axi4_Bridge #(
    parameter SYS_CLK_FREQ = 125_000_000,    // System clock frequency in Hz
    parameter BAUD_RATE    = 115_200,        // UART baud rate
    parameter DATA_BITS    = 8,              // Number of data bits (7 or 8)
    parameter STOP_BITS    = 1,              // Number of stop bits (1 or 2)
    parameter PARITY       = "NONE",         // Parity type: "NONE", "EVEN", "ODD"
    parameter FLOW_CONTROL = 1,              // Enable hardware flow control (0/1)
    parameter FIFO_DEPTH   = 64,             // FIFO depth
    parameter ADDR_WIDTH   = 8,              // AXI address width
    parameter DATA_WIDTH   = 32              // AXI data width
)(
    // System interface
    input  logic                     sys_clk,           // System clock (125MHz)
    input  logic                     sys_rst,           // System reset (active high)
    
    // AXI4-Lite Slave interface (for external master connection)
    input  logic [ADDR_WIDTH-1:0]    s_axi_awaddr,      // Write address
    input  logic [2:0]               s_axi_awprot,      // Write protection type
    input  logic                     s_axi_awvalid,     // Write address valid
    output logic                     s_axi_awready,     // Write address ready
    input  logic [DATA_WIDTH-1:0]    s_axi_wdata,       // Write data
    input  logic [(DATA_WIDTH/8)-1:0] s_axi_wstrb,      // Write strobes
    input  logic                     s_axi_wvalid,      // Write valid
    output logic                     s_axi_wready,      // Write ready
    output logic [1:0]               s_axi_bresp,       // Write response
    output logic                     s_axi_bvalid,      // Write response valid
    input  logic                     s_axi_bready,      // Response ready
    input  logic [ADDR_WIDTH-1:0]    s_axi_araddr,      // Read address
    input  logic [2:0]               s_axi_arprot,      // Read protection type
    input  logic                     s_axi_arvalid,     // Read address valid
    output logic                     s_axi_arready,     // Read address ready
    output logic [DATA_WIDTH-1:0]    s_axi_rdata,       // Read data
    output logic [1:0]               s_axi_rresp,       // Read response
    output logic                     s_axi_rvalid,      // Read valid
    input  logic                     s_axi_rready,      // Read ready
    
    // UART physical interface
    output logic                     uart_txd,          // UART transmit data
    input  logic                     uart_rxd,          // UART receive data
    output logic                     uart_rts_n,        // Request to Send (active low)
    input  logic                     uart_cts_n,        // Clear to Send (active low)
    
    // Interrupt output
    output logic                     interrupt_out,     // Interrupt signal
    
    // Debug RGB LEDs for state observation
    output logic                     led5_r,             // Debug LED 5 Red
    output logic                     led5_g,             // Debug LED 5 Green  
    output logic                     led5_b,             // Debug LED 5 Blue
    output logic                     led6_r,             // Debug LED 6 Red
    output logic                     led6_g,             // Debug LED 6 Green
    output logic                     led6_b,             // Debug LED 6 Blue
    
    // Debug interface (optional)
    output logic [3:0]               debug_led           // Debug LEDs
);

    // Internal clock and reset
    logic clk, rst;
    assign clk = sys_clk;
    assign rst = sys_rst;
    
    // Internal AXI4-Lite interface instantiation
    axi4_lite_if #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH)
    ) axi_if (
        .aclk(clk),
        .aresetn(~rst)  // Convert to active-low reset for AXI
    );
    
    // Connect external AXI4-Lite signals to internal interface
    assign axi_if.awaddr = s_axi_awaddr;
    assign axi_if.awprot = s_axi_awprot;
    assign axi_if.awvalid = s_axi_awvalid;
    assign s_axi_awready = axi_if.awready;
    assign axi_if.wdata = s_axi_wdata;
    assign axi_if.wstrb = s_axi_wstrb;
    assign axi_if.wvalid = s_axi_wvalid;
    assign s_axi_wready = axi_if.wready;
    assign s_axi_bresp = axi_if.bresp;
    assign s_axi_bvalid = axi_if.bvalid;
    assign axi_if.bready = s_axi_bready;
    assign axi_if.araddr = s_axi_araddr;
    assign axi_if.arprot = s_axi_arprot;
    assign axi_if.arvalid = s_axi_arvalid;
    assign s_axi_arready = axi_if.arready;
    assign s_axi_rdata = axi_if.rdata;
    assign s_axi_rresp = axi_if.rresp;
    assign s_axi_rvalid = axi_if.rvalid;
    assign axi_if.rready = s_axi_rready;
    
    // AXI4-Lite to Register Bank interface
    logic [ADDR_WIDTH-1:0]   reg_addr;
    logic [DATA_WIDTH-1:0]   reg_wdata;
    logic [(DATA_WIDTH/8)-1:0] reg_wstrb;
    logic                    reg_write;
    logic                    reg_read;
    logic [DATA_WIDTH-1:0]   reg_rdata;
    logic                    reg_ready;
    logic                    reg_error;
    
    // Register Bank outputs
    control_reg_t            control_reg;
    logic                    fifo_reset;
    logic [5:0]              tx_thresh_high, tx_thresh_low;
    logic [5:0]              rx_thresh_high, rx_thresh_low;
    
    // Register Bank inputs
    status_reg_t             status_inputs;
    fifo_status_reg_t        fifo_status;
    error_status_reg_t       error_inputs;
    
    // TX/RX FIFO interfaces
    logic [7:0]              tx_fifo_wr_data;
    logic                    tx_fifo_wr_en;
    logic                    tx_fifo_full;
    logic                    tx_fifo_almost_full;
    logic [6:0]              tx_fifo_count;     // Fixed: 7 bits for 64-depth FIFO
    
    logic [7:0]              tx_fifo_rd_data;
    logic                    tx_fifo_rd_en;
    logic                    tx_fifo_empty;
    logic                    tx_fifo_almost_empty;
    
    logic [7:0]              rx_fifo_wr_data;
    logic                    rx_fifo_wr_en;
    logic                    rx_fifo_full;
    logic                    rx_fifo_almost_full;
    logic [6:0]              rx_fifo_count;     // Fixed: 7 bits for 64-depth FIFO
    
    logic [7:0]              rx_fifo_rd_data;
    logic                    rx_fifo_rd_en;
    logic                    rx_fifo_empty;
    logic                    rx_fifo_almost_empty;
    
    // UART Controller interfaces
    logic                    uart_tx_start;
    logic                    uart_tx_done;
    logic                    uart_tx_active;
    logic                    uart_tx_ready;
    logic [7:0]              uart_rx_data;
    logic                    uart_rx_done;
    logic                    uart_rx_active;
    logic                    uart_parity_error;
    logic                    uart_frame_error;
    logic                    uart_overrun_error;
    
    // Protocol Handler interfaces
    logic [7:0]              protocol_uart_tx_data;
    logic                    protocol_uart_tx_valid;
    logic                    protocol_uart_tx_ready;
    logic                    protocol_uart_rx_ready;
    logic [ADDR_WIDTH-1:0]   protocol_reg_addr;
    logic [DATA_WIDTH-1:0]   protocol_reg_wdata;
    logic                    protocol_reg_write;
    logic                    protocol_reg_read;
    
    // Debug signals from Protocol Handler
    logic [3:0]              debug_protocol_state;
    logic                    debug_cmd_valid;
    logic                    debug_protocol_error;
    
    // Interrupt Controller interfaces
    logic                    error_int_flag;
    logic                    rx_ready_int_flag;
    logic                    tx_done_int_flag;
    logic                    fifo_thresh_int_flag;
    logic                    interrupt_out_internal; // Internal interrupt signal (not exposed externally)
    
    // AXI4-Lite Slave instance (using interface connection)
    Axi4_Lite_Slave #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH)
    ) u_axi4_lite_slave (
        .clk(clk),
        .rst(rst),
        // AXI4-Lite interface connection
        .axi_if(axi_if.slave),
        // Internal register interface
        .reg_addr(reg_addr),
        .reg_wdata(reg_wdata),
        .reg_wstrb(reg_wstrb),
        .reg_write(reg_write),
        .reg_read(reg_read),
        .reg_rdata(reg_rdata),
        .reg_ready(reg_ready),
        .reg_error(reg_error)
    );
    
    // Register Bank instance
    Register_Bank #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH)
    ) u_register_bank (
        .clk(clk),
        .rst(rst),
        .reg_addr(reg_addr),
        .reg_wdata(reg_wdata),
        .reg_wstrb(reg_wstrb),
        .reg_write(reg_write),
        .reg_read(reg_read),
        .reg_rdata(reg_rdata),
        .reg_ready(reg_ready),
        .reg_error(reg_error),
        .control_reg(control_reg),
        .fifo_reset(fifo_reset),
        .tx_thresh_high(tx_thresh_high),
        .tx_thresh_low(tx_thresh_low),
        .rx_thresh_high(rx_thresh_high),
        .rx_thresh_low(rx_thresh_low),
        .status_inputs(status_inputs),
        .fifo_status(fifo_status),
        .error_inputs(error_inputs)
    );
    
    // TX FIFO instance
    Dual_Port_Fifo #(
        .DATA_WIDTH(8),
        .DEPTH(FIFO_DEPTH)
    ) u_tx_fifo (
        .clk(clk),
        .rst(rst),
        .fifo_rst(fifo_reset),
        .wr_en(tx_fifo_wr_en),
        .wr_data(tx_fifo_wr_data),
        .wr_full(tx_fifo_full),
        .wr_almost_full(tx_fifo_almost_full),
        .rd_en(tx_fifo_rd_en),
        .rd_data(tx_fifo_rd_data),
        .rd_empty(tx_fifo_empty),
        .rd_almost_empty(tx_fifo_almost_empty),
        .count(tx_fifo_count),
        .almost_full_thresh(tx_thresh_high),
        .almost_empty_thresh(tx_thresh_low)
    );
    
    // RX FIFO instance
    Dual_Port_Fifo #(
        .DATA_WIDTH(8),
        .DEPTH(FIFO_DEPTH)
    ) u_rx_fifo (
        .clk(clk),
        .rst(rst),
        .fifo_rst(fifo_reset),
        .wr_en(rx_fifo_wr_en),
        .wr_data(rx_fifo_wr_data),
        .wr_full(rx_fifo_full),
        .wr_almost_full(rx_fifo_almost_full),
        .rd_en(rx_fifo_rd_en),
        .rd_data(rx_fifo_rd_data),
        .rd_empty(rx_fifo_empty),
        .rd_almost_empty(rx_fifo_almost_empty),
        .count(rx_fifo_count),
        .almost_full_thresh(rx_thresh_high),
        .almost_empty_thresh(rx_thresh_low)
    );
    
    // UART Controller instance
    Uart_Controller #(
        .SYS_CLK_FREQ(SYS_CLK_FREQ),
        .BAUD_RATE(BAUD_RATE),
        .DATA_BITS(DATA_BITS),
        .STOP_BITS(STOP_BITS),
        .PARITY(PARITY),
        .FLOW_CONTROL(FLOW_CONTROL)
    ) u_uart_controller (
        .clk(clk),
        .rst(rst),
        .uart_enable(control_reg.uart_en),
        .tx_enable(control_reg.tx_en),
        .rx_enable(control_reg.rx_en),
        .uart_txd(uart_txd),
        .uart_rxd(uart_rxd),
        .uart_rts_n(uart_rts_n),
        .uart_cts_n(uart_cts_n),
        .tx_data(tx_fifo_rd_data),
        .tx_start(uart_tx_start),
        .tx_done(uart_tx_done),
        .tx_active(uart_tx_active),
        .tx_ready(uart_tx_ready),
        .rx_data(uart_rx_data),
        .rx_done(uart_rx_done),
        .rx_active(uart_rx_active),
        .rx_fifo_full(rx_fifo_full),
        .parity_error(uart_parity_error),
        .frame_error(uart_frame_error),
        .overrun_error(uart_overrun_error)
    );
    
    // Protocol Handler instance
    // Note: Protocol Handler is always enabled to allow initial configuration
    // The uart_en control is handled at the UART Controller level
    Protocol_Handler #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH)
    ) u_protocol_handler (
        .clk(clk),
        .rst(rst),
        .enable(1'b1),  // Always enabled for protocol communication
        .uart_rx_data(rx_fifo_rd_data),
        .uart_rx_valid(!rx_fifo_empty && protocol_uart_rx_ready),
        .uart_rx_ready(protocol_uart_rx_ready),
        .uart_tx_data(protocol_uart_tx_data),
        .uart_tx_valid(protocol_uart_tx_valid),
        .uart_tx_ready(protocol_uart_tx_ready),
        .reg_addr(protocol_reg_addr),
        .reg_wdata(protocol_reg_wdata),
        .reg_write(protocol_reg_write),
        .reg_read(protocol_reg_read),
        .reg_rdata(reg_rdata),
        .reg_ready(reg_ready),
        .reg_error(reg_error),
        .debug_state(debug_protocol_state),
        .debug_cmd_valid(debug_cmd_valid),
        .debug_error(debug_protocol_error)
    );
    
    // Interrupt Controller instance
    Interrupt_Controller u_interrupt_controller (
        .clk(clk),
        .rst(rst),
        .error_interrupt(uart_parity_error || uart_frame_error || uart_overrun_error),
        .rx_ready_interrupt(!rx_fifo_empty),
        .tx_done_interrupt(uart_tx_done),
        .fifo_thresh_interrupt(tx_fifo_almost_full || rx_fifo_almost_full),
        .error_int_enable(control_reg.int_en_error),
        .rx_ready_int_enable(control_reg.int_en_rx_rdy),
        .tx_done_int_enable(control_reg.int_en_tx_done),
        .fifo_thresh_int_enable(control_reg.int_en_fifo_thr),
        .error_int_flag(error_int_flag),
        .rx_ready_int_flag(rx_ready_int_flag),
        .tx_done_int_flag(tx_done_int_flag),
        .fifo_thresh_int_flag(fifo_thresh_int_flag),
        .error_int_clear(reg_write && (reg_addr == 8'h04) && reg_wdata[7]),    // STATUS_REG address
        .rx_ready_int_clear(reg_write && (reg_addr == 8'h04) && reg_wdata[6]),
        .tx_done_int_clear(reg_write && (reg_addr == 8'h04) && reg_wdata[5]),
        .fifo_thresh_int_clear(reg_write && (reg_addr == 8'h04) && reg_wdata[4]),
        .interrupt_out(interrupt_out)
    );
    
    // UART TX FIFO control logic
    always_ff @(posedge clk) begin
        if (rst) begin
            uart_tx_start <= 1'b0;
        end else begin
            uart_tx_start <= !tx_fifo_empty && uart_tx_ready && control_reg.tx_en;
        end
    end
    
    assign tx_fifo_rd_en = uart_tx_start;
    
    // UART RX FIFO control logic
    assign rx_fifo_wr_en = uart_rx_done && !rx_fifo_full;
    assign rx_fifo_wr_data = uart_rx_data;
    assign rx_fifo_rd_en = protocol_uart_rx_ready && !rx_fifo_empty;
    
    // Protocol Handler TX to UART TX FIFO bridge
    assign tx_fifo_wr_en = protocol_uart_tx_valid && !tx_fifo_full;
    assign tx_fifo_wr_data = protocol_uart_tx_data;
    assign protocol_uart_tx_ready = !tx_fifo_full;
    
    // Status register inputs
    assign status_inputs.tx_active = uart_tx_active;
    assign status_inputs.rx_active = uart_rx_active;
    assign status_inputs.tx_fifo_empty = tx_fifo_empty;
    assign status_inputs.rx_fifo_not_empty = !rx_fifo_empty;
    assign status_inputs.int_flag_error = error_int_flag;
    assign status_inputs.int_flag_rx_rdy = rx_ready_int_flag;
    assign status_inputs.int_flag_tx_done = tx_done_int_flag;
    assign status_inputs.int_flag_fifo_thr = fifo_thresh_int_flag;
    assign status_inputs.reserved_31_16 = '0;
    assign status_inputs.reserved_15_12 = '0;
    assign status_inputs.reserved_11_8 = '0;
    
    // FIFO status register inputs
    assign fifo_status.rx_fifo_count = rx_fifo_count;
    assign fifo_status.tx_fifo_count = tx_fifo_count;
    assign fifo_status.rx_fifo_full = rx_fifo_full;
    assign fifo_status.rx_fifo_empty = rx_fifo_empty;
    assign fifo_status.rx_fifo_nearly_full = rx_fifo_almost_full;
    assign fifo_status.rx_fifo_nearly_empty = rx_fifo_almost_empty;
    assign fifo_status.tx_fifo_full = tx_fifo_full;
    assign fifo_status.tx_fifo_empty = tx_fifo_empty;
    assign fifo_status.tx_fifo_nearly_full = tx_fifo_almost_full;
    assign fifo_status.tx_fifo_nearly_empty = tx_fifo_almost_empty;
    assign fifo_status.reserved_31_24 = '0;
    
    // Error status register inputs
    assign error_inputs.parity_error = uart_parity_error;
    assign error_inputs.frame_error = uart_frame_error;
    assign error_inputs.overrun_error = uart_overrun_error;
    assign error_inputs.any_error = uart_parity_error || uart_frame_error || uart_overrun_error;
    assign error_inputs.parity_count = '0;    // Error counters not implemented in this version
    assign error_inputs.frame_count = '0;
    assign error_inputs.overrun_count = '0;
    
    // Debug LED outputs
    assign debug_led[0] = uart_tx_active;     // TX Active
    assign debug_led[1] = uart_rx_active;     // RX Active
    assign debug_led[2] = error_inputs.any_error; // Error Status
    assign debug_led[3] = interrupt_out;      // Interrupt Status
    
    // RGB LED Debug Mapping for Protocol Handler State Observation
    // LED5 (R,G,B) = Protocol State[2:0] 
    Led_pwm led5 (
        .clk(clk),
        .rst(rst),
        .led_in(debug_protocol_state[2:0]),
        .pwm_out({led5_r, led5_g, led5_b})
    );
    
    // LED6 PWM control for status flags
    Led_pwm led6 (
        .clk(clk),
        .rst(rst),
        .led_in({debug_protocol_state[3], debug_cmd_valid, debug_protocol_error}),
        .pwm_out({led6_r, led6_g, led6_b})
    );
    
    // Note: uart_rts_n is managed by u_uart_controller
    // RX FIFO status is connected through rx_fifo_almost_full signal

endmodule
