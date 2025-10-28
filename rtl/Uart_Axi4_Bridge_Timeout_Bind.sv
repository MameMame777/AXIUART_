`timescale 1ns / 1ps

bind Uart_Axi4_Bridge Uart_Axi4_Bridge_Timeout_Assertions #(
    .FRAME_RESPONSE_TIMEOUT_CYCLES(1_250_000),
    .AXI_TRANSACTION_TIMEOUT_CYCLES(2_500_000),
    .BRIDGE_STALL_TIMEOUT_CYCLES(6_250_000)
) Uart_Axi4_Bridge_Timeout_Assertions_inst (
    .clk(clk),
    .rst(rst),
    .parser_frame_valid(parser_frame_valid),
    .parser_frame_error(parser_frame_error),
    .parser_frame_consumed(parser_frame_consumed),
    .bridge_busy(bridge_busy),
    .main_state(main_state),
    .axi_start_transaction(axi_start_transaction),
    .axi_transaction_done(axi_transaction_done),
    .builder_response_complete(builder_response_complete),
    .bridge_error_code(bridge_error_code)
);
