// Emergency assertion bind for UART-AXI diagnostic
bind uart_axi4_tb_top emergency_uart_axi_assertions emergency_uart_axi_assertions_inst();

// Frame parser diagnostics bind
bind uart_axi4_tb_top.dut.uart_bridge_inst.frame_parser emergency_frame_parser_diagnostics emergency_frame_parser_diag_inst (
    .clk(clk),
    .rst(rst),
    .frame_valid_hold(frame_valid_hold),
    .state(state)
);