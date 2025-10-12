`timescale 1ns / 1ps

// Emergency UART-AXI Bridge Diagnostic Assertions
// Monitors critical paths for Phase 3 regression analysis
module emergency_uart_axi_assertions;

    // Access internal signals from DUT
    wire clk = uart_axi4_tb_top.dut.clk;
    wire rst = uart_axi4_tb_top.dut.rst;
    
    // Frame Parser signals
    wire parser_frame_valid = uart_axi4_tb_top.dut.uart_bridge_inst.frame_parser.frame_valid;
    wire parser_frame_error = uart_axi4_tb_top.dut.uart_bridge_inst.frame_parser.frame_error;
    wire [3:0] parser_state = uart_axi4_tb_top.dut.uart_bridge_inst.frame_parser.state;
    wire [7:0] parser_cmd = uart_axi4_tb_top.dut.uart_bridge_inst.frame_parser.cmd;
    wire [31:0] parser_addr = uart_axi4_tb_top.dut.uart_bridge_inst.frame_parser.addr;
    wire parser_busy = uart_axi4_tb_top.dut.uart_bridge_inst.frame_parser.parser_busy;
    
    // Bridge state machine signals
    wire [3:0] bridge_state = uart_axi4_tb_top.dut.uart_bridge_inst.main_state;
    wire axi_start_transaction = uart_axi4_tb_top.dut.uart_bridge_inst.axi_start_transaction;
    wire axi_transaction_done = uart_axi4_tb_top.dut.uart_bridge_inst.axi_transaction_done;
    wire parser_frame_consumed = uart_axi4_tb_top.dut.uart_bridge_inst.parser_frame_consumed;
    
    // AXI interface signals
    wire axi_awvalid = uart_axi4_tb_top.dut.axi_internal.awvalid;
    wire axi_awready = uart_axi4_tb_top.dut.axi_internal.awready;
    wire axi_wvalid = uart_axi4_tb_top.dut.axi_internal.wvalid;
    wire axi_wready = uart_axi4_tb_top.dut.axi_internal.wready;
    wire axi_bvalid = uart_axi4_tb_top.dut.axi_internal.bvalid;
    wire axi_bready = uart_axi4_tb_top.dut.axi_internal.bready;
    wire [31:0] axi_awaddr = uart_axi4_tb_top.dut.axi_internal.awaddr;
    
    // UART receive signals
    wire [7:0] rx_data = uart_axi4_tb_top.dut.uart_bridge_inst.rx_data;
    wire rx_valid = uart_axi4_tb_top.dut.uart_bridge_inst.rx_valid;
    wire rx_fifo_empty = uart_axi4_tb_top.dut.uart_bridge_inst.rx_fifo_empty;
    wire rx_fifo_rd_en = uart_axi4_tb_top.dut.uart_bridge_inst.rx_fifo_rd_en;

    // Critical Path Assertion 1: Frame parser must process received UART data
    property uart_frame_processing;
        @(posedge clk) disable iff (rst)
        (rx_valid && !rx_fifo_empty) |-> ##[1:1000] parser_busy;
    endproperty
    
    assert property (uart_frame_processing) else 
        $error("[ASSERTION FAIL] Frame parser not processing UART data - CRITICAL PATH BROKEN");
    
    // Critical Path Assertion 2: Parser must reach VALIDATE state for complete frame
    property parser_reaches_validate;
        @(posedge clk) disable iff (rst)
        $rose(parser_busy) |-> ##[1:10000] (parser_state == 4'd8); // VALIDATE state = 8
    endproperty
    
    assert property (parser_reaches_validate) else
        $error("[ASSERTION FAIL] Parser never reaches VALIDATE state - FRAME PROCESSING FAILED");
    
    // Critical Path Assertion 3: Frame_valid must be asserted for successful frame
    property frame_valid_generation;
        @(posedge clk) disable iff (rst)
        (parser_state == 4'd8) && !parser_frame_error |-> ##[0:10] parser_frame_valid;
    endproperty
    
    assert property (frame_valid_generation) else
        $error("[ASSERTION FAIL] frame_valid not generated after successful VALIDATE - PARSER OUTPUT FAILED");
    
    // Critical Path Assertion 4: Bridge must respond to frame_valid
    property bridge_responds_to_frame_valid;
        @(posedge clk) disable iff (rst)
        $rose(parser_frame_valid) |-> ##[1:100] (bridge_state == 4'd1); // MAIN_AXI_TRANSACTION = 1
    endproperty
    
    assert property (bridge_responds_to_frame_valid) else
        $error("[ASSERTION FAIL] Bridge not responding to frame_valid - BRIDGE STATE MACHINE FAILED");
    
    // Critical Path Assertion 5: AXI transaction must start
    property axi_transaction_starts;
        @(posedge clk) disable iff (rst)
        (bridge_state == 4'd1) |-> ##[1:50] axi_start_transaction;
    endproperty
    
    assert property (axi_transaction_starts) else
        $error("[ASSERTION FAIL] AXI transaction not starting - AXI MASTER INTERFACE FAILED");
    
    // Critical Path Assertion 6: AXI signals must be driven
    property axi_signals_driven;
        @(posedge clk) disable iff (rst)
        axi_start_transaction |-> ##[1:20] axi_awvalid;
    endproperty
    
    assert property (axi_signals_driven) else
        $error("[ASSERTION FAIL] AXI AWVALID not asserted - AXI SIGNAL GENERATION FAILED");
    
    // Progress Monitor: Track overall system progression
    sequence uart_to_axi_complete_sequence;
        (rx_valid && !rx_fifo_empty) ##[1:1000] parser_frame_valid ##[1:100] axi_awvalid;
    endsequence
    
    property uart_to_axi_complete_property;
        @(posedge clk) disable iff (rst)
        uart_to_axi_complete_sequence;
    endproperty
    
    assert property (uart_to_axi_complete_property) else
        $error("[ASSERTION FAIL] COMPLETE UART->AXI CONVERSION FAILED - SYSTEM LEVEL FAILURE");
    
    // Coverage for successful paths
    cover property (@(posedge clk) disable iff (rst) parser_frame_valid);
    cover property (@(posedge clk) disable iff (rst) axi_awvalid);
    cover property (@(posedge clk) disable iff (rst) uart_to_axi_complete_sequence);
    
    // Timeout detection
    property no_infinite_parser_busy;
        @(posedge clk) disable iff (rst)
        $rose(parser_busy) |-> ##[1:50000] !parser_busy;
    endproperty
    
    assert property (no_infinite_parser_busy) else
        $error("[ASSERTION FAIL] Parser stuck in busy state - INFINITE LOOP DETECTED");

endmodule