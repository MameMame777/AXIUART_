`timescale 1ns / 1ps

// DUT診断用SystemVerilogアサーション
// UART→AXI変換処理の各段階を監視し、処理停止箇所を特定
// 
// 作成日: 2025年10月12日
// 目的: Phase 3基盤退行の根本原因特定

module DUT_Diagnostic_Assertions (
    input logic clk,
    input logic rst,
    
    // UART信号監視
    input logic uart_rx,
    input logic uart_tx,
    
    // Frame Parser監視信号
    input logic [3:0] parser_state,
    input logic parser_frame_valid,
    input logic parser_frame_error,
    input logic [7:0] parser_cmd,
    input logic [31:0] parser_addr,
    input logic [5:0] parser_data_count,
    input logic parser_frame_consumed,
    input logic parser_busy,
    
    // Bridge状態監視信号
    input logic [3:0] bridge_state,
    input logic bridge_busy,
    input logic [7:0] bridge_error_code,
    
    // AXI Master監視信号
    input logic axi_awvalid,
    input logic axi_awready,
    input logic axi_wvalid,
    input logic axi_wready,
    input logic axi_bvalid,
    input logic axi_bready,
    input logic [31:0] axi_awaddr,
    input logic [31:0] axi_wdata,
    input logic [1:0] axi_bresp,
    
    // UART RX FIFO監視
    input logic rx_fifo_empty,
    input logic rx_fifo_rd_en,
    input logic [7:0] rx_fifo_data
);

    // Frame Parser状態定義 (Frame_Parser.svから)
    typedef enum logic [3:0] {
        IDLE        = 4'h0,
        CMD         = 4'h1,
        ADDR_BYTE0  = 4'h2,
        ADDR_BYTE1  = 4'h3,
        ADDR_BYTE2  = 4'h4,
        ADDR_BYTE3  = 4'h5,
        DATA_RX     = 4'h6,
        CRC_RX      = 4'h7,
        VALIDATE    = 4'h8,
        ERROR       = 4'h9
    } parser_state_t;
    
    // Bridge状態定義 (Uart_Axi4_Bridge.svから推定)
    typedef enum logic [3:0] {
        BRIDGE_IDLE             = 4'h0,
        BRIDGE_FRAME_WAIT       = 4'h1,
        BRIDGE_AXI_TRANSACTION  = 4'h2,
        BRIDGE_RESPONSE_BUILD   = 4'h3,
        BRIDGE_RESPONSE_SEND    = 4'h4,
        BRIDGE_ERROR_HANDLING   = 4'h5
    } bridge_state_t;
    
    // === UART受信フレーム検出アサーション ===
    
    // SOF (0xA5) 検出監視
    property uart_sof_detection;
        @(posedge clk) disable iff (rst)
        (!rx_fifo_empty && rx_fifo_rd_en && rx_fifo_data == 8'hA5 && parser_state == IDLE)
        |-> ##[1:10] (parser_state == CMD);
    endproperty
    
    assert property (uart_sof_detection) else
        $warning("ASSERTION FAIL: SOF検出後にCMD状態に遷移していない");
    
    cover property (uart_sof_detection);
    
    // フレーム受信完了監視 (8バイト受信)
    sequence frame_8_bytes_received;
        (!rx_fifo_empty && rx_fifo_rd_en && rx_fifo_data == 8'hA5 && parser_state == IDLE) ##1
        (parser_state == CMD) ##[1:20] 
        (parser_state == ADDR_BYTE0) ##[1:20]
        (parser_state == ADDR_BYTE1) ##[1:20]
        (parser_state == ADDR_BYTE2) ##[1:20]
        (parser_state == ADDR_BYTE3) ##[1:20]
        (parser_state == DATA_RX) ##[1:20]
        (parser_state == CRC_RX) ##[1:20]
        (parser_state == VALIDATE);
    endsequence
    
    property frame_complete_detection;
        @(posedge clk) disable iff (rst)
        frame_8_bytes_received |-> ##[1:5] parser_frame_valid;
    endproperty
    
    assert property (frame_complete_detection) else
        $error("ASSERTION FAIL: 8バイトフレーム受信完了後にframe_validが立たない");
    
    cover property (frame_complete_detection);
    
    // === Frame Parser動作監視アサーション ===
    
    // frame_valid生成後のBridge応答監視
    property bridge_responds_to_frame_valid;
        @(posedge clk) disable iff (rst)
        ($rose(parser_frame_valid) && !parser_frame_error)
        |-> ##[1:10] (bridge_state != BRIDGE_IDLE && bridge_state != BRIDGE_FRAME_WAIT);
    endproperty
    
    assert property (bridge_responds_to_frame_valid) else
        $error("ASSERTION FAIL: frame_valid検出後にBridgeが応答していない");
    
    cover property (bridge_responds_to_frame_valid);
    
    // frame_consumed信号生成監視
    property frame_consumption;
        @(posedge clk) disable iff (rst)
        (parser_frame_valid && !parser_frame_error && bridge_state == BRIDGE_AXI_TRANSACTION)
        |-> ##[1:10] parser_frame_consumed;
    endproperty
    
    assert property (frame_consumption) else
        $warning("ASSERTION FAIL: AXI_TRANSACTION状態でframe_consumedが生成されない");
    
    cover property (frame_consumption);
    
    // === AXI Master動作監視アサーション ===
    
    // Write取引開始監視 (CMD[7]=0の場合)
    property axi_write_initiation;
        @(posedge clk) disable iff (rst)
        (parser_frame_valid && !parser_frame_error && parser_cmd[7] == 1'b0 && bridge_state == BRIDGE_AXI_TRANSACTION)
        |-> ##[1:20] axi_awvalid;
    endproperty
    
    assert property (axi_write_initiation) else
        $error("ASSERTION FAIL: Write命令でAXI awvalidが立たない");
    
    cover property (axi_write_initiation);
    
    // Read取引開始監視 (CMD[7]=1の場合)  
    property axi_read_initiation;
        @(posedge clk) disable iff (rst)
        (parser_frame_valid && !parser_frame_error && parser_cmd[7] == 1'b1 && bridge_state == BRIDGE_AXI_TRANSACTION)
        |-> ##[1:20] (axi_awvalid); // Read操作でも最初はwrite address channelを使用する設計の場合
    endproperty
    
    assert property (axi_read_initiation) else
        $error("ASSERTION FAIL: Read命令でAXI取引が開始されない");
    
    cover property (axi_read_initiation);
    
    // AXI Write完了監視
    property axi_write_completion;
        @(posedge clk) disable iff (rst)
        (axi_awvalid && axi_awready) ##1 (axi_wvalid && axi_wready) 
        |-> ##[1:50] (axi_bvalid && axi_bready);
    endproperty
    
    assert property (axi_write_completion) else
        $warning("ASSERTION FAIL: AXI Write応答が完了していない");
    
    cover property (axi_write_completion);
    
    // === タイミング制約アサーション ===
    
    // Parser状態遷移時間制約
    property parser_state_transition_timeout;
        @(posedge clk) disable iff (rst)
        $changed(parser_state) |-> ##[1:1000] $changed(parser_state) or (parser_state == IDLE);
    endproperty
    
    assert property (parser_state_transition_timeout) else
        $error("ASSERTION FAIL: Parser状態遷移がタイムアウト");
    
    // Bridge応答時間制約
    property bridge_response_timeout;
        @(posedge clk) disable iff (rst)
        $rose(parser_frame_valid) |-> ##[1:2000] parser_frame_consumed or parser_frame_error;
    endproperty
    
    assert property (bridge_response_timeout) else
        $error("ASSERTION FAIL: Bridge応答がタイムアウト");
    
    // === デバッグ情報出力 ===
    
    // フレーム受信完了時の詳細出力
    always @(posedge clk) begin
        if (!rst && $rose(parser_frame_valid)) begin
            $display("ASSERTION DEBUG: Frame valid detected at %t", $time);
            $display("  CMD: 0x%02X, ADDR: 0x%08X, Data count: %d", parser_cmd, parser_addr, parser_data_count);
            $display("  Bridge state: %d, Bridge busy: %b", bridge_state, bridge_busy);
            $display("  AXI signals: awvalid=%b, awready=%b, wvalid=%b, wready=%b", 
                     axi_awvalid, axi_awready, axi_wvalid, axi_wready);
        end
    end
    
    // Bridge状態変化時の詳細出力  
    always @(posedge clk) begin
        if (!rst && $changed(bridge_state)) begin
            $display("ASSERTION DEBUG: Bridge state changed to %d at %t", bridge_state, $time);
            $display("  Parser: valid=%b, error=%b, consumed=%b, busy=%b", 
                     parser_frame_valid, parser_frame_error, parser_frame_consumed, parser_busy);
        end
    end
    
    // AXI取引開始時の詳細出力
    always @(posedge clk) begin
        if (!rst && $rose(axi_awvalid)) begin
            $display("ASSERTION DEBUG: AXI transaction started at %t", $time);
            $display("  Address: 0x%08X, Data: 0x%08X", axi_awaddr, axi_wdata);
        end
    end

endmodule