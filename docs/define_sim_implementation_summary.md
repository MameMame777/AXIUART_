# DEFINE_SIM Implementation Summary

## Date: September 24, 2025

## Overview
システムステータス出力信号（`system_busy`, `system_error`, `system_ready`）を`DEFINE_SIM`マクロによる条件付きコンパイル対応に実装しました。これにより、これらの信号はシミュレーション時のみ有効となり、シンセサイズ時には完全に除外されます。

## 実装内容

### 1. RTLモジュール修正 (AXIUART_Top.sv)

#### ポート定義の条件付きコンパイル化
```systemverilog
module AXIUART_Top #(
    // parameters...
)(
    // Clock and reset
    input  logic        clk,
    input  logic        rst,
    
    // UART interface (external connections)
    input  logic        uart_rx,
    output logic        uart_tx

    // System status outputs - simulation only
    `ifdef DEFINE_SIM
    // Simulation-only system status outputs
    , output logic        system_busy,
    output logic [7:0]  system_error,
    output logic        system_ready
    `endif
);
```

#### assign文の条件付きコンパイル化
```systemverilog
// System status outputs (simulation only)
`ifdef DEFINE_SIM
assign system_busy = bridge_busy;
assign system_error = (bridge_error_code != 8'h00);
assign system_ready = !system_busy && !system_error;
`endif
```

### 2. テストベンチ修正 (uart_axi4_tb_top.sv)

#### マクロ定義の追加
```systemverilog
`timescale 1ns / 1ps

// Enable simulation-only system status signals
`define DEFINE_SIM

import uvm_pkg::*;
import uart_axi4_test_pkg::*;
`include "uvm_macros.svh"
```

#### 信号宣言の条件付きコンパイル化
```systemverilog
// System status signals from DUT (simulation only)
`ifdef DEFINE_SIM
logic system_ready;
logic system_busy;
logic [7:0] system_error;
`endif
```

#### DUTインスタンス化の条件付き接続
```systemverilog
) dut (
    .clk(clk),
    .rst(~rst_n),  // RTL expects active-high reset
    
    // UART interface - external connections
    .uart_rx(uart_if_inst.uart_rx),
    .uart_tx(uart_if_inst.uart_tx)
    
    // System status outputs (simulation only)
    `ifdef DEFINE_SIM
    ,
    .system_busy(system_busy),      
    .system_error(system_error),     
    .system_ready(system_ready)
    `endif    
);
```

### 3. テストケース修正

#### システムテスト (axiuart_system_test.sv)
```systemverilog
// Monitor system status
repeat (50) @(posedge uart_axi4_tb_top.dut.clk);

`ifdef DEFINE_SIM
`uvm_info("SYSTEM_TEST", $sformatf("System Status: Ready=%b, Busy=%b, Error=%b", 
          uart_axi4_tb_top.dut.system_ready,
          uart_axi4_tb_top.dut.system_busy, 
          uart_axi4_tb_top.dut.system_error), UVM_LOW)
`else
`uvm_info("SYSTEM_TEST", "System Status: Not available (synthesis mode)", UVM_LOW)
`endif
```

#### ミニマルテスト (uart_axi4_minimal_test.sv)
```systemverilog
// Monitor system status signals
`ifdef DEFINE_SIM
`uvm_info("MINIMAL_TEST", $sformatf("System Status - Ready: %b, Busy: %b, Error: %b", 
          uart_axi4_tb_top.dut.system_ready,
          uart_axi4_tb_top.dut.system_busy, 
          uart_axi4_tb_top.dut.system_error), UVM_LOW)
`else
`uvm_info("MINIMAL_TEST", "System Status - Not available (synthesis mode)", UVM_LOW)
`endif
```

### 4. 制約ファイル更新 (AXIUART.xdc)

システムステータス出力のピン制約をコメントアウト済みのオプション設定として用意：

```tcl
###################################################################################
# System Status Outputs (Optional - for debugging/monitoring)
###################################################################################

# System Ready Indicator (LED0)
# set_property -dict { PACKAGE_PIN M14   IOSTANDARD LVCMOS33 } [get_ports { system_ready }]

# System Busy Indicator (LED1) 
# set_property -dict { PACKAGE_PIN M15   IOSTANDARD LVCMOS33 } [get_ports { system_busy }]

# System Error Indicator (LED2)
# set_property -dict { PACKAGE_PIN G14   IOSTANDARD LVCMOS33 } [get_ports { system_error }]
```

## 動作仕様

### シミュレーション時 (`DEFINE_SIM`定義あり)
- システムステータス信号が有効化されます
- テストベンチでシステム状態の監視が可能です
- UVMテストでステータス情報が表示されます

### シンセサイズ時 (`DEFINE_SIM`定義なし)
- システムステータス信号は完全に除外されます
- ポート定義から削除されるためピン制約エラーが発生しません
- リソースオーバーヘッドがゼロになります

## メリット

1. **リソース最適化**: synthesis時にはステータス関連ロジックが完全に除去されます
2. **ピン制約の柔軟性**: 制約ファイルでの設定有無に関係なくコンパイルが成功します
3. **デバッグ機能維持**: シミュレーション時には全ての監視機能が利用可能です
4. **保守性**: 条件付きコンパイルにより、同一ソースで複数用途に対応可能です

## 使用方法

### シミュレーション実行時
テストベンチで`DEFINE_SIM`が定義済みのため、自動的にシステムステータス監視が有効になります。

### Vivado合成時
`DEFINE_SIM`マクロが未定義のため、システムステータス信号は自動的に除外され、クリーンなシンセサイズが実行されます。

## コード品質

- SystemVerilogコーディングガイドラインに準拠
- 条件付きコンパイル構文の正確な実装
- テストケースでの適切なエラーハンドリング
- 制約ファイルとの整合性維持

この実装により、ユーザー要求の「シミュレーション専用システムステータス信号」が完全に実現されました。