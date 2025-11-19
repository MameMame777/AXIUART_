# AXIUART UVM テストベンチ アーキテクチャ詳細

**作成日**: 2025年11月17日  
**対象DUT**: AXIUART_Top (UART-AXI4 Bridge System)  
**UVMバージョン**: UVM 1.2  
**シミュレータ**: Altair DSIM 2025.1.0

---

## 目次

1. [概要](#概要)
2. [アーキテクチャ全体図](#アーキテクチャ全体図)
3. [主要コンポーネント](#主要コンポーネント)
4. [階層構造](#階層構造)
5. [テストシナリオ](#テストシナリオ)
6. [検証戦略](#検証戦略)
7. [デバッグ機能](#デバッグ機能)

---

## 概要

### 目的
AXIUART UVMテストベンチは、UARTとAXI4-Liteインターフェース間のブリッジ機能を持つ`AXIUART_Top`システムの包括的な機能検証を提供します。

### 主要検証項目
- **UART Protocol**: フレーム構造、CRC検証、フロー制御
- **AXI4-Lite Protocol**: Write/Read transactions、タイムアウト、エラーハンドリング
- **Bridge Logic**: コマンド解析、レスポンス生成、FIFO管理
- **System Integration**: エンドツーエンド通信、複数トランザクション処理、カバレッジ収集

### 設計哲学
1. **階層的モジュラー設計**: 各コンポーネントは独立して再利用可能
2. **段階的検証**: 単純なテストから複雑なシナリオへ
3. **実践的デバッグ**: 豊富なログ、波形ダンプ、アサーションによる問題特定
4. **拡張性**: 新しいテストケース、シーケンス、カバレッジポイントを簡単に追加

---

## アーキテクチャ全体図

```
┌─────────────────────────────────────────────────────────────────────┐
│                       uart_axi4_tb_top.sv                           │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                        DUT: AXIUART_Top                        │ │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐       │ │
│  │  │  Uart_Rx/Tx  │  │ Frame_Parser │  │ Uart_Axi4_   │       │ │
│  │  │              │──│ Frame_Builder│──│    Bridge    │       │ │
│  │  └──────────────┘  └──────────────┘  └──────┬───────┘       │ │
│  │                                              │               │ │
│  │  ┌──────────────────────────────────────────▼──────────┐    │ │
│  │  │          Register_Block + Axi4_Lite_Master          │    │ │
│  │  └─────────────────────────────────────────────────────┘    │ │
│  └───────────────────────────────────────────────────────────────┘ │
│                                                                     │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                    UVM Environment                            │ │
│  │  ┌─────────────────────────────────────────────────────────┐ │ │
│  │  │              uart_axi4_env                              │ │ │
│  │  │  ┌────────────────┐  ┌────────────────┐               │ │ │
│  │  │  │  uart_agent    │  │ axi4_lite_     │               │ │ │
│  │  │  │  ┌──────────┐  │  │    monitor     │               │ │ │
│  │  │  │  │ Driver   │  │  └────────────────┘               │ │ │
│  │  │  │  │ Monitor  │  │                                    │ │ │
│  │  │  │  │ Sequencer│  │  ┌────────────────┐               │ │ │
│  │  │  │  └──────────┘  │  │  Scoreboard    │               │ │ │
│  │  │  └────────────────┘  │ (Correlation   │               │ │ │
│  │  │                      │    Engine)     │               │ │ │
│  │  │  ┌────────────────┐  └────────────────┘               │ │ │
│  │  │  │  Coverage      │                                    │ │ │
│  │  │  │  Collector     │  ┌────────────────┐               │ │ │
│  │  │  └────────────────┘  │ Bridge Status  │               │ │ │
│  │  │                      │    Monitor     │               │ │ │
│  │  │                      └────────────────┘               │ │ │
│  │  └─────────────────────────────────────────────────────────┘ │ │
│  └───────────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────────────┘
```

---

## 主要コンポーネント

### 1. テストベンチトップ (`uart_axi4_tb_top.sv`)

**役割**: DUTインスタンス化、クロック生成、リセット制御、インターフェース接続

**主要機能**:
```systemverilog
// Clock generation (125 MHz)
initial clk = 0;
always #4ns clk = ~clk;

// DUT instance
AXIUART_Top #(
    .CLK_FREQ_HZ(125_000_000),
    .BAUD_RATE(7_812_500),  // 8Mbaud default
    .RX_FIFO_DEPTH(64),
    .TX_FIFO_DEPTH(128),     // 増強済み
    .REG_BASE_ADDR(32'h0000_1000)
) dut (...);

// Interface instances
uart_if uart_if_inst(clk, rst);
bridge_status_if status_if(clk, rst_n);
```

**リセットシーケンス**:
- 初期: 100μs extended reset
- 安定化: 200ns stability period
- 動作: テスト実行開始

**波形ダンプ**:
```systemverilog
// MXD形式 (DSIM binary waveform)
$dumpfile("../archive/waveforms/uart_axi4_basic_test.mxd");
$dumpvars(0, dut);
$dumpvars(0, uart_if_inst);
```

---

### 2. UVM環境 (`uart_axi4_env.sv`)

**階層構成**:
```
uart_axi4_env
├── uart_agent
│   ├── uart_driver        (アクティブ時)
│   ├── uart_sequencer     (アクティブ時)
│   └── uart_monitor       (常時)
├── axi4_lite_monitor      (オプション)
├── uart_axi4_scoreboard   (Phase 3 Correlation Engine)
├── uart_axi4_coverage     (カバレッジ収集)
└── bridge_status_monitor  (システムステータス監視)
```

**Configuration Object** (`uart_axi4_env_config`):
```systemverilog
class uart_axi4_env_config extends uvm_object;
    // Timing parameters
    int clk_freq_hz = 125_000_000;
    int baud_rate = 7_812_500;
    int bit_time_ns;
    int byte_time_ns;
    
    // Feature enables
    bit enable_coverage = 1;
    bit enable_scoreboard = 1;
    bit enable_correlation = 1;
    bit enable_protocol_checking = 1;
    bit enable_axi_monitor = 1;
    
    // Debug controls
    bit enable_driver_runtime_logs = 1;
    bit enable_driver_debug_logs = 1;
    int driver_runtime_verbosity = UVM_MEDIUM;
    int driver_debug_verbosity = UVM_HIGH;
    
    // Timeout settings
    int frame_timeout_ns = 40960;
    int system_timeout_cycles = 1000;
    int axi_timeout_cycles = 1000;
    
    // Simulation watchdog
    bit enable_simulation_watchdog = 1;
    int simulation_timeout_multiplier = 4096;
    longint simulation_timeout_min_ns = 327680;
endclass
```

---

### 3. UART Agent (`uart_agent.sv`)

#### 3.1 UART Driver (`uart_driver.sv`)

**責務**: UVMシーケンスから受け取ったトランザクションを物理UART信号に変換して送信

**主要メソッド**:
```systemverilog
// メインドライブタスク
virtual task run_phase(uvm_phase phase);
    forever begin
        seq_item_port.get_next_item(req);
        drive_transaction(req);
        collect_response_from_fifo(req);
        seq_item_port.item_done();
    end
endtask

// UARTフレーム送信
task drive_frame(uart_frame_transaction req);
    drive_uart_byte(SOF);           // 0xA5
    drive_uart_byte(cmd);           // Command
    drive_uart_byte(addr[7:0]);     // Address[31:24]
    drive_uart_byte(addr[15:8]);    // Address[23:16]
    drive_uart_byte(addr[23:16]);   // Address[15:8]
    drive_uart_byte(addr[31:24]);   // Address[7:0]
    foreach (data[i])
        drive_uart_byte(data[i]);   // Data bytes
    drive_uart_byte(crc);           // CRC8
endtask

// ビット単位UART送信
task drive_uart_byte(logic [7:0] data);
    vif.uart_rx = 0;              // Start bit
    #(bit_time_ns * 1ns);
    for (int i = 0; i < 8; i++) begin
        vif.uart_rx = data[i];    // Data bits (LSB first)
        #(bit_time_ns * 1ns);
    end
    vif.uart_rx = 1;              // Stop bit
    #(bit_time_ns * 1ns);
endtask
```

**レスポンス収集**:
```systemverilog
// Monitorから受信したTXフレームを取得
task collect_response_from_fifo(uart_frame_transaction req);
    uart_frame_transaction resp;
    bit success;
    
    success = wait_for_monitor_response(
        .resp(resp),
        .timeout_ns(cfg.frame_timeout_ns),
        .poll_interval_ns(cfg.byte_time_ns)
    );
    
    if (!success)
        `uvm_error("UART_DRIVER", "Response timeout")
endtask
```

**デバッグ機能**:
- `UART_DRIVER_DEBUG`: VIF状態、クロック検証
- `UART_DRIVER_BYTE`: バイト送信詳細
- `UART_DRIVER_BYTE_STATE`: ビット単位遷移
- `UART_DRIVER_TIMING`: タイミング計算
- `UART_DRIVER_WAIT`: レスポンス待機状態

---

#### 3.2 UART Monitor (`uart_monitor.sv`)

**責務**: UART信号をサンプリングし、UVMトランザクションに変換

**RX監視** (DUT受信フレーム):
```systemverilog
task collect_rx_frames();
    forever begin
        @(negedge vif.uart_rx);  // SOF検出 (0xA5)
        
        // フレーム収集
        for (int i = 0; i < MAX_RX_FRAME_BYTES; i++) begin
            sample_uart_byte(rx_bytes[i]);
        end
        
        // フレーム解析
        parse_rx_frame(rx_bytes, trans);
        
        // 検証
        if (trans.crc_valid)
            analysis_port.write(trans);
        else
            `uvm_error("UART_MONITOR", "CRC mismatch")
    end
endtask
```

**TX監視** (DUT送信フレーム):
```systemverilog
task collect_tx_frames();
    forever begin
        @(posedge vif.uart_tx);  // TX開始検出
        
        // バイト収集
        for (int i = 0; i < expected_tx_bytes; i++) begin
            sample_tx_byte(tx_bytes[i]);
        end
        
        // レスポンス解析
        parse_tx_frame(tx_bytes, trans);
        
        // Driverへ通知 (FIFO経由)
        analysis_port.write(trans);
    end
endtask
```

**CRC検証**:
```systemverilog
function bit validate_crc(logic [7:0] frame_bytes[], logic [7:0] received_crc);
    logic [7:0] calculated_crc;
    calculated_crc = calculate_crc8(frame_bytes);
    return (calculated_crc == received_crc);
endfunction
```

---

### 4. AXI4-Lite Monitor (`axi4_lite_monitor.sv`)

**役割**: DUT内部のAXI4-Liteバスをパッシブ監視し、Write/Read transactionをキャプチャ

**Write Transaction監視**:
```systemverilog
task collect_write_transactions();
    forever begin
        @(posedge vif.clk);
        
        // AW channel (Address Write)
        if (vif.awvalid && vif.awready) begin
            axi_trans.addr = vif.awaddr;
            aw_captured = 1;
        end
        
        // W channel (Write Data)
        if (vif.wvalid && vif.wready) begin
            axi_trans.data = vif.wdata;
            w_captured = 1;
        end
        
        // B channel (Write Response)
        if (vif.bvalid && vif.bready) begin
            axi_trans.resp = vif.bresp;
            
            if (aw_captured && w_captured) begin
                analysis_port.write(axi_trans);
                aw_captured = 0;
                w_captured = 0;
            end
        end
    end
endtask
```

**Read Transaction監視**:
```systemverilog
task collect_read_transactions();
    forever begin
        @(posedge vif.clk);
        
        // AR channel (Address Read)
        if (vif.arvalid && vif.arready) begin
            axi_trans.addr = vif.araddr;
            ar_captured = 1;
        end
        
        // R channel (Read Data)
        if (vif.rvalid && vif.rready) begin
            axi_trans.data = vif.rdata;
            axi_trans.resp = vif.rresp;
            
            if (ar_captured) begin
                analysis_port.write(axi_trans);
                ar_captured = 0;
            end
        end
    end
endtask
```

---

### 5. Scoreboard (`uart_axi4_scoreboard.sv`)

**Phase 3 Correlation Engine**: UART transactionとAXI transactionの相関検証

**アーキテクチャ**:
```
┌──────────────────────────────────────────────────┐
│         Phase 3 Scoreboard Architecture          │
├──────────────────────────────────────────────────┤
│                                                  │
│  ┌────────────────┐      ┌────────────────┐    │
│  │ UART RX Queue  │      │ AXI TX Queue   │    │
│  │ (Commands)     │      │ (Responses)    │    │
│  └────────┬───────┘      └────────┬───────┘    │
│           │                       │            │
│           ▼                       ▼            │
│  ┌─────────────────────────────────────────┐   │
│  │      Correlation Engine                 │   │
│  │  - Command/Response matching            │   │
│  │  - Timing verification                  │   │
│  │  - Data integrity check                 │   │
│  └─────────────────┬───────────────────────┘   │
│                    │                            │
│                    ▼                            │
│  ┌─────────────────────────────────────────┐   │
│  │      Match/Mismatch Report              │   │
│  │  ✓ Exact matches                        │   │
│  │  ✗ Data mismatches                      │   │
│  │  ⚠ Timeout/protocol errors              │   │
│  └─────────────────────────────────────────┘   │
└──────────────────────────────────────────────────┘
```

**比較ロジック**:
```systemverilog
function void compare_transactions(
    uart_frame_transaction uart_trans,
    axi4_lite_transaction axi_trans
);
    bit match = 1;
    
    // Address match
    if (uart_trans.address !== axi_trans.addr) begin
        `uvm_error("SCOREBOARD", 
            $sformatf("Address mismatch: UART=0x%08h AXI=0x%08h",
                     uart_trans.address, axi_trans.addr))
        match = 0;
    end
    
    // Data match (Write transaction)
    if (uart_trans.cmd == CMD_WRITE) begin
        if (uart_trans.data[0] !== axi_trans.data[7:0]) begin
            `uvm_error("SCOREBOARD",
                $sformatf("Data mismatch: UART=0x%02h AXI=0x%08h",
                         uart_trans.data[0], axi_trans.data))
            match = 0;
        end
    end
    
    if (match) begin
        match_count++;
        `uvm_info("SCOREBOARD", "Transaction matched", UVM_MEDIUM)
    end else begin
        mismatch_count++;
    end
endfunction
```

**最終レポート**:
```systemverilog
function void report_phase(uvm_phase phase);
    `uvm_info("SCOREBOARD", "=== FINAL REPORT ===", UVM_LOW)
    `uvm_info("SCOREBOARD", 
        $sformatf("UART transactions: %0d", uart_trans_count), UVM_LOW)
    `uvm_info("SCOREBOARD",
        $sformatf("AXI transactions: %0d", axi_trans_count), UVM_LOW)
    `uvm_info("SCOREBOARD",
        $sformatf("Matches: %0d", match_count), UVM_LOW)
    `uvm_info("SCOREBOARD",
        $sformatf("Mismatches: %0d", mismatch_count), UVM_LOW)
    
    if (mismatch_count > 0)
        `uvm_error("SCOREBOARD", "Test FAILED: Mismatches detected")
    else if (match_count > 0)
        `uvm_info("SCOREBOARD", "PERFECT: All transactions matched", UVM_LOW)
endfunction
```

---

### 6. Coverage Collector (`uart_axi4_coverage.sv`)

**カバレッジ項目**:

```systemverilog
covergroup frame_coverage;
    // Command coverage
    cp_command: coverpoint trans.cmd {
        bins write = {CMD_WRITE};
        bins read  = {CMD_READ};
        bins config = {CMD_CONFIG};
        bins metadata = {CMD_METADATA};
    }
    
    // Address coverage
    cp_address: coverpoint trans.address {
        bins control_reg  = {32'h0000_1000};
        bins status_reg   = {32'h0000_1004};
        bins data_reg     = {32'h0000_1008};
        bins metadata_reg = {32'h0000_100C};
        bins other_regs[] = {[32'h0000_1010:32'h0000_1FFF]};
    }
    
    // Data pattern coverage
    cp_data_pattern: coverpoint trans.data[0] {
        bins zero      = {8'h00};
        bins all_ones  = {8'hFF};
        bins alternating_01 = {8'h55};
        bins alternating_10 = {8'hAA};
        bins random[]  = {[8'h01:8'hFE]};
    }
    
    // Cross coverage
    cx_cmd_addr: cross cp_command, cp_address;
endgroup

covergroup burst_coverage;
    cp_burst_length: coverpoint burst_length {
        bins single   = {1};
        bins short[]  = {[2:4]};
        bins medium[] = {[5:8]};
        bins long[]   = {[9:16]};
    }
    
    cp_inter_frame_gap: coverpoint inter_frame_gap {
        bins tight  = {[0:100]};      // ns
        bins normal = {[101:1000]};
        bins loose  = {[1001:10000]};
    }
endgroup
```

**カバレッジ閾値**:
- Frame coverage: ≥80%
- Burst coverage: ≥70%
- Error coverage: ≥50%
- **Total coverage target: ≥80%**

---

## 階層構造

### ディレクトリ構成
```
sim/uvm/
├── agents/
│   ├── uart/
│   │   ├── uart_agent.sv
│   │   ├── uart_driver.sv
│   │   ├── uart_monitor.sv
│   │   └── uart_sequencer.sv
│   └── axi4_lite/
│       ├── axi4_lite_monitor.sv
│       └── axi4_lite_transaction.sv
├── env/
│   ├── uart_axi4_env.sv
│   ├── uart_axi4_env_config.sv
│   ├── uart_axi4_scoreboard.sv
│   ├── uart_axi4_coverage.sv
│   └── uart_axi4_correlation_engine.sv
├── tests/
│   ├── uart_axi4_base_test.sv
│   ├── enhanced_uart_axi4_base_test.sv
│   ├── uart_axi4_basic_test.sv
│   ├── uart_axi4_basic_115200_test.sv
│   ├── uart_axi4_comprehensive_test.sv
│   └── ... (60+ test variants)
├── sequences/
│   ├── basic_func_sequence.sv
│   ├── simple_debug_write_sequence_20250923.sv
│   ├── performance_test_sequence.sv
│   └── error_injection_sequence.sv
├── interfaces/
│   ├── uart_if.sv
│   ├── axi4_lite_if.sv
│   └── bridge_status_if.sv
├── assertions/
│   ├── Frame_Parser_Assertions.sv
│   ├── Frame_Parser_CRC_Status_Assertions.sv
│   └── Uart_Axi4_Bridge_Timeout_Assertions.sv
├── tb/
│   └── uart_axi4_tb_top.sv
└── packages/
    └── uart_axi4_test_pkg.sv
```

---

## テストシナリオ

### 1. Basic Test (`uart_axi4_basic_test`)

**目的**: 基本的な単一Write transaction検証

**シーケンス**:
```systemverilog
virtual task run_phase(uvm_phase phase);
    simple_debug_write_sequence_20250923 seq;
    
    phase.raise_objection(this);
    
    // Reset完了待機
    wait_for_reset_completion();
    
    // 単一Write transaction
    seq = simple_debug_write_sequence_20250923::type_id::create("seq");
    seq.start(env.uart_agt.sequencer);
    
    // 完了確認
    wait_for_completion();
    
    phase.drop_objection(this);
endtask
```

**期待結果**:
- ✓ UART RX frame正常受信
- ✓ AXI Write transaction発行
- ✓ UART TX response返信
- ✓ Scoreboard match確認
- ✓ UVM_ERROR = 0

---

### 2. Baud Rate Change Test (`uart_axi4_basic_115200_test`)

**目的**: 実行時ボーレート変更機能検証

**フェーズ構成**:
```systemverilog
// Phase 1: CONFIG write (8Mbaud → 921.6kbaud)
seq_phase1 = simple_debug_write_sequence_20250923::type_id::create("seq_phase1");
seq_phase1.cmd = CMD_CONFIG;
seq_phase1.address = 32'h0000_1000;  // CONTROL register
seq_phase1.data[0] = 8'h88;          // Divisor for 921600 baud
seq_phase1.start(env.uart_agt.sequencer);

// Phase 2: 遅延 (baud switch安定化)
#(cfg.byte_time_ns * 4 * 1ns);

// Phase 3: Write transaction (921.6kbaud)
cfg.baud_rate = 921_600;
cfg.bit_time_ns = 1_000_000_000 / cfg.baud_rate;
seq_phase3 = simple_debug_write_sequence_20250923::type_id::create("seq_phase3");
seq_phase3.cmd = CMD_WRITE;
seq_phase3.address = 32'h0000_2000;
seq_phase3.data[0] = 8'h55;
seq_phase3.start(env.uart_agt.sequencer);
```

**既知の問題**:
- ⚠ CONFIG応答フレームが不正 (0x00バイト、parse error)
- ⚠ タイムアウト発生 (60秒)
- 🔍 調査中: Frame_Builder/Uart_Axi4_Bridgeのタイミング問題疑い

---

### 3. Comprehensive Test

**カバレッジ項目**:
- Multiple command types (WRITE, READ, CONFIG, METADATA)
- Address space sweep
- Burst transactions (1-16 frames)
- Error injection (CRC error, timeout, protocol violation)
- Flow control stress (RTS/CTS)

---

## 検証戦略

### レイヤー構造
```
┌─────────────────────────────────────────┐
│ Layer 4: System Integration Tests      │  ← Comprehensive, Multi-scenario
├─────────────────────────────────────────┤
│ Layer 3: Protocol Compliance Tests     │  ← Baud change, Flow control
├─────────────────────────────────────────┤
│ Layer 2: Functional Tests               │  ← Write/Read, Error handling
├─────────────────────────────────────────┤
│ Layer 1: Sanity Tests                   │  ← Basic connectivity
└─────────────────────────────────────────┘
```

### 段階的検証アプローチ

**Stage 1: Sanity (基本動作)**
- `uart_axi4_basic_test`: 単一Write
- `uart_axi4_simple_write_test`: 複数Write

**Stage 2: Functional (機能検証)**
- `uart_axi4_read_protocol_test`: Read transaction
- `uart_axi4_write_protocol_test`: Write variations
- `uart_axi4_error_paths_test`: Error handling

**Stage 3: Protocol (プロトコル準拠)**
- `uart_axi4_basic_115200_test`: Baud change
- `uart_flow_control_tests`: RTS/CTS
- `uart_axi4_burst_perf_test`: Burst performance

**Stage 4: Integration (統合)**
- `uart_axi4_comprehensive_test`: Full coverage
- `axiuart_system_test`: End-to-end scenarios

---

## デバッグ機能

### 1. Verbosity Control

**UVMメッセージレベル**:
```systemverilog
// Global verbosity
uvm_top.set_report_verbosity_level_hier(UVM_MEDIUM);

// Component-specific
cfg.driver_runtime_verbosity = UVM_MEDIUM;
cfg.driver_debug_verbosity = UVM_HIGH;
cfg.scoreboard_runtime_verbosity = UVM_LOW;
```

**Plusargs**:
```bash
+UVM_VERBOSITY=UVM_HIGH          # グローバル
+UART_BASIC_VERBOSE              # Test-specific debug
```

---

### 2. Waveform Dumping

**MXD形式** (DSIM Binary):
```systemverilog
$dumpfile("../archive/waveforms/uart_axi4_basic_test.mxd");
$dumpvars(0, dut);                    // DUT階層全体
$dumpvars(0, uart_if_inst);           // UART interface
```

**VCD形式** (Text):
```systemverilog
+WAVE_FORMAT=VCD                 # Plusarg for VCD
```

---

### 3. Assertions

**Frame_Parser_Assertions**:
```systemverilog
// SOF検出確認
sva_sof_detected: assert property (
    @(posedge clk) disable iff (!rst_n)
    (rx_valid && rx_data == 8'hA5) |-> ##1 (state == CMD)
);

// CRC検証確認
sva_crc_valid: assert property (
    @(posedge clk) disable iff (!rst_n)
    (frame_valid && crc_ok) |-> (error_status == 8'h00)
);
```

**Uart_Axi4_Bridge_Timeout_Assertions**:
```systemverilog
// AXIタイムアウト検出
sva_axi_timeout: assert property (
    @(posedge clk) disable iff (!rst_n)
    (axi_state == AXI_WRITE_WAIT) |->
    ##[1:AXI_TIMEOUT_CYCLES] (axi_done || axi_timeout)
);
```

---

### 4. Logging Strategy

**Driver logs**:
```
[UART_DRIVER]           : High-level transaction info
[UART_DRIVER_DEBUG]     : VIF state, clock verification
[UART_DRIVER_BYTE]      : Byte-level transmission
[UART_DRIVER_BYTE_STATE]: Bit-level state machine
[UART_DRIVER_TIMING]    : Timing calculations
[UART_DRIVER_WAIT]      : Response wait status
```

**Monitor logs**:
```
[UART_MONITOR]          : Frame collection
[UART_MONITOR_TX]       : TX byte sampling
[UART_MONITOR_FIFO]     : FIFO operations
[UART_MONITOR_DBG]      : Debug traces
```

**Scoreboard logs**:
```
[SCOREBOARD]            : Match/mismatch results
[SCOREBOARD_CORRELATION]: Correlation engine details
```

---

### 5. MCP Server Integration

**ツール経由実行**:
```bash
# 環境確認
python mcp_server/mcp_client.py --workspace $PWD \
    --tool check_dsim_environment

# テスト一覧
python mcp_server/mcp_client.py --workspace $PWD \
    --tool list_available_tests

# コンパイルのみ
python mcp_server/mcp_client.py --workspace $PWD \
    --tool run_uvm_simulation \
    --test-name uart_axi4_basic_test \
    --mode compile --verbosity UVM_LOW --timeout 120

# 実行 (波形あり)
python mcp_server/mcp_client.py --workspace $PWD \
    --tool run_uvm_simulation \
    --test-name uart_axi4_basic_test \
    --mode run --verbosity UVM_MEDIUM \
    --waves --timeout 180
```

**バッチ実行**:
```bash
# Compile + Run 一括実行
python mcp_server/mcp_client.py --workspace $PWD \
    --tool run_uvm_simulation_batch \
    --test-name uart_axi4_basic_test \
    --verbosity UVM_MEDIUM --waves \
    --compile-timeout 120 --run-timeout 180
```

---

## 付録

### A. プロトコル定義

**UARTフレーム構造**:
```
┌────┬────┬────────┬────────┬────────┬────────┬─────┬────┐
│SOF │CMD │ADDR[31]│ADDR[23]│ADDR[15]│ADDR[7] │DATA │CRC │
│0xA5│    │  :24]  │  :16]  │   :8]  │   :0]  │     │    │
└────┴────┴────────┴────────┴────────┴────────┴─────┴────┘
 1B   1B     1B       1B       1B       1B     0-16B  1B
```

**Commands**:
- `0x00` = WRITE
- `0x01` = READ
- `0x02` = CONFIG (baud rate change)
- `0x03` = METADATA

**Response Frame**:
```
┌────┬────────┬────────┬────┐
│SOF │ STATUS │CMD_ECHO│CRC │
│0x5A│        │        │    │
└────┴────────┴────────┴────┘
 1B     1B       1B      1B
```

---

### B. タイミングパラメータ

**8Mbaud (デフォルト)**:
- Bit time: 125 ns
- Byte time: 1250 ns (10 bits with start/stop)
- Frame time (8 bytes): ~10 μs

**921.6kbaud**:
- Bit time: 1085 ns
- Byte time: 10850 ns
- Frame time (8 bytes): ~87 μs

**115.2kbaud**:
- Bit time: 8680 ns
- Byte time: 86800 ns
- Frame time (8 bytes): ~694 μs

---

### C. リソース配置

**Logs**: `sim/exec/logs/`
```
uart_axi4_basic_test_20251117_194259.log    # Compile
uart_axi4_basic_test_20251117_194318.log    # Run
```

**Waveforms**: `archive/waveforms/`
```
uart_axi4_basic_test_20251117_194318.mxd    # Binary waveform
```

**Coverage**: `sim/uvm/metrics.db`
- DSIM coverage database (binary format)

---

## まとめ

本UVMテストベンチは以下の特徴を持ちます:

✅ **包括的検証**: UART、AXI4-Lite、ブリッジロジックの全レイヤー  
✅ **段階的アプローチ**: Sanity → Functional → Protocol → Integration  
✅ **強力なデバッグ**: Verbosity制御、波形、アサーション、詳細ログ  
✅ **自動化対応**: MCP Server経由のコマンドライン実行  
✅ **拡張性**: 新しいテスト、シーケンス、カバレッジポイントを容易に追加可能  

**現在の課題**:
- 🔍 `uart_axi4_basic_115200_test`: CONFIG応答フレーム不正問題の調査中
- 📊 カバレッジ向上: 現在33.79% → 目標80%

**次のステップ**:
1. RTLタイミング問題の特定 (Frame_Builder/Uart_Axi4_Bridge)
2. 波形トレース詳細解析
3. カバレッジギャップの特定と追加テストケース作成

---

**ドキュメント管理**:
- **最終更新**: 2025年11月17日
- **バージョン**: 1.0
- **レビュアー**: (記入欄)
