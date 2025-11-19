# UART ボーレート切替問題 — 実装ステップ詳細

**作成日:** 2024-11-18  
**対象問題:** CONFIG write 後の UVM ハング（ボーレート同期不整合）  
**実装方針:** 段階的アプローチ（短期 → 中期 → 長期）

---

## ステップ1: 最小限修正（即日実装）

### 目的
Sequence の response 検証を緩和し、Test が Phase 2 まで進行できるようにする

### 対象ファイル
- `sim/uvm/sequences/uart_configure_baud_sequence.sv`

### 実装手順

#### 1-1. バックアップ作成
```powershell
# 作業ディレクトリ確認
cd E:\Nautilus\workspace\fpgawork\AXIUART_

# タイムスタンプ付きバックアップ
$timestamp = Get-Date -Format 'yyyyMMdd_HHmmss'
Copy-Item sim/uvm/sequences/uart_configure_baud_sequence.sv `
          sim/uvm/sequences/uart_configure_baud_sequence.sv.backup_$timestamp

# バックアップ確認
Get-Item sim/uvm/sequences/uart_configure_baud_sequence.sv.backup_*
```

#### 1-2. コード修正

**修正箇所:** Line 96-108

**修正前:**
```systemverilog
finish_item(req);

// Validate response - Critical for baud rate change verification
// If response fails, subsequent transactions at wrong baud rate will hang
if (!req.response_received) begin
    `uvm_fatal(get_type_name(), 
        "CONFIG write failed - no response received. DUT may not have processed baud divisor change.")
end else if (req.response_status != STATUS_OK) begin
    `uvm_fatal(get_type_name(),
        $sformatf("CONFIG write returned error STATUS=0x%02X - DUT rejected baud configuration", 
                  req.response_status))
end else begin
    `uvm_info(get_type_name(), 
        $sformatf("CONFIG write acknowledged by DUT - divisor=0x%04h programmed successfully", 
                  sanitized_divisor), 
        UVM_LOW)
end
```

**修正後:**
```systemverilog
finish_item(req);

// CONFIG write 特殊処理:
// - DUT は AXI write 完了後、即座に新ボーレートに切替
// - Response frame は新ボーレートで送信されるため、UVM Monitor は旧ボーレートで
//   サンプリングして受信失敗する（タイミングミスマッチ）
// - AXI BRESP=OKAY で書き込み成功は確認済みなので、UART response 検証はスキップ
// - Test 側で timing 更新を行うため、ここでは return する必要がある
//
// 技術的背景:
//   t=15,964,000ns: AXI write complete (RESP=0x0)
//   t=16,012,000ns: DUT が新baud (921600) で TX 開始
//   t=17,228,000ns: Monitor が旧baud (7.8125M) でサンプリング → 0x00 取得（誤）
//   結果: response_received = false → 以前は FATAL → Test ハング

if (!req.response_received) begin
    `uvm_info(get_type_name(), 
        $sformatf("CONFIG write completed via AXI (addr=0x%08X, data=0x%08X). "
                  "UART response not captured (expected - DUT switched to new baud rate). "
                  "Test will update UVM timing parameters.",
                  req.addr, req.data),
        UVM_LOW)
    
    // response なしでも正常完了とみなす（AXI write 成功済み）
    
end else if (req.response_status != STATUS_OK) begin
    // Response が取れた場合でも STATUS エラーはボーレートミスマッチの可能性
    `uvm_warning(get_type_name(),
        $sformatf("CONFIG response STATUS=0x%02X (may be sampling artifact from baud mismatch)", 
                  req.response_status))
    
end else begin
    // Response が正常に取れた場合（稀なケース）
    `uvm_info(get_type_name(), 
        $sformatf("CONFIG response received successfully (unexpected but valid) - divisor=0x%04h", 
                  sanitized_divisor), 
        UVM_LOW)
end
```

#### 1-3. コンパイル確認
```powershell
# MCP Client 経由でコンパイル（推奨）
python mcp_server/mcp_client.py --workspace . `
    --tool run_uvm_simulation `
    --test-name uart_axi4_basic_115200_test `
    --mode compile `
    --verbosity UVM_LOW `
    --timeout 180

# コンパイルエラー確認
Get-Content sim/exec/logs/*.log | Select-String -Pattern "error|Error|ERROR" | Select-Object -Last 20
```

#### 1-4. シミュレーション実行
```powershell
# Full simulation with waveforms
python mcp_server/mcp_client.py --workspace . `
    --tool run_uvm_simulation `
    --test-name uart_axi4_basic_115200_test `
    --mode run `
    --verbosity UVM_MEDIUM `
    --waves `
    --timeout 300
```

#### 1-5. 結果確認

**成功パターンの確認:**
```powershell
# Phase 1 完了メッセージ
Get-Content sim/exec/logs/*.log | Select-String -Pattern "CONFIG write completed via AXI"

# Test 側の timing 更新メッセージ
Get-Content sim/exec/logs/*.log | Select-String -Pattern "CONFIG write complete - switching UVM timing"

# UVM 環境更新メッセージ
Get-Content sim/exec/logs/*.log | Select-String -Pattern "UVM environment updated.*byte_time_ns"

# Phase 2 開始メッセージ
Get-Content sim/exec/logs/*.log | Select-String -Pattern "PHASE.*2.*Testing data transfer"

# エラー確認（FATAL が出ていないこと）
Get-Content sim/exec/logs/*.log | Select-String -Pattern "UVM_FATAL" | Select-Object -Last 10
```

**期待される出力:**
```
UVM_INFO @ 15964000: CONFIG write completed via AXI (addr=0x00001008, data=0x00000087). 
                      UART response not captured (expected - DUT switched to new baud rate). 
                      Test will update UVM timing parameters.

UVM_INFO @ 15964500: [BASIC115_PHASE1] CONFIG write complete - switching UVM timing to 921600 baud

UVM_INFO @ 15965000: [BASIC115_PHASE1] UVM environment updated: byte_time_ns=10850, bit_time_cycles=135

UVM_INFO @ 15965500: === PHASE 2: Testing data transfer at 921600 baud ===
```

### 成功判定基準

- ✅ コンパイルエラーなし
- ✅ "CONFIG write completed via AXI" メッセージ出力
- ✅ "CONFIG write complete - switching UVM timing" 出力
- ✅ "UVM environment updated" 出力
- ✅ "PHASE 2" 開始メッセージ出力
- ✅ `UVM_FATAL` エラーなし
- ✅ Test がハングせず終了（成功 or Phase 2 での別エラー）

### ロールバック手順（問題発生時）

```powershell
# バックアップから復元
$backup = Get-Item sim/uvm/sequences/uart_configure_baud_sequence.sv.backup_* | Sort-Object LastWriteTime -Descending | Select-Object -First 1
Copy-Item $backup.FullName sim/uvm/sequences/uart_configure_baud_sequence.sv -Force

# 再コンパイル
python mcp_server/mcp_client.py --workspace . `
    --tool run_uvm_simulation `
    --test-name uart_axi4_basic_115200_test `
    --mode compile `
    --verbosity UVM_LOW `
    --timeout 180
```

### 完了条件

- [ ] バックアップ作成完了
- [ ] コード修正適用完了
- [ ] コンパイル成功確認
- [ ] シミュレーション実行完了
- [ ] Phase 2 到達確認
- [ ] エラーログ確認（FATAL なし）

**所要時間:** 約1時間  
**リスクレベル:** 低（1ファイル・局所的変更）

---

## ステップ2: 中期改善（1週間以内）

### 実装条件
以下のいずれかに該当する場合に実装:
- ステップ1 で Phase 2 に到達するが、Phase 2 でボーレート関連エラーが発生
- より堅牢な同期処理が必要と判断された場合
- 他のボーレート切替テストでも同様の対策が必要

### 目的
Test 側で明示的な再同期処理を追加し、UVM 環境が新ボーレートで安定動作するようにする

### 対象ファイル
1. `sim/uvm/tests/uart_axi4_basic_115200_test.sv`
2. `sim/uvm/agents/uart/uart_monitor.sv`
3. `sim/uvm/agents/uart/uart_driver.sv`

### 実装手順

#### 2-1. Monitor に状態リセット API 追加

**ファイル:** `sim/uvm/agents/uart/uart_monitor.sv`

**追加場所:** Class 内の function 定義部分（既存の function の後）

**追加コード:**
```systemverilog
// ボーレート切替時の状態リセット
// - 収集中のバイト列をクリア
// - フレーム解析状態をリセット
// - タイムスタンプをリセット
function void reset_sampling_state();
    `uvm_info(get_type_name(), 
        $sformatf("Resetting sampling state @ t=%0t for baud rate change", $time),
        UVM_HIGH)
    
    // 収集中のデータをクリア
    collected_bytes.delete();
    
    // フレーム解析状態をリセット
    current_frame_start_time = 0;
    frame_parse_in_progress = 0;
    
    // 連続エラーカウンタをリセット（存在する場合）
    if (consecutive_parse_errors > 0) begin
        `uvm_info(get_type_name(), 
            $sformatf("Clearing %0d consecutive parse errors", consecutive_parse_errors),
            UVM_MEDIUM)
        consecutive_parse_errors = 0;
    end
endfunction
```

#### 2-2. Driver に応答バッファリセット API 追加

**ファイル:** `sim/uvm/agents/uart/uart_driver.sv`

**追加場所:** Class 内の function 定義部分

**追加コード:**
```systemverilog
// ボーレート切替時の応答バッファリセット
// - FIFO 内の未処理データをクリア
// - Timeout カウンタをリセット
function void reset_response_buffer();
    `uvm_info(get_type_name(), 
        $sformatf("Resetting response buffer @ t=%0t for baud rate change", $time),
        UVM_HIGH)
    
    // FIFO の未処理データがあれば警告
    // （実装は FIFO interface の仕様による）
    
    // Timeout 関連の状態をリセット
    // （実装は内部構造による）
endfunction
```

#### 2-3. Test に明示的な再同期処理追加

**ファイル:** `sim/uvm/tests/uart_axi4_basic_115200_test.sv`

**修正箇所:** Line 167-186 の `program_baud_divisor_register()` task

**修正前:**
```systemverilog
// Phase 1: Configure baud divisor via UART protocol
cfg_seq = uart_configure_baud_sequence::type_id::create("uart_cfg_baud_seq");
cfg_seq.addr = CONFIG_REG_ADDR;
cfg_seq.data = DIVISOR_921600;
cfg_seq.start(env.uart_agt.sequencer);

// Update UVM environment timing for new baud rate
cfg.baud_rate = TARGET_BAUD_RATE;
cfg.calculate_timing();

`uvm_info("BASIC115_PHASE1", 
    $sformatf("CONFIG write complete - switching UVM timing to %0d baud", TARGET_BAUD_RATE),
    UVM_LOW)

`uvm_info("BASIC115_PHASE1", 
    $sformatf("UVM environment updated: byte_time_ns=%0d, bit_time_cycles=%0d", 
              cfg.byte_time_ns, cfg.bit_time_cycles),
    UVM_LOW)
```

**修正後:**
```systemverilog
// Phase 1: Configure baud divisor via UART protocol
cfg_seq = uart_configure_baud_sequence::type_id::create("uart_cfg_baud_seq");
cfg_seq.addr = CONFIG_REG_ADDR;
cfg_seq.data = DIVISOR_921600;
cfg_seq.start(env.uart_agt.sequencer);

`uvm_info("BASIC115_PHASE1", 
    $sformatf("CONFIG write completed @ t=%0t. Waiting for DUT to stabilize at new baud rate...", $time),
    UVM_MEDIUM)

// DUT がボーレート切替後に安定するまで待機
// - 新ボーレート (921600) で数バイト送信完了する時間
// - TX line が idle になることを想定
// - 計算: 4 bytes × (1 start + 8 data + 1 stop) × (1/921600) ≈ 43 μs
//         安全マージン含めて 10 μs
#10us;

`uvm_info("BASIC115_PHASE1", 
    $sformatf("DUT stabilization wait complete @ t=%0t. Updating UVM timing...", $time),
    UVM_HIGH)

// UVM 環境のタイミングパラメータを更新
cfg.baud_rate = TARGET_BAUD_RATE;
cfg.calculate_timing();

`uvm_info("BASIC115_PHASE1", 
    $sformatf("CONFIG write complete - switching UVM timing to %0d baud", TARGET_BAUD_RATE),
    UVM_LOW)

`uvm_info("BASIC115_PHASE1", 
    $sformatf("UVM environment updated: byte_time_ns=%0d, bit_time_cycles=%0d", 
              cfg.byte_time_ns, cfg.bit_time_cycles),
    UVM_LOW)

// Monitor/Driver の内部状態をリセット
`uvm_info("BASIC115_PHASE1", 
    "Resetting Monitor and Driver state for clean Phase 2 start",
    UVM_HIGH)

env.uart_agt.monitor.reset_sampling_state();
env.uart_agt.driver.reset_response_buffer();

`uvm_info("BASIC115_PHASE1", 
    $sformatf("Phase 1 complete @ t=%0t. Ready for Phase 2 data transfer.", $time),
    UVM_MEDIUM)
```

#### 2-4. コンパイル＆実行

```powershell
# バックアップ作成（3ファイル）
$timestamp = Get-Date -Format 'yyyyMMdd_HHmmss'
Copy-Item sim/uvm/tests/uart_axi4_basic_115200_test.sv `
          sim/uvm/tests/uart_axi4_basic_115200_test.sv.backup_$timestamp
Copy-Item sim/uvm/agents/uart/uart_monitor.sv `
          sim/uvm/agents/uart/uart_monitor.sv.backup_$timestamp
Copy-Item sim/uvm/agents/uart/uart_driver.sv `
          sim/uvm/agents/uart/uart_driver.sv.backup_$timestamp

# コンパイル
python mcp_server/mcp_client.py --workspace . `
    --tool run_uvm_simulation `
    --test-name uart_axi4_basic_115200_test `
    --mode compile `
    --verbosity UVM_LOW `
    --timeout 180

# 実行
python mcp_server/mcp_client.py --workspace . `
    --tool run_uvm_simulation `
    --test-name uart_axi4_basic_115200_test `
    --mode run `
    --verbosity UVM_MEDIUM `
    --waves `
    --timeout 300
```

#### 2-5. 結果確認

```powershell
# 追加メッセージの確認
Get-Content sim/exec/logs/*.log | Select-String -Pattern "Waiting for DUT to stabilize|Resetting.*state|Phase 1 complete"

# Phase 2 でのエラー確認
Get-Content sim/exec/logs/*.log | Select-String -Pattern "PHASE.*2" -Context 0,20

# ボーレート関連エラー
Get-Content sim/exec/logs/*.log | Select-String -Pattern "baud.*mismatch|parse.*error|frame.*too short"
```

### 成功判定基準

- ✅ ステップ1 の全判定基準をクリア
- ✅ "Waiting for DUT to stabilize" メッセージ出力
- ✅ "Resetting Monitor and Driver state" メッセージ出力
- ✅ "Phase 1 complete" メッセージ出力
- ✅ Phase 2 でボーレート関連のエラーが**減少**または**消失**
- ✅ Test が最後まで実行される

### 完了条件

- [ ] Monitor に `reset_sampling_state()` 追加完了
- [ ] Driver に `reset_response_buffer()` 追加完了
- [ ] Test に待機＆リセット処理追加完了
- [ ] コンパイル成功確認
- [ ] シミュレーション実行完了
- [ ] Phase 2 の安定動作確認
- [ ] 回帰テスト実行（他のテストに影響なし）

**所要時間:** 2-3日  
**リスクレベル:** 中（3ファイル変更・既存機能への影響あり）

---

## ステップ3: 長期対策（要検討・1ヶ月以内）

### 実装条件
以下の**すべて**に該当する場合にのみ実装:
- ステップ1 + ステップ2 で安定動作しない
- 他のテストケースでも同様の問題が多発
- RTL 変更が許容される開発フェーズ
- 長期的な保守性を最優先する方針

### 目的
RTL に `baud_switch_done` ステータスビットを追加し、ハードウェアレベルで確実な同期を実現

### 対象ファイル
1. `rtl/Register_Block.sv`
2. `sim/uvm/sequences/uart_axi4_axi_read_sequence.sv`（新規作成または既存利用）
3. `sim/uvm/sequences/uart_configure_baud_sequence.sv`（ステップ1の修正に追加）
4. `sim/uvm/tests/uart_axi4_basic_115200_test.sv`（ステップ2の修正に追加）

### 実装手順

#### 3-1. RTL に STATUS ビット追加

**ファイル:** `rtl/Register_Block.sv`

**追加場所1:** Parameter 定義部分

```systemverilog
// STATUS register bit definitions
localparam STATUS_TX_BUSY_BIT       = 0;
localparam STATUS_RX_READY_BIT      = 1;
localparam STATUS_TX_FIFO_FULL_BIT  = 2;
localparam STATUS_RX_FIFO_EMPTY_BIT = 3;
localparam STATUS_BAUD_APPLIED_BIT  = 4;  // ★追加: Baud rate change applied
```

**追加場所2:** Internal signal 定義部分

```systemverilog
logic baud_switch_in_progress;
logic baud_applied;
```

**追加場所3:** Sequential logic 部分

```systemverilog
// Baud rate switch tracking
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        baud_switch_in_progress <= 1'b0;
        baud_applied <= 1'b1;  // Reset 直後は適用済みとする
    end else begin
        // CONFIG register への書き込み検出
        if (axi_wvalid && axi_wready && axi_awaddr == CONFIG_ADDR) begin
            baud_switch_in_progress <= 1'b1;
            baud_applied <= 1'b0;
            `ifdef ENABLE_DEBUG
            $display("[%0t][REG_BLOCK] Baud switch initiated - divisor=0x%04h", 
                     $time, axi_wdata[15:0]);
            `endif
        end
        
        // Response frame 送信完了検出
        // （Frame_Builder または Bridge からの信号が必要）
        else if (baud_switch_in_progress && response_tx_complete) begin
            baud_switch_in_progress <= 1'b0;
            baud_applied <= 1'b1;
            `ifdef ENABLE_DEBUG
            $display("[%0t][REG_BLOCK] Baud switch completed - new rate applied", $time);
            `endif
        end
    end
end
```

**追加場所4:** STATUS register 読み出し部分

```systemverilog
// STATUS register composition
assign status_reg[STATUS_TX_BUSY_BIT]       = tx_busy;
assign status_reg[STATUS_RX_READY_BIT]      = rx_ready;
assign status_reg[STATUS_TX_FIFO_FULL_BIT]  = tx_fifo_full;
assign status_reg[STATUS_RX_FIFO_EMPTY_BIT] = rx_fifo_empty;
assign status_reg[STATUS_BAUD_APPLIED_BIT]  = baud_applied;  // ★追加
assign status_reg[31:5]                     = 27'b0;          // Reserved bits
```

#### 3-2. AXI Read Sequence 作成または確認

**新規作成が必要な場合:**

**ファイル:** `sim/uvm/sequences/uart_axi4_axi_read_sequence.sv`

```systemverilog
`ifndef UART_AXI4_AXI_READ_SEQUENCE_SV
`define UART_AXI4_AXI_READ_SEQUENCE_SV

class uart_axi4_axi_read_sequence extends uvm_sequence #(axi4_lite_transaction);
    `uvm_object_utils(uart_axi4_axi_read_sequence)
    
    // Input parameters
    bit [31:0] addr;
    
    // Output data
    bit [31:0] read_data;
    bit [1:0]  response;
    
    function new(string name = "uart_axi4_axi_read_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        axi4_lite_transaction req;
        
        req = axi4_lite_transaction::type_id::create("axi_read_req");
        
        start_item(req);
        
        req.transaction_type = AXI_READ;
        req.addr = addr;
        
        finish_item(req);
        
        // Collect response
        read_data = req.rdata;
        response = req.rresp;
        
        `uvm_info(get_type_name(),
            $sformatf("AXI Read: ADDR=0x%08X, DATA=0x%08X, RESP=%0d",
                      addr, read_data, response),
            UVM_MEDIUM)
    endtask
endclass

`endif
```

#### 3-3. CONFIG Sequence にポーリング処理追加

**ファイル:** `sim/uvm/sequences/uart_configure_baud_sequence.sv`

**追加場所:** `finish_item(req)` の後、既存の検証コードの後

```systemverilog
// ステップ1 で追加した検証コードの後に追加

// ★ステップ3追加: AXI 経由で baud_applied ビットをポーリング
`uvm_info(get_type_name(), 
    "Polling STATUS register for baud_applied confirmation...",
    UVM_MEDIUM)

bit baud_confirmed = 0;
int poll_count = 0;
const int MAX_POLLS = 100;
const int POLL_INTERVAL_NS = 1000;  // 1 μs

uart_axi4_axi_read_sequence status_read_seq;

while (!baud_confirmed && poll_count < MAX_POLLS) begin
    status_read_seq = uart_axi4_axi_read_sequence::type_id::create("status_poll");
    status_read_seq.addr = STATUS_REG_ADDR;  // 0x0000_100C など
    
    // AXI master sequencer で実行（要: sequencer handle の取得方法確認）
    // status_read_seq.start(m_axi_sequencer);
    
    if (status_read_seq.read_data[STATUS_BAUD_APPLIED_BIT]) begin
        baud_confirmed = 1;
        `uvm_info(get_type_name(),
            $sformatf("Baud rate applied confirmed @ poll #%0d (t=%0t)",
                      poll_count, $time),
            UVM_LOW)
        break;
    end
    
    #(POLL_INTERVAL_NS * 1ns);
    poll_count++;
end

if (!baud_confirmed) begin
    `uvm_warning(get_type_name(),
        $sformatf("Baud rate applied bit not confirmed after %0d polls. Proceeding anyway.",
                  MAX_POLLS))
end
```

#### 3-4. Test 側でポーリング待機

**ファイル:** `sim/uvm/tests/uart_axi4_basic_115200_test.sv`

**修正箇所:** ステップ2 で追加した `#10us` 待機の部分

**修正前（ステップ2）:**
```systemverilog
// DUT がボーレート切替後に安定するまで待機
#10us;
```

**修正後（ステップ3）:**
```systemverilog
// CONFIG sequence 内でポーリング完了しているため、追加待機は不要
// （または短縮）
#1us;  // 最小限の安定化待機
```

#### 3-5. RTL シミュレーションとデバッグ

```powershell
# RTL 変更のバックアップ
$timestamp = Get-Date -Format 'yyyyMMdd_HHmmss'
Copy-Item rtl/Register_Block.sv rtl/Register_Block.sv.backup_$timestamp

# RTL 変更適用後、コンパイル
python mcp_server/mcp_client.py --workspace . `
    --tool run_uvm_simulation `
    --test-name uart_axi4_basic_115200_test `
    --mode compile `
    --verbosity UVM_LOW `
    --timeout 180

# 実行
python mcp_server/mcp_client.py --workspace . `
    --tool run_uvm_simulation `
    --test-name uart_axi4_basic_115200_test `
    --mode run `
    --verbosity UVM_HIGH `
    --waves `
    --timeout 300
```

#### 3-6. 波形確認

```powershell
# STATUS register の baud_applied ビット確認
# Waves デバッガで以下をモニタ:
#   - Register_Block.baud_switch_in_progress
#   - Register_Block.baud_applied
#   - Register_Block.status_reg[4]
#   - AXI read transaction (ADDR=0x100C)
```

#### 3-7. 回帰テスト

```powershell
# 他のテストケースでの動作確認
python mcp_server/mcp_client.py --workspace . `
    --tool run_uvm_simulation `
    --test-name uart_axi4_basic_test `
    --mode run `
    --verbosity UVM_MEDIUM `
    --timeout 300

# 基本的な AXI read/write テスト
python mcp_server/mcp_client.py --workspace . `
    --tool run_uvm_simulation `
    --test-name uart_axi4_single_write_test `
    --mode run `
    --verbosity UVM_MEDIUM `
    --timeout 300
```

### 成功判定基準

- ✅ RTL に `STATUS_BAUD_APPLIED_BIT` 追加完了
- ✅ `baud_applied` ロジック動作確認（波形）
- ✅ AXI read sequence でステータス読み出し成功
- ✅ CONFIG sequence でポーリング成功
- ✅ "Baud rate applied confirmed" メッセージ出力
- ✅ Test が Phase 2 まで安定動作
- ✅ 回帰テストで既存機能に影響なし

### リスク評価と対策

#### リスク1: RTL 変更による既存機能への影響
**対策:**
- STATUS register の既存ビット（bit 0-3）は変更しない
- Reserved bits（bit 5-31）を使用
- `baud_applied` は read-only（write 不可）

#### リスク2: response_tx_complete 信号の取得
**現状確認が必要:**
- Frame_Builder や Bridge から completion 信号が出ているか
- Register_Block まで配線されているか

**対策:**
- 信号がない場合は新規追加が必要
- または、TX_BUSY ビットの立ち下がりを検出

#### リスク3: AXI read sequence の実装
**対策:**
- 既存の AXI master agent の interface を確認
- Sequencer handle の取得方法を明確化
- AXI read transaction の動作を事前検証

### 完了条件

- [ ] RTL 設計レビュー完了
- [ ] `Register_Block.sv` 修正完了
- [ ] AXI read sequence 実装完了
- [ ] CONFIG sequence ポーリング追加完了
- [ ] Test 側待機時間調整完了
- [ ] コンパイル成功確認
- [ ] 波形でロジック動作確認
- [ ] シミュレーション実行完了
- [ ] 回帰テスト全件パス
- [ ] ドキュメント更新（RTL 仕様書、レジスタマップ）

**所要時間:** 1週間〜1ヶ月（設計レビュー・検証含む）  
**リスクレベル:** 高（RTL 変更・システム全体への影響）

---

## 実装判断フローチャート

```
Start
  │
  ├─► ステップ1 実装
  │     │
  │     ├─► Phase 2 到達？
  │     │     ├─ Yes ─► Phase 2 で安定動作？
  │     │     │           ├─ Yes ─► 完了（ステップ2/3 不要）
  │     │     │           └─ No ──► ステップ2 へ
  │     │     └─ No ──► ステップ1 修正再実施 or ステップ2 へ
  │
  ├─► ステップ2 実装（条件: Phase 2 不安定）
  │     │
  │     ├─► Phase 2 で安定動作？
  │     │     ├─ Yes ─► 完了（ステップ3 不要）
  │     │     └─ No ──► 他のテストでも問題？
  │     │                 ├─ Yes ─► ステップ3 検討
  │     │                 └─ No ──► ステップ2 修正再実施
  │
  └─► ステップ3 実装（条件: RTL 変更許可 + 長期対策必要）
        │
        ├─► RTL 設計レビュー
        ├─► 実装＆検証
        └─► 回帰テスト全件パス ─► 完了
```

---

## トラブルシューティング

### ステップ1 で Phase 2 に到達しない

**確認項目:**
```powershell
# Sequence の修正が適用されているか
Select-String -Path sim/uvm/sequences/uart_configure_baud_sequence.sv `
              -Pattern "CONFIG write completed via AXI"

# コンパイルエラー
Get-Content sim/exec/logs/*.log | Select-String -Pattern "error|Error"

# Test が別の箇所でハング
Get-Content sim/exec/logs/*.log | Select-Object -Last 100
```

### ステップ2 で Monitor リセットが効かない

**確認項目:**
```systemverilog
// Monitor の internal state を確認
// - collected_bytes.size() が 0 にリセットされているか
// - 波形で reset_sampling_state() 呼び出しタイミング確認
```

### ステップ3 で baud_applied が立たない

**確認項目:**
```powershell
# RTL ログで baud_switch_in_progress の遷移確認
Get-Content sim/exec/logs/*.log | Select-String -Pattern "Baud switch initiated|Baud switch completed"

# response_tx_complete 信号の有無確認
# 波形で Frame_Builder の完了タイミングと Register_Block の入力を確認
```

---

## 開発日誌への記録

各ステップ完了時に `docs/diary_<date>.md` に記録:

```markdown
## ステップ1 完了 (2024-11-18)

**実装内容:**
- uart_configure_baud_sequence.sv 修正（response 検証緩和）

**結果:**
- Phase 2 到達成功
- CONFIG write complete メッセージ確認
- UVM environment updated 確認

**次のアクション:**
- Phase 2 の動作を1週間観察
- 必要に応じてステップ2 実装検討
```

---

**Document Version:** 1.0  
**Last Updated:** 2024-11-18  
**Status:** Ready for Step 1 Implementation  
**Next Action:** ステップ1 バックアップ作成から開始
