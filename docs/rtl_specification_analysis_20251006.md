# 📋 Phase 1 実行: RTL仕様詳細把握レポート

**実行日**: 2025年10月6日  
**対象**: AXIUART_ RTL実装詳細調査  
**作業基準**: protocol_alignment_work_instruction_20251006.md Phase 1

---

## 🔍 1.1 プロトコル定数の完全調査

### 1.1.1 SOF定数の調査結果

#### 全RTLファイルでのSOF関連定数検索
```bash
# 実行コマンド結果
grep -r "SOF\|0x5A\|0x2D" rtl/ --include="*.sv"
```

**重要発見**: RTL内で複数のSOF定数が定義されている

#### 1.1.1.1 Frame_Builder.svでのSOF定数定義
```systemverilog
// File: rtl/Frame_Builder.sv (line 37)
localparam [7:0] SOF_DEVICE_TO_HOST = 8'h5A;

// Hardware correction for observed UART transmission bit flips
// Updated based on FPGA test results (2025-10-06)
// New patterns: SOF 0x5A→0x6B (XOR 0x31), CMD 0x20→0x39 (XOR 0x19), STATUS 0x00→0x60 (XOR 0x60)
localparam [7:0] SOF_CORRECTION_MASK = 8'h31;        // To compensate for 0x5A→0x6B flip
localparam [7:0] SOF_DEVICE_TO_HOST_CORRECTED = SOF_DEVICE_TO_HOST ^ SOF_CORRECTION_MASK;
```

**計算結果**: `0x5A ^ 0x31 = 0x6B` (not 0x2D)

#### 1.1.1.2 Frame_Parser.svでのSOF定数定義
```systemverilog
// File: rtl/Frame_Parser.sv (line 46)
localparam [7:0] SOF_HOST_TO_DEVICE = 8'hA5;
```

**プロトコル構造**:
- Host → Device: SOF = 0xA5
- Device → Host: SOF = 0x5A (修正前) → 0x6B (修正後)

**問題**: 実際の送信値は0x6Bであり、期待値0x2Dと異なる

### 1.1.2 STATUS定数の調査結果

#### 1.1.2.1 AXI Master HandlerでのSTATUS生成

```systemverilog
// File: rtl/Axi4_Lite_Master.sv (line 29)
localparam [7:0] STATUS_OK = 8'h00;

// STATUS出力 (line 392)
assign axi_status = status_reg;
```

#### 1.1.2.2 BridgeでのSTATUS伝播処理

```systemverilog
// File: rtl/Uart_Axi4_Bridge.sv
logic [7:0] axi_status;          // AXI Masterからの入力
logic [7:0] builder_status_code; // Frame Builderへの出力

// 正常時の処理 (line 439)
builder_status_code = axi_status;  // 0x00を転送

// Frame Builderへの接続 (line 271)
.status_code(builder_status_code),
```

#### 1.1.2.3 Frame BuilderでのSTATUS修正処理

```systemverilog
// File: rtl/Frame_Builder.sv (line 44)
localparam [7:0] STATUS_CORRECTION_MASK = 8'h60;  // To compensate for 0x00→0x60 flip

// STATUS送信処理 (line 217)
debug_status_input = status_reg;                        // Original STATUS value (0x00)
debug_status_output = status_reg ^ STATUS_CORRECTION_MASK;  // Corrected STATUS (0x60)

// 実際の送信値
tx_fifo_data = status_reg ^ STATUS_CORRECTION_MASK;  // 0x00 ^ 0x60 = 0x60
```

**計算結果**: `0x00 ^ 0x60 = 0x60` (not 0x6C)

**プロトコル整合性問題発見**:

- 期待値: STATUS = 0x6C
- RTL実装値: STATUS = 0x60
- 差分: 0x0C (12 decimal)

### 1.1.3 CMD_ECHO処理の調査結果

#### 1.1.3.1 BridgeでのCMDキャプチャ処理

```systemverilog
// File: rtl/Uart_Axi4_Bridge.sv
logic [7:0] captured_cmd;

// Frame_Parser出力キャプチャ (line 335)
captured_cmd <= parser_cmd;

// Frame_Builderへのエコー出力 (line 417)
builder_cmd_echo = captured_cmd;
```

#### 1.1.3.2 Frame BuilderでのCMD_ECHO修正処理

```systemverilog
// File: rtl/Frame_Builder.sv (line 43)
localparam [7:0] CMD_CORRECTION_MASK = 8'h19;  // To compensate for 0x20→0x39 flip

// CMD送信処理 (line 238)
tx_fifo_data = cmd_reg ^ CMD_CORRECTION_MASK;

// デバッグ信号 (line 246-247)
debug_cmd_echo_in = cmd_echo;         // Original CMD value
debug_cmd_echo_out = cmd_reg ^ CMD_CORRECTION_MASK;  // Corrected CMD
```

**CMD_ECHOデータフロー**:
```
parser_cmd → captured_cmd → builder_cmd_echo → cmd_reg → cmd_reg ^ CMD_CORRECTION_MASK → tx_fifo_data
```

---

## 🔍 1.2 データフロー詳細解析

### 1.2.1 Frame Builder内データフロー

#### 1.2.1.1 プロトコルフィールド修正システム

**修正マスク定義** (Frame_Builder.sv line 42-44):
```systemverilog
localparam [7:0] SOF_CORRECTION_MASK = 8'h31;        // 0x5A→0x6B flip
localparam [7:0] CMD_CORRECTION_MASK = 8'h19;        // 0x20→0x39 flip  
localparam [7:0] STATUS_CORRECTION_MASK = 8'h60;     // 0x00→0x60 flip
```

**実際の変換結果**:

| Field | Original | Mask | Result | Expected |
|-------|----------|------|--------|----------|
| SOF   | 0x5A     | 0x31 | 0x6B   | 0x2D     |
| STATUS| 0x00     | 0x60 | 0x60   | 0x6C     |
| CMD   | 0x20*    | 0x19 | 0x39   | ?        |

*CMD値は実際の受信コマンドに依存

#### 1.2.1.2 送信データパス

```systemverilog
Input Values → status_reg/cmd_reg → Correction Logic → TX FIFO → UART TX
```

**詳細フロー** (Frame_Builder.sv):

1. `status_code` → `status_reg` (line 134)
2. `cmd_echo` → `cmd_reg` (line 135)  
3. `status_reg ^ STATUS_CORRECTION_MASK` → `tx_fifo_data` (line 217)
4. `cmd_reg ^ CMD_CORRECTION_MASK` → `tx_fifo_data` (line 238)

#### 1.2.2 UART送信経路データフロー

**TX FIFOからUART TXまでの完全経路**:

```
Frame_Builder.tx_fifo_data → TX FIFO → Uart_Tx.tx_data → tx_shift_reg → uart_tx_pin
```

**シリアル送信ビット順序** (Uart_Tx.sv line 145):
```systemverilog
DATA_BITS: uart_tx_int = tx_shift_reg[0]; // LSB first transmission
```

**bit shifting処理** (Uart_Tx.sv line 116):
```systemverilog
tx_shift_reg_next = {1'b0, tx_shift_reg[7:1]};  // Right shift for LSB first
```

---

## 🔍 1.3 状態管理ロジック解析

### 1.3.1 Frame Builder状態機械

#### 1.3.1.1 状態遷移とデータ送信タイミング

**状態定義** (Frame_Builder.sv line 64-74):
```systemverilog
typedef enum logic [3:0] {
    IDLE, SOF, STATUS, CMD, ADDR_BYTE0, ADDR_BYTE1, ADDR_BYTE2, ADDR_BYTE3, DATA, CRC, DONE
} frame_state_t;
```

**状態遷移フロー**:
```
IDLE → SOF → STATUS → CMD → [ADDR_BYTE0-3] → [DATA] → CRC → DONE → IDLE
```

**各状態でのtx_fifo_data値**:

| State | tx_fifo_data Value | Original | Correction |
|-------|------------------|----------|------------|
| SOF | SOF_DEVICE_TO_HOST_CORRECTED | 0x5A | 0x5A ^ 0x31 = 0x6B |
| STATUS | status_reg ^ STATUS_CORRECTION_MASK | 0x00 | 0x00 ^ 0x60 = 0x60 |
| CMD | cmd_reg ^ CMD_CORRECTION_MASK | cmd_reg | cmd_reg ^ 0x19 |
| ADDR_BYTE* | addr_reg[bits] | No correction | - |
| DATA | data_reg[index] | No correction | - |
| CRC | crc_out | No correction | - |

#### 1.3.1.2 状態間でのデータ保持・変更

**レジスタ更新タイミング** (Frame_Builder.sv line 130-140):
```systemverilog
// build_response_edge時の一括更新
if (build_response_edge) begin
    status_reg <= status_code;        // AXI Masterからの結果
    cmd_reg <= cmd_echo;             // Bridgeからのコマンドエコー
    addr_reg <= addr_echo;           // アドレスエコー
    // データとカウントの更新
end
```

**状態依存性**: 各レジスタは応答開始時に固定され、フレーム送信完了まで保持

### 1.3.2 Bridge状態管理

#### 1.3.2.1 メイン状態とbuilder制御の関係

**Bridge主要状態** (Uart_Axi4_Bridge.sv line 135-141):
```systemverilog
typedef enum logic [2:0] {
    MAIN_IDLE,                // フレーム待機
    MAIN_AXI_TRANSACTION,     // AXI処理実行
    MAIN_BUILD_RESPONSE,      // 応答フレーム生成開始
    MAIN_WAIT_RESPONSE,       // 応答送信完了待機
    MAIN_DISABLED_RESPONSE    // 無効化時応答
} main_state_t;
```

**各状態でのbuilder制御信号**:

| Bridge State | builder_build_response | builder_status_code | builder_cmd_echo |
|-------------|----------------------|-------------------|-----------------|
| MAIN_IDLE | 0 | 0x00 | 0x00 |
| MAIN_AXI_TRANSACTION | 0 | 0x00 | 0x00 |
| MAIN_BUILD_RESPONSE | 1 | axi_status | captured_cmd |
| MAIN_WAIT_RESPONSE | 0 | axi_status | captured_cmd |
| MAIN_DISABLED_RESPONSE | 1 | STATUS_BUSY_CODE | captured_cmd |

**重要**: `captured_cmd`はparser出力の消失前にキャプチャされ、応答完了まで保持される

---

## 📊 Phase 1 調査結果サマリー

### 🔍 発見された主要な不整合

#### 1. SOF値の不整合
- **期待値**: 0x2D  
- **RTL実装値**: 0x6B (0x5A ^ 0x31)
- **差分**: 0x46 (70 decimal)

#### 2. STATUS値の不整合  
- **期待値**: 0x6C
- **RTL実装値**: 0x60 (0x00 ^ 0x60)
- **差分**: 0x0C (12 decimal)

### 🔧 RTL修正マスクの確認済み動作

**修正システムは正常に動作中**:
- SOF修正: 0x5A → 0x6B (XOR 0x31)
- STATUS修正: 0x00 → 0x60 (XOR 0x60)  
- CMD修正: cmd_value → cmd_value ^ 0x19

### 📋 次段階への提言

1. **プロトコル仕様書との照合** (Phase 2)
2. **期待値の根拠確認** (Phase 2)
3. **テスト仕様の妥当性検証** (Phase 2)
4. **RTL vs 仕様の根本的整合性確立** (Phase 3)
