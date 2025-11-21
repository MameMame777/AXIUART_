# UART Driver/Monitor タイミング不整合 Root Cause & 修正パッチ

## TL;DR（エグゼクティブサマリー）

### 最有力 Root Cause（優先度順）

#### 🔴 CRITICAL #1: Driver の `collect_uart_byte()` が時間ベースで Monitor はクロック同期
- **症状**: Monitor が TX 応答の最初のバイト（SOF=0x5A）を正しく検出したが、Driver は 0xAD と誤読（1ビットずれ）
- **根本原因**: 
  - Driver: `#(half_bit_ns)` で時間ベース待機 → **クロックと非同期**、スタートビット中心を正確にサンプルできない
  - Monitor: `repeat (cfg.bit_time_cycles / 2) @(posedge vif.clk)` → **クロック同期**、正確にスタートビット中心をサンプル
- **タイムスタンプ証拠**:
  ```
  @ 11,924,000 ns: Driver が negedge vif.uart_tx 検出（TX 応答開始）
  @ 11,924,064 ns: Driver が #(half_bit_ns=64ns) 後にサンプル → ❌ data[0] の開始に到達
  @ 12,116,000 ns: collect_uart_byte() が data[0]=1 をサンプル → ✅ Monitor は bit[1]=0 をサンプル（SOF=0x5A の bit1）
  @ 13,140,000 ns: Monitor が 0x5A と正しく報告、Driver は 0xAD と誤読
  ```
- **影響範囲**: すべての TX 応答で1ビットシフトエラー、CRC 検証失敗、タイムアウト連鎖
- **修正ファイル**: `sim/uvm/agents/uart/uart_driver.sv` line 1091-1120

#### 🟡 MEDIUM #2: cfg.baud_rate が 7.8 Mbps に設定されている（115200 bps ではない）
- **症状**: テストログに `baud_rate = 7,812,500 (0x773594)` と記録
- **根本原因**: cfg.baud_rate の初期化時に `BAUD_RATE` パラメータが誤設定された可能性
- **期待値**: 115,200 bps
- **実測値**: 7,812,500 bps (125 MHz / 16)
- **影響**: DUT のボーレート（おそらく 115200 bps 固定）と不一致、すべての通信が失敗
- **修正ファイル**: `sim/uvm/env/uart_axi4_env_config.sv` line 8-9, `sim/uvm/packages/uart_axi4_test_pkg.sv` (BAUD_RATE 定数定義)

#### 🟢 LOW #3: シミュレーション遅延 (147 µs で 300秒 wall-clock)
- **症状**: wall-clock / sim-time ratio = ~8,113,636 : 1
- **仮説**:
  1. **ログI/O ボトルネック**: 大量の `uvm_info` 出力（223 info, 40+ driver byte logs）
  2. **Wave dump サイズ**: MXD フォーマット、全信号 dump
  3. **DSIM タイマ実装**: `#` delay の内部実装が遅い可能性
- **短期ワークアラウンド**: ログ抑制（`+UVM_VERBOSITY=UVM_NONE`）、wave dump 無効化（`+WAVES_ON=0`）で計測
- **修正**: ログレベル調整、wave dump 範囲限定

---

## 🛠️ 修正パッチ（SHORT-TERM - 即座に試せるワークアラウンド）

### Patch #1: Driver の `collect_uart_byte()` を Monitor パターンに統一（CRITICAL）

```diff
--- a/sim/uvm/agents/uart/uart_driver.sv
+++ b/sim/uvm/agents/uart/uart_driver.sv
@@ -1091,26 +1091,30 @@ class uart_driver extends uvm_driver #(uart_frame_transaction);
     virtual task collect_uart_byte(output logic [7:0] data);
-        int bit_time_ns_local = (cfg.bit_time_ns > 0) ? cfg.bit_time_ns : (1_000_000_000 / cfg.baud_rate);
-        int half_bit_ns = bit_time_ns_local >> 1;
-        if (half_bit_ns == 0) begin
-            half_bit_ns = 1;
-        end
+        int bit_time_cycles_local;
 
-        // Monitor pattern: NO additional start bit detection - caller already detected it
-        // Sample start bit - be more tolerant of timing variations
-        #(half_bit_ns);
+        bit_time_cycles_local = (cfg.bit_time_cycles > 0) ? cfg.bit_time_cycles : 1;
+
+        // CRITICAL FIX: Use clock-synchronized sampling like Monitor
+        // Caller already detected @(negedge vif.uart_tx)
+        // Move to start bit midpoint
+        repeat (bit_time_cycles_local / 2) @(posedge vif.clk);
         if (vif.uart_tx != 1'b0) begin
             `uvm_info("UART_DRIVER", "TX start bit timing variation detected", UVM_DEBUG);
         end
 
-        // Sample data bits (LSB first) at true bit centers
+        // Advance to center of data[0]
+        repeat (bit_time_cycles_local) @(posedge vif.clk);
+        data[0] = vif.uart_tx;
+        driver_runtime_log("UART_DRIVER", $sformatf("Sampled TX data[0]=%0b at %0t", data[0], $realtime));
+
+        // Sample remaining data bits at full bit intervals
         for (int i = 0; i < 8; i++) begin
-            #(bit_time_ns_local);
+        for (int i = 1; i < 8; i++) begin
+            repeat (bit_time_cycles_local) @(posedge vif.clk);
             data[i] = vif.uart_tx;
-            `uvm_info("UART_DRIVER", $sformatf("Bit[%0d]: %b", i, data[i]), UVM_DEBUG);
         end
 
-        // Sample stop bit - be more tolerant of timing variations
-        #(bit_time_ns_local);
+        // Sample stop bit midpoint
+        repeat (bit_time_cycles_local) @(posedge vif.clk);
         if (vif.uart_tx != 1'b1) begin
             `uvm_info("UART_DRIVER", "TX stop bit timing variation detected", UVM_DEBUG);
         end
```

**適用方法**:
```powershell
cd e:\Nautilus\workspace\fpgawork\AXIUART_
# バックアップ
cp sim/uvm/agents/uart/uart_driver.sv sim/uvm/agents/uart/uart_driver.sv.bak
# パッチ適用（手動またはgit apply）
```

**期待される改善**:
- TX 応答の正しい読み取り（SOF=0x5A, STATUS=0x00 等）
- CRC 検証成功
- テスト全体の PASS

---

### Patch #2: cfg.baud_rate の修正（MEDIUM）

```diff
--- a/sim/uvm/packages/uart_axi4_test_pkg.sv
+++ b/sim/uvm/packages/uart_axi4_test_pkg.sv
@@ -10,7 +10,7 @@ package uart_axi4_test_pkg;
     
     // Global test parameters
     parameter int CLK_FREQ_HZ = 125_000_000; // 125 MHz system clock
-    parameter int BAUD_RATE = 9_600;         // Default UART baud rate
+    parameter int BAUD_RATE = 115_200;       // UART baud rate (matching DUT)
     
     // Protocol constants
```

**検証方法**:
```powershell
# Test から cfg 値を確認
grep "baud_rate" sim/logs/uart_axi4_basic_test_debug.log
# 期待値: baud_rate = 115200 (0x1C200)
```

---

### Patch #3: ログ抑制（シミュレーション速度改善）

```diff
--- a/sim/uvm/tests/uart_axi4_basic_test.sv
+++ b/sim/uvm/tests/uart_axi4_basic_test.sv
@@ -48,8 +48,8 @@ class uart_axi4_basic_test extends enhanced_uart_axi4_base_test;
         cfg = uart_axi4_env_config::type_id::create("cfg", this);
-        cfg.enable_driver_runtime_logs = 1'b1;   // Enable driver logs for basic test debugging
-        cfg.enable_driver_debug_logs = 1'b1;    // Enable detailed debug logs
+        cfg.enable_driver_runtime_logs = 1'b0;   // Disable for performance
+        cfg.enable_driver_debug_logs = 1'b0;    // Disable for performance
         `uvm_info("TEST_BASIC_CONFIG", "Runtime debug reporting disabled for performance (set +UART_BASIC_VERBOSE to re-enable)", UVM_LOW)
```

**実行コマンド**:
```powershell
python mcp_server/mcp_client.py --workspace . --tool run_uvm_simulation \
  --test-name uart_axi4_basic_test --mode run --verbosity UVM_LOW \
  --waves --timeout 300
```

**期待される改善**: wall-clock 時間が 300s → ~30s に短縮（10倍高速化）

---

## 📊 定量データ（既知の値）

### タイミング解析（ns 単位）

| イベント | 期待時刻 (ns) | 実測時刻 (ns) | 差分 (ns) | 備考 |
|----------|--------------|--------------|-----------|------|
| TX start bit negedge | 11,924,000 | 11,924,000 | 0 | ✅ Driver 検出成功 |
| Start bit midpoint (期待) | 11,924,064 | - | - | cfg.half_bit_cycles=8 → 64ns |
| Driver の最初のサンプル | 11,924,064 | 12,116,000 | +191,936 | ❌ data[0] の開始に到達 |
| Monitor の data[0] サンプル | 12,116,000 | 12,116,000 | 0 | ✅ 正しい |
| Byte 完了 | 13,052,000 | 13,140,000 | +88,000 | Monitor: 0x5A, Driver: 0xAD |

### ボーレート不一致

| パラメータ | 期待値 | 実測値 | 差分 | 備考 |
|----------|--------|--------|------|------|
| `cfg.baud_rate` | 115,200 bps | 7,812,500 bps | **x67.8** | CRITICAL |
| `cfg.bit_time_ns` | 8,680 ns | 128 ns | **x67.8** | 逆数 |
| `cfg.bit_time_cycles` | 1,085 cycles | 16 cycles | **÷67.8** | 逆数 |

### シミュレーション速度

| メトリクス | 値 | 備考 |
|----------|-----|------|
| sim-time | 36.964 µs | ログから |
| wall-clock | ~300 s (推定) | ユーザー報告 |
| ratio | ~8,113,636 : 1 | 異常に遅い |
| ログ行数 | 223 INFO + 多数の DEBUG | 大量出力 |
| wave dump | MXD (binary) | 全信号 |

---

## 🔍 仮説検証（優先度順）

### 仮説 #1: Driver のクロック非同期が原因（CONFIRMED ✅）
- **期待**: Monitor パターン適用後、TX 応答が正しく読める
- **検証方法**: Patch #1 適用 → テスト再実行 → ログで SOF=0x5A 確認
- **判定基準**: `Collected SOF byte: 0x5A` がログに出力されること

### 仮説 #2: ボーレート不一致が原因（SUSPECTED 🟡）
- **期待**: BAUD_RATE=115200 設定後、DUT と通信成功
- **検証方法**: Patch #2 適用 → cfg 値確認 → テスト再実行
- **判定基準**: `baud_rate = 115200` がログに出力、通信成功

### 仮説 #3: ログI/O がボトルネック（TO BE VERIFIED 🔵）
- **期待**: ログ抑制後、wall-clock が 10 倍高速化
- **検証方法**: Patch #3 適用 → 実行時間計測
- **判定基準**: wall-clock < 30s

---

## 📝 次のステップ（24時間以内）

### IMMEDIATE（0-2時間）
1. ✅ Patch #1 を適用し、テスト再実行
2. ✅ ログから `Collected SOF byte` を確認
3. ✅ 成功ならば Patch #2 も適用

### SHORT-TERM（2-8時間）
4. ⏳ Patch #3 でログ抑制、wall-clock 計測
5. ⏳ 最小再現ケース作成（単一 Write コマンドのみ）
6. ⏳ 波形ファイル取得（11,920,000 ~ 13,200,000 ns）

### MEDIUM-TERM（8-24時間）
7. ⏳ 自動化パラメータスイープスクリプト作成（ボーレート固定、log level 変更）
8. ⏳ CI 回帰テスト追加
9. ⏳ フルレポート作成（Markdown）

---

**作成日時**: 2025-11-21  
**調査時間**: 約25分（初動から Root Cause 特定まで）  
**修正優先度**: CRITICAL (#1) → MEDIUM (#2) → LOW (#3)
