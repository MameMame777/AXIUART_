# 不足データリスト（24時間以内提出用）

## CRITICAL - タイミング不整合 Root Cause 特定に必要

### 1. 波形ファイル（最優先）
- **ファイル**: `E:\Nautilus\workspace\fpgawork\AXIUART_\archive\waveforms\uart_axi4_basic_test_20251115_092201.mxd`
- **必要時間窓**: 11,920,000 ns ~ 13,200,000 ns (TX 応答の最初のバイト)
- **必須信号**:
  - `uart_if_inst.uart_tx` (DUT → Driver)
  - `uart_if_inst.clk`
  - `dut.uart_bridge_inst.frame_builder.tx_fifo_data`
  - `dut.uart_bridge_inst.uart_tx_inst.state`
- **理由**: Driver が `@(negedge vif.uart_tx)` 検出後、`collect_uart_byte()` が最初の**データビット**をSOFの開始ビットとして誤読している証拠を確認するため

### 2. Monitor TX 収集実装（高優先度）
- **ファイル**: `e:\Nautilus\workspace\fpgawork\AXIUART_\sim\uvm\agents\uart\uart_monitor.sv`
- **必要行番号**: 180-350 (collect_tx_transactions および collect_uart_tx_byte の実装)
- **理由**: Monitor が正しく `0x5A` を検出した方法と、Driver との実装差分を特定するため

### 3. シミュレーション環境メトリクス
- **DSIM バージョン**: ログに記載あり (2025.1.0)
- **CPU 情報**: プロセッサコア数、スレッド数
- **実行時間**:
  - Wall-clock time: 300秒（想定）
  - Simulation time: 36.964 µs
  - **ratio**: ~8,113,636 : 1 (300s / 36.964µs)
- **メモリ使用量**: シミュレーション中のピーク
- **I/O 統計**: ログファイルサイズ、wave dump サイズ
- **理由**: シミュレーション遅延の根本原因（ログI/O vs wave dump vs タイマ実装）を切り分けるため

### 4. cfg 設定値の実際の値（実行時）
- **必要値** (ログから一部取得済み):
  ```
  clk_freq_hz = 125,000,000 (0x7735940)
  baud_rate = 7,812,500 (0x773594) <- CRITICAL: これは115200ではない！
  bit_time_ns = 128 (0x80)
  byte_time_ns = 1,280 (0x500)
  bit_time_cycles = 16 (0x10)
  half_bit_cycles = 8 (0x8)
  ```
- **問題**: `baud_rate = 7,812,500` は **115,200 bps ではなく、125MHz/16 = 7.8125 Mbps**！
- **理由**: ボーレート設定の不一致が根本原因の可能性

## 中優先度 - シミュレーション遅延の定量化

### 5. ログ出力統計
- **ログファイルサイズ**: `sim/exec/logs/*.log`
- **行数**: `wc -l sim/exec/logs/uart_axi4_basic_test_20251115_092201.log`
- **ログ生成レート**: lines/second during simulation
- **理由**: ログI/Oがボトルネックか確認

### 6. Wave dump 統計
- **ファイルサイズ**: `uart_axi4_basic_test_20251115_092201.mxd` のバイト数
- **dump 対象信号数**: `$dumpvars` の引数
- **理由**: Wave dump がボトルネックか確認

## 低優先度 - 再現性確認

### 7. 最小再現ケース用のシード値
- **現在のシード**: 1 (ログから確認済み)
- **追加実行**: seed=2,3,4,5 での同一テスト実行結果
- **理由**: 再現率の確認

## 即座に実行可能な分析（アーティファクト不要）

以下は現在のファイルだけで可能:
1. ✅ Driver の `collect_uart_byte()` タイミングバグ特定（完了）
2. ⏳ cfg.calculate_timing() の検証（baud_rate 不一致の確認）
3. ⏳ Monitor の TX 収集実装解析（file read で実行中）

## タイムライン

| 時刻 | イベント | 期待値 | 実測値 | 差分 |
|------|----------|--------|--------|------|
| 11,924,000 ns | TX start bit (negedge) | Driver 検出 | ✅ | - |
| ~11,924,064 ns | Start bit center | Driver が half_bit_ns 後にサンプル | ❌ (data[0] 開始へ) | +128 ns |
| 12,116,000 ns | First sample in collect_uart_byte | SOF bit0=0 | data[0]=1 (**SOF bit1**) | 1 bit shift |
| 12,244,000 ns | Second sample | SOF bit1=1 | data[1]=0 (SOF bit2) | 1 bit shift |
| ... | ... | ... | ... | ... |
| 13,140,000 ns | Monitor reports | SOF=0x5A | Driver=0xAD | bit-shift error |

**結論**: Driver は negedge 検出→half_bit_ns 待機で**スタートビットの中心ではなく、次のビット（data[0]）の開始**をサンプルしている。

## 次のステップ（優先度順）

1. **IMMEDIATE**: Monitor の `collect_uart_tx_byte` 実装確認（正しいパターンを特定）
2. **IMMEDIATE**: `uart_driver.sv` line 927-959 の修正パッチ作成
3. **SHORT-TERM**: baud_rate 不一致（7.8Mbps vs 115200bps）の調査
4. **SHORT-TERM**: 最小ログ/最小波形での再実行（wall-clock 改善測定）
5. **MEDIUM-TERM**: 自動化パラメータスイープスクリプト作成

---
**更新日時**: 2025-11-21 (調査開始から15分経過)
