# ✅ AXIUART_ カバレッジ向上 実行チェックリスト

**作成日**: 2025年9月28日  
**基準ドキュメント**: coverage_improvement_plan_20250928.md  
**現在のベースライン**: Toggle 14.0%, Expression 83.3%, Functional 25.0%

---

## 🚀 Phase 4.1: Toggle Coverage集中改善 (1週間目標)

### 📋 作業前準備チェックリスト

- [ ] **環境確認**
  - [ ] DSIM_HOME設定確認: `echo $env:DSIM_HOME`
  - [ ] DSIM_LIB_PATH設定確認: `echo $env:DSIM_LIB_PATH`  
  - [ ] DSIM_ROOT設定確認: `echo $env:DSIM_ROOT`
  - [ ] 作業ディレクトリ移動: `cd E:\Nautilus\workspace\fpgawork\AXIUART_\sim\uvm`

- [ ] **ベースライン記録**
  - [ ] 現在のカバレッジ記録: Toggle 14.0%, Expression 83.3%, Functional 25.0%
  - [ ] 基本テスト実行確認: `.\run_uvm.ps1 -TestName "uart_axi4_basic_test" -Waves:$true`
  - [ ] UVM_ERROR: 0 確認
  - [ ] metrics.db サイズ記録: `(Get-Item "metrics.db").Length / 1MB`

### 📋 Task 4.1.1: register_block_inst改善 (最優先)

**目標**: 13.7% → 65%+ (Toggle Coverage)  
**予想工数**: 2-3日

#### 4.1.1.1 レジスタマップ全アドレス範囲テスト
- [ ] **ファイル作成**: `sequences/register_comprehensive_sequence.sv`
  ```systemverilog
  class register_comprehensive_access_sequence extends uart_frame_sequence;
  ```

- [ ] **実装内容**
  - [ ] 全レジスタアドレス 0x1000-0x1FFF の順次アクセス
  - [ ] 有効アドレス範囲の確認テスト
  - [ ] 無効アドレス (範囲外) のエラーレスポンス確認
  - [ ] アドレスデコーダー全パスの動作確認

- [ ] **テスト実行・確認**
  - [ ] コンパイル成功確認
  - [ ] 単体テスト実行: `.\run_uvm.ps1 -TestName "register_comprehensive_test" -Waves:$true`
  - [ ] UVM_ERROR: 0 維持確認
  - [ ] カバレッジ改善確認: register_block_inst ≥ 25%

#### 4.1.1.2 読み書きパターン全組み合わせ
- [ ] **アクセス幅テスト実装**
  - [ ] 8-bit アクセス (size=2'b00) 全レジスタ
  - [ ] 16-bit アクセス (size=2'b01) 全レジスタ  
  - [ ] 32-bit アクセス (size=2'b10) 全レジスタ
  - [ ] 無効サイズ (size=2'b11) エラー確認

- [ ] **アライメントテスト実装**
  - [ ] 0x00 offset (4-byte aligned)
  - [ ] 0x01 offset (misaligned)
  - [ ] 0x02 offset (2-byte aligned)
  - [ ] 0x03 offset (misaligned)

- [ ] **アクセス権限テスト実装**
  - [ ] Read-Only レジスタの書き込み保護確認
  - [ ] Write-Only レジスタの読み出し動作確認
  - [ ] Read-Write レジスタの正常動作確認

- [ ] **テスト実行・確認**
  - [ ] コンパイル成功確認
  - [x] テスト実行・UVM_ERROR: 0 維持
  - [ ] カバレッジ改善確認: register_block_inst ≥ 45%

#### 4.1.1.3 レジスタビットフィールド個別テスト
- [ ] **ビットフィールド操作実装**
  - [ ] 制御レジスタ各ビットの個別 set/clear
  - [ ] ステータスレジスタ各ビットの状態確認
  - [ ] 予約ビット (reserved) の読み出し値確認 (常に0)
  - [ ] Read-Modify-Write 操作の整合性確認

- [ ] **レジスタ固有機能テスト**
  - [ ] UART制御レジスタの機能ビット確認
  - [ ] FIFOステータスレジスタの動的更新確認
  - [ ] 割り込み制御・ステータスレジスタの動作確認

- [ ] **テスト実行・確認**
  - [ ] コンパイル成功確認
  - [x] テスト実行・UVM_ERROR: 0 維持
  - [ ] カバレッジ改善確認: register_block_inst ≥ 65%

#### 4.1.1.4 アクセスタイミングパターンテスト
- [ ] **タイミングパターン実装**
  - [ ] Back-to-back アクセス (連続クロック)
  - [ ] Random interval アクセス (1-16クロック間隔)
  - [ ] Burst access pattern (連続アドレス)
  - [ ] 読み書き混在パターン

- [ ] **テスト実行・確認**
  - [ ] コンパイル成功確認
  - [x] テスト実行・UVM_ERROR: 0 維持 (2025-09-30, seed 12345)
  - [x] CONTROL partial readback quiet time extended (multiplier = 4, 3.6 µs hold); register_comprehensive_test returned full 4-byte payload. Waveform: `archive/waveforms/register_comprehensive_test_20250930_073435.mxd`
  - [ ] カバレッジ改善確認: register_block_inst ≥ 70%

- [ ] **Task 4.1.1 完了確認**
  - [ ] register_block_inst Toggle Coverage ≥ 65% 達成
  - [ ] 全体 Toggle Coverage ≥ 20% 達成
  - [ ] UVM_ERROR: 0 完全維持
  - [ ] 波形ファイル (.mxd) 生成確認

### 📋 Task 4.1.2: UARTプロトコルレイヤー改善

**目標**: uart_tx, uart_rx モジュール Toggle Coverage ≥ 85%  
**予想工数**: 1-2日

#### 4.1.2.1 UART送信パターン多様化
- [ ] **ファイル作成**: `sequences/uart_tx_pattern_sequence.sv`

- [ ] **送信パターン実装**
  - [ ] 特殊データパターン送信 (0x00, 0xFF, 0xAA, 0x55)
  - [ ] ランダムデータパターン送信
  - [ ] 異なるフレーム長での送信 (1-16バイト)
  - [ ] 送信FIFO満杯・空き状態での動作確認

- [ ] **テスト実行・確認**
  - [ ] コンパイル成功確認
  - [ ] テスト実行・UVM_ERROR: 0 維持
  - [ ] uart_tx モジュール Toggle Coverage ≥ 85%

#### 4.1.2.2 フレーミングエラー注入・回復テスト
- [ ] **エラー注入実装** (既存 error_injection_sequence.sv の修正)
  - [ ] ストップビット違反の注入・検出
  - [ ] スタートビット違反の注入・検出  
  - [ ] パリティエラー注入・検出 (パリティ有効時)
  - [ ] エラー発生後の正常通信回復確認

- [ ] **テスト実行・確認**
  - [ ] コンパイル成功確認 (UVMマクロエラー解決)
  - [ ] テスト実行・UVM_ERROR: 0 維持
  - [ ] uart_rx モジュール Toggle Coverage ≥ 85%

- [ ] **Task 4.1.2 完了確認**
  - [ ] uart_tx, uart_rx モジュール Toggle Coverage ≥ 85% 達成
  - [ ] UVM_ERROR: 0 完全維持

### 📋 Task 4.1.3: AXI4-Liteプロトコル境界条件テスト

**目標**: axi_internal モジュール Toggle Coverage ≥ 85%  
**予想工数**: 1-2日

#### 4.1.3.1 VALID/READYハンドシェイク全パターン
- [ ] **ファイル作成**: `sequences/axi_handshake_sequence.sv`

- [ ] **ハンドシェイクパターン実装**
  - [ ] Write Address Channel: AWVALID/AWREADY 全組み合わせ
  - [ ] Write Data Channel: WVALID/WREADY 全組み合わせ
  - [ ] Write Response Channel: BVALID/BREADY 全組み合わせ
  - [ ] Read Address Channel: ARVALID/ARREADY 全組み合わせ
  - [ ] Read Data Channel: RVALID/RREADY 全組み合わせ

- [ ] **エラーレスポンステスト**
  - [ ] AXI SLVERR レスポンス生成・処理
  - [ ] AXI DECERR レスポンス生成・処理
  - [ ] アウトスタンディング取引制限テスト

- [ ] **テスト実行・確認**
  - [ ] コンパイル成功確認
  - [ ] テスト実行・UVM_ERROR: 0 維持
  - [ ] axi_internal モジュール Toggle Coverage ≥ 85%

- [ ] **Task 4.1.3 完了確認**
  - [ ] axi_internal モジュール Toggle Coverage ≥ 85% 達成
  - [ ] UVM_ERROR: 0 完全維持

### 📋 Phase 4.1 完了確認 (1週間後)

- [ ] **カバレッジ目標達成確認**
  - [ ] 全体 Toggle Coverage ≥ 30.0% (現在14.0%から+16.0%以上向上)
  - [ ] register_block_inst Toggle Coverage ≥ 65.0%
  - [ ] UVM_ERROR: 0 完全維持

- [ ] **品質確認**
  - [ ] 高度カバレッジテスト実行: `.\run_uvm.ps1 -TestName "uart_axi4_advanced_coverage_test" -Waves:$true`
  - [ ] カバレッジレポート更新: `dcreport.exe metrics.db -out_dir coverage_report`
  - [ ] 波形ファイル生成確認
  - [ ] metrics.db サイズ ≥ 1MB 確認

---

## 🚀 Phase 4.2: Expression & Functional Coverage拡張 (2週間目標)

### 📋 Task 4.2.1: Expression Coverage最適化

**目標**: 83.3% → 90.0%  
**予想工数**: 1-2日

#### 4.2.1.1 未カバー条件分岐の特定・テスト
- [ ] **RTL解析**
  - [ ] `coverage_report/expr_*.html` ファイルで未カバー条件特定
  - [ ] Frame_Parser.sv の条件分岐解析
  - [ ] Uart_Axi4_Bridge.sv の条件分岐解析
  - [ ] Register_Block.sv の条件分岐解析

- [ ] **テストケース追加実装**
  - [ ] `sequences/expression_coverage_sequence.sv` 作成
  - [ ] 特定された未カバー条件のテストケース追加
  - [ ] 境界値・エッジケースのテスト追加

- [ ] **テスト実行・確認**
  - [ ] コンパイル成功確認
  - [ ] テスト実行・UVM_ERROR: 0 維持
  - [ ] Expression Coverage ≥ 90.0% 達成

### 📋 Task 4.3.1: Functional Coverage拡張

**目標**: 25.0% → 60.0%  
**予想工数**: 2-3日

#### 4.3.1.1 カバレッジグループ実装・拡張
- [ ] **ファイル修正**: `env/uart_axi4_coverage.sv`

- [ ] **UARTフレームカバレッジ実装**
  ```systemverilog
  covergroup uart_frame_coverage;
      frame_type: coverpoint transaction.frame_type;
      frame_size: coverpoint transaction.frame_size;
      cross frame_type, frame_size;
  endgroup
  ```

- [ ] **AXI取引カバレッジ実装**
  ```systemverilog
  covergroup axi_transaction_coverage;
      addr_alignment: coverpoint transaction.addr[1:0];
      burst_type: coverpoint transaction.burst_type;
      response_type: coverpoint transaction.response;
      cross addr_alignment, burst_type, response_type;
  endgroup
  ```

- [ ] **システム状態カバレッジ実装**
  ```systemverilog
  covergroup system_state_coverage;
      uart_state: coverpoint dut.uart_bridge_inst.current_state;
      axi_state: coverpoint dut.axi_master.current_state;
      fifo_level: coverpoint dut.rx_fifo.fill_level;
      cross uart_state, axi_state, fifo_level;
  endgroup
  ```

#### 4.3.1.2 カバレッジ収集機構実装
- [ ] **monitor統合**
  - [ ] UART monitor からのトランザクションサンプリング
  - [ ] AXI monitor からのトランザクションサンプリング
  - [ ] カバレッジグループの適切なサンプルタイミング

- [ ] **テスト実行・確認**
  - [ ] コンパイル成功確認
  - [ ] テスト実行・UVM_ERROR: 0 維持
  - [ ] Functional Coverage ≥ 60.0% 達成

### 📋 Phase 4.2 完了確認 (2週間後)

- [ ] **カバレッジ目標達成確認**
  - [ ] 全体 Toggle Coverage ≥ 50.0%
  - [ ] Expression Coverage ≥ 90.0%
  - [ ] Functional Coverage ≥ 60.0%
  - [ ] UVM_ERROR: 0 完全維持

---

## 🚀 Phase 4.3: 最終目標達成・完成 (1ヶ月目標)

### 📋 Task 4.4.1: 新機能テストシーケンス追加

**目標**: システム安定性・品質向上  
**予想工数**: 2-3日

#### 4.4.1.1 プロトコルエラー処理テスト
- [ ] **ファイル作成**: `sequences/protocol_error_test_sequence.sv`

- [ ] **エラー処理テスト実装**
  - [ ] 不正フレーム注入・破棄テスト
  - [ ] CRCエラー注入・検出・報告テスト
  - [ ] タイムアウト発生・回復テスト
  - [ ] プロトコル違反時の適切なエラーレスポンス

- [ ] **テスト実行・確認**
  - [ ] コンパイル成功確認
  - [ ] テスト実行・UVM_ERROR: 0 維持
  - [ ] システム安定性確認

### 📋 最終品質確認・完成

- [ ] **最終カバレッジ確認**
  - [ ] Toggle Coverage ≥ 75.0% 達成
  - [ ] Expression Coverage ≥ 95.0% 達成
  - [ ] Functional Coverage ≥ 80.0% 達成
  - [ ] Line Coverage 100.0% 維持

- [ ] **最終品質確認**
  - [ ] 全テストスイート実行・UVM_ERROR: 0
  - [ ] 波形ファイル生成・内容確認
  - [ ] カバレッジレポート生成・内容確認
  - [ ] ドキュメント更新完了

---

## 📊 進捗管理チェックリスト

### 日次チェックリスト
- [ ] **毎日の作業開始時**
  - [ ] DSIM環境確認
  - [ ] 前日のカバレッジ数値記録
  - [ ] 作業対象ファイルのバックアップ

- [ ] **毎日の作業終了時**
  - [ ] UVM_ERROR: 0 確認
  - [ ] カバレッジ改善確認・記録
  - [ ] 波形ファイル (.mxd) 生成確認
  - [ ] 作業ログ更新

### 週次レビューチェックリスト
- [ ] **1週間後レビュー**
  - [ ] Toggle Coverage: 14.0% → 30.0% 達成確認
  - [ ] Expression Coverage: 83.3% → 87.0% 達成確認
  - [ ] Functional Coverage: 25.0% → 40.0% 達成確認

- [ ] **2週間後レビュー**
  - [ ] Toggle Coverage: 30.0% → 50.0% 達成確認
  - [ ] Expression Coverage: 87.0% → 90.0% 達成確認
  - [ ] Functional Coverage: 40.0% → 60.0% 達成確認

- [ ] **1ヶ月後最終レビュー**
  - [ ] Toggle Coverage: 50.0% → 75.0% 達成確認
  - [ ] Expression Coverage: 90.0% → 95.0% 達成確認
  - [ ] Functional Coverage: 60.0% → 80.0% 達成確認

---

## 🎯 成功基準・完了条件

### 技術品質基準 (必須)
- [ ] **UVM_ERROR: 0** (絶対条件・全期間維持)
- [ ] **コンパイル・リンクエラー: 0**
- [ ] **timescale統一維持** (`timescale 1ns / 1ps`)
- [ ] **SystemVerilogコーディング規約準拠**

### カバレッジ品質基準 (目標)
- [ ] **Toggle Coverage ≥ 75.0%** (現在14.0%から+61.0%以上向上)
- [ ] **Expression Coverage ≥ 95.0%** (現在83.3%から+11.7%以上向上)
- [ ] **Functional Coverage ≥ 80.0%** (現在25.0%から+55.0%以上向上)
- [ ] **Line Coverage 100.0%** (完全維持)

### プロジェクト完了条件
- [ ] **全カバレッジ目標達成**
- [ ] **包括的テストスイート完成**
- [ ] **ドキュメント更新完了**
- [ ] **次作業者への完全な引き継ぎ完了**

---

*SystemVerilog検証エンジニアとして、このチェックリストに従い、段階的で確実なカバレッジ向上を達成します。* 🏆  
*品質至上主義と継続改善の精神で、測定可能で持続可能な改善を実現します。* 🚀