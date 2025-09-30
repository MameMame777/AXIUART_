# 🎯 AXIUART_ カバレッジ向上 詳細作業計画書

**作成日**: 2025年9月28日  
**対象プロジェクト**: AXIUART_ UART-AXI4 Lite Bridge System  
**現在のカバレッジ基準**: Line 100.0%, Toggle 14.0%, Expression 83.3%, Functional 25.0%

---

## 📊 現状分析と改善目標

### 現在のカバレッジ詳細分析

| モジュール | Toggle Coverage | 改善優先度 | 主な改善機会 |
|------------|-----------------|------------|--------------|
| **register_block_inst** | 13.7% | 🔴 最高 | レジスタアクセスパターン網羅 |
| **uart_axi4_tb_top.dut** | 14.0% | 🔴 高 | 全体統合テスト強化 |
| **axi_internal** | 75.0% | 🟡 中 | AXI プロトコル境界条件 |
| **uart_bridge_inst** | 62.5% | 🟡 中 | ブリッジロジック強化 |
| **他のモジュール** | 75.0%+ | 🟢 低 | 維持・微調整 |

### 目標設定

| カバレッジ種別 | 現在値 | 短期目標(1週間) | 中期目標(2週間) | 長期目標(1ヶ月) |
|----------------|--------|-----------------|-----------------|-----------------|
| **Toggle Coverage** | 14.0% | 30.0% | 50.0% | 75.0% |
| **Expression Coverage** | 83.3% | 87.0% | 90.0% | 95.0% |
| **Functional Coverage** | 25.0% | 40.0% | 60.0% | 80.0% |
| **Line Coverage** | 100.0% | 100.0% | 100.0% | 100.0% |

---

## 🚀 Phase 4 詳細実装計画

### 4.1 Toggle Coverage向上 (目標: 14.0%→50.0%)

#### タスク 4.1.1: register_block_inst 改善 (最優先)
**現在**: 13.7%  
**目標**: 75.0%  
**予想工数**: 2-3日  

**細分化タスク**:
- [ ] **4.1.1.1** レジスタマップ全アドレス範囲テスト実装
  ```systemverilog
  // sequences/register_comprehensive_sequence.sv
  class register_comprehensive_access_sequence extends uart_frame_sequence;
      // 全レジスタアドレス 0x1000-0x1FFF の網羅的アクセス
  ```

- [ ] **4.1.1.2** 読み書きパターン全組み合わせテスト
  ```systemverilog
  // 8-bit, 16-bit, 32-bit アクセスの全パターン
  // アライメント: aligned, misaligned cases
  ```

- [ ] **4.1.1.3** レジスタビットフィールド個別テスト
  ```systemverilog
  // 各レジスタの全ビットに対する set/clear テスト
  // 特殊機能レジスタ（ステータス、制御）の状態遷移テスト
  ```

- [ ] **4.1.1.4** レジスタアクセスタイミングパターンテスト
  ```systemverilog
  // Back-to-back アクセス
  // Random interval アクセス
  // Burst アクセスパターン
  ```

**成功基準**: register_block_inst Toggle Coverage ≥ 65%

#### タスク 4.1.2: UARTプロトコルレイヤー改善
**予想工数**: 1-2日

**細分化タスク**:
- [ ] **4.1.2.1** UART送信パターンの多様化
- [ ] **4.1.2.2** フレーミングエラー注入・回復テスト
- [ ] **4.1.2.3** CRC エラーパターン網羅
- [ ] **4.1.2.4** タイムアウト・再送ロジックテスト

#### タスク 4.1.3: AXI4-Liteプロトコル境界条件テスト
**予想工数**: 1-2日

**細分化タスク**:
- [ ] **4.1.3.1** AXI VALID/READY ハンドシェイク全パターン
- [ ] **4.1.3.2** AXI エラーレスポンス生成・処理
- [ ] **4.1.3.3** AXI アウトスタンディング取引制限テスト
- [ ] **4.1.3.4** AXI アドレス境界・プロテクション違反テスト

### 4.2 Expression Coverage最適化 (目標: 83.3%→90.0%)

#### タスク 4.2.1: 条件分岐全組み合わせテスト
**予想工数**: 1日

**細分化タスク**:
- [ ] **4.2.1.1** if-else文の全ブランチカバレッジ確認
- [ ] **4.2.1.2** case文の全ケース＋default確認
- [ ] **4.2.1.3** 三項演算子の全パス確認
- [ ] **4.2.1.4** 複合条件式の全組み合わせ確認

#### タスク 4.2.2: エラー条件の網羅的テスト
**予想工数**: 1-2日

**細分化タスク**:
- [ ] **4.2.2.1** UART受信エラー（パリティ、フレーミング、オーバーラン）
- [ ] **4.2.2.2** FIFO オーバーフロー・アンダーフロー
- [ ] **4.2.2.3** CRC計算・検証エラー
- [ ] **4.2.2.4** AXI プロトコル違反エラー

### 4.3 Functional Coverage拡張 (目標: 25.0%→60.0%)

#### タスク 4.3.1: プロトコルレベルカバレッジ実装
**予想工数**: 2-3日

**細分化タスク**:
- [ ] **4.3.1.1** UARTフレームフォーマットカバレッジグループ実装
  ```systemverilog
  covergroup uart_frame_coverage;
      frame_type: coverpoint transaction.frame_type {
          bins sof = {FRAME_SOF};
          bins data = {FRAME_DATA};
          bins status = {FRAME_STATUS};
      }
      frame_size: coverpoint transaction.frame_size {
          bins small = {[1:4]};
          bins medium = {[5:8]};
          bins large = {[9:16]};
      }
      cross frame_type, frame_size;
  endgroup
  ```

- [ ] **4.3.1.2** AXI4-Lite取引パターンカバレッジ
  ```systemverilog
  covergroup axi_transaction_coverage;
      addr_alignment: coverpoint transaction.addr[1:0] {
          bins aligned = {2'b00};
          bins misaligned = {2'b01, 2'b10, 2'b11};
      }
      burst_type: coverpoint transaction.burst_type;
      response_type: coverpoint transaction.response;
      cross addr_alignment, burst_type, response_type;
  endgroup
  ```

- [ ] **4.3.1.3** システムレベル状態遷移カバレッジ
  ```systemverilog
  covergroup system_state_coverage;
      uart_state: coverpoint dut.uart_bridge_inst.current_state;
      axi_state: coverpoint dut.axi_master.current_state;
      fifo_level: coverpoint dut.rx_fifo.fill_level {
          bins empty = {0};
          bins low = {[1:16]};
          bins medium = {[17:48]};
          bins high = {[49:63]};
          bins full = {64};
      }
      cross uart_state, axi_state, fifo_level;
  endgroup
  ```

#### タスク 4.3.2: バーストアクセスパターンカバレッジ
**予想工数**: 1-2日

**細分化タスク**:
- [ ] **4.3.2.1** 単発アクセスパターン
- [ ] **4.3.2.2** 連続アクセスパターン（アドレス連続）
- [ ] **4.3.2.3** ランダムアクセスパターン
- [ ] **4.3.2.4** 混合アクセスパターン（読み書き混在）

### 4.4 新機能テストシーケンス追加

#### タスク 4.4.1: プロトコルエラー処理テスト
**予想工数**: 2日

**細分化タスク**:
- [ ] **4.4.1.1** 不正フレーム検出・破棄テスト
- [ ] **4.4.1.2** CRCエラー検出・報告テスト
- [ ] **4.4.1.3** タイムアウト検出・回復テスト
- [ ] **4.4.1.4** プロトコル違反時の適切なエラーレスポンス

---

## 📋 実装チェックリスト

### 環境準備チェックリスト

- [ ] **作業前確認**
  - [ ] DSIM環境変数設定確認 (DSIM_HOME, DSIM_LIB_PATH, DSIM_ROOT)
  - [ ] プロジェクトファイル整合性確認 (dsim_config.f, run_uvm.ps1)
  - [ ] ベースラインカバレッジ記録 (現在: Toggle 14.0%, Expression 83.3%, Functional 25.0%)

- [ ] **開発環境設定**
  - [ ] VSCode + SystemVerilog拡張機能
  - [ ] PowerShell 実行環境
  - [ ] MXD波形ビューア準備

### Phase 4.1 実装チェックリスト (Toggle Coverage改善)

#### 4.1.1 register_block_inst 改善
- [ ] **4.1.1.1 レジスタマップ全アドレス範囲テスト**
  - [ ] sequences/register_comprehensive_sequence.sv 作成
  - [ ] 全レジスタアドレス範囲 0x1000-0x1FFF のアクセステスト実装
  - [ ] アドレスデコーダー全パス動作確認
  - [ ] 無効アドレスアクセス時のエラーハンドリング確認

- [ ] **4.1.1.2 読み書きパターン全組み合わせ**
  - [ ] 8-bit (size=2'b00) アクセステスト
  - [ ] 16-bit (size=2'b01) アクセステスト
  - [ ] 32-bit (size=2'b10) アクセステスト
  - [ ] アライメント条件: 0x00, 0x01, 0x02, 0x03 offset
  - [ ] 読み出し専用レジスタの書き込み保護確認
  - [ ] 書き込み専用レジスタの読み出し動作確認

- [ ] **4.1.1.3 レジスタビットフィールド個別テスト**
  - [ ] 制御レジスタ各ビットのset/clear動作
  - [ ] ステータスレジスタ各ビットの正しい反映
  - [ ] 予約ビットの読み出し値確認 (常に0)
  - [ ] Read-Modify-Write動作の整合性確認

- [ ] **4.1.1.4 アクセスタイミングパターン**
  - [ ] Back-to-backアクセス (連続クロック)
  - [ ] Random intervalアクセス (1-16クロック間隔)
  - [ ] Burst access pattern (アドレス連続)
  - [ ] 読み書き混在パターン

- [ ] **実装確認・テスト**
  - [ ] register_comprehensive_sequence コンパイル成功
  - [ ] tests/uart_axi4_register_comprehensive_test.sv 作成
  - [ ] テスト実行: UVM_ERROR: 0 維持
  - [ ] カバレッジ確認: register_block_inst Toggle Coverage ≥ 50%

#### 4.1.2 UARTプロトコルレイヤー改善
- [ ] **4.1.2.1 UART送信パターン多様化**
  - [ ] sequences/uart_tx_pattern_sequence.sv 作成
  - [ ] 異なるデータパターン (0x00, 0xFF, 0xAA, 0x55, random) 送信
  - [ ] 異なるフレーム長 (1-16バイト) での送信テスト
  - [ ] 送信FIFO満杯・空き状態での動作確認

- [ ] **4.1.2.2 フレーミングエラー注入・回復**
  - [ ] sequences/uart_error_injection_sequence.sv 修正
  - [ ] ストップビット違反の注入・検出
  - [ ] スタートビット違反の注入・検出
  - [ ] エラー発生後の正常通信回復確認

- [ ] **実装確認・テスト**
  - [ ] UART関連シーケンス コンパイル成功
  - [ ] UVM_ERROR: 0 維持
  - [ ] uart_tx, uart_rx モジュール Toggle Coverage ≥ 80%

#### 4.1.3 AXI4-Liteプロトコル境界条件
- [ ] **4.1.3.1 VALID/READYハンドシェイク全パターン**
  - [ ] sequences/axi_handshake_sequence.sv 作成
  - [ ] AWVALID/AWREADY の全組み合わせ
  - [ ] WVALID/WREADY の全組み合わせ
  - [ ] BVALID/BREADY の全組み合わせ
  - [ ] ARVALID/ARREADY の全組み合わせ
  - [ ] RVALID/RREADY の全組み合わせ

- [ ] **実装確認・テスト**
  - [ ] AXI4-Lite関連シーケンス コンパイル成功
  - [ ] axi_internal モジュール Toggle Coverage ≥ 85%

### Phase 4.2 実装チェックリスト (Expression Coverage改善)

#### 4.2.1 条件分岐全組み合わせテスト
- [ ] **RTL条件分岐解析**
  - [ ] Frame_Parser.sv の条件分岐解析
  - [ ] Uart_Axi4_Bridge.sv の条件分岐解析
  - [ ] Register_Block.sv の条件分岐解析
  - [ ] 未カバー条件の特定

- [ ] **テストケース実装**
  - [ ] sequences/expression_coverage_sequence.sv 作成
  - [ ] 特定された未カバー条件のテストケース追加
  - [ ] 境界値・エッジケースのテスト追加

- [ ] **実装確認・テスト**
  - [ ] Expression Coverage ≥ 87%達成
  - [ ] UVM_ERROR: 0 維持

### Phase 4.3 実装チェックリスト (Functional Coverage拡張)

#### 4.3.1 プロトコルレベルカバレッジ実装
- [ ] **カバレッジグループ実装**
  - [ ] env/uart_axi4_coverage.sv にカバレッジグループ追加
  - [ ] uart_frame_coverage 実装・インスタンス化
  - [ ] axi_transaction_coverage 実装・インスタンス化
  - [ ] system_state_coverage 実装・インスタンス化

- [ ] **カバレッジ収集機構**
  - [ ] monitor からのトランザクションサンプリング実装
  - [ ] カバレッジグループの適切なサンプルタイミング
  - [ ] カバレッジデータのレポート出力

- [ ] **実装確認・テスト**
  - [ ] Functional Coverage ≥ 40%達成
  - [ ] カバレッジグループ全て正常動作
  - [ ] UVM_ERROR: 0 維持

### Phase 4.4 実装チェックリスト (新機能テストシーケンス)

#### 4.4.1 プロトコルエラー処理テスト
- [ ] **エラー処理テストシーケンス**
  - [ ] sequences/protocol_error_test_sequence.sv 作成
  - [ ] 不正フレーム注入テスト
  - [ ] CRCエラー注入・検出テスト
  - [ ] タイムアウト発生・回復テスト

- [ ] **実装確認・テスト**
  - [ ] エラー処理の適切な動作確認
  - [ ] システム安定性維持確認
  - [ ] UVM_ERROR: 0 維持

---

## 📊 進捗管理・品質保証

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

### 週次レビューポイント
- [ ] **Toggle Coverage目標達成確認**
  - [ ] 週間目標: 14.0% → 30.0%
  - [ ] register_block_inst: 13.7% → 65.0%

- [ ] **Expression Coverage目標達成確認**
  - [ ] 週間目標: 83.3% → 87.0%

- [ ] **Functional Coverage目標達成確認**
  - [ ] 週間目標: 25.0% → 40.0%

### 品質保証基準
- [ ] **技術品質維持**
  - [ ] UVM_ERROR: 0 (絶対条件)
  - [ ] コンパイル・リンクエラー: 0
  - [ ] timescale統一維持
  - [ ] SystemVerilogコーディング規約準拠

- [ ] **カバレッジ品質**
  - [ ] 意図的なカバレッジ向上 (テストケース追加による)
  - [ ] 無意味なカバレッジ稼ぎの排除
  - [ ] カバレッジホール分析・対策実施

---

## 🎯 成功基準・完了条件

### 短期成功基準 (1週間後)
- ✅ **Toggle Coverage ≥ 30.0%** (現在14.0%から+16.0%以上向上)
- ✅ **Expression Coverage ≥ 87.0%** (現在83.3%から+3.7%以上向上)  
- ✅ **Functional Coverage ≥ 40.0%** (現在25.0%から+15.0%以上向上)
- ✅ **UVM_ERROR: 0 完全維持**

### 中期成功基準 (2週間後)
- ✅ **Toggle Coverage ≥ 50.0%**
- ✅ **Expression Coverage ≥ 90.0%**
- ✅ **Functional Coverage ≥ 60.0%**
- ✅ **register_block_inst Toggle Coverage ≥ 65.0%**

### 長期成功基準 (1ヶ月後)
- ✅ **Toggle Coverage ≥ 75.0%** (目標値達成)
- ✅ **Expression Coverage ≥ 95.0%** (目標値超過)
- ✅ **Functional Coverage ≥ 80.0%** (目標値達成)
- ✅ **全モジュール Toggle Coverage ≥ 65.0%**

### プロジェクト完了条件
- [ ] 全カバレッジ目標達成
- [ ] 包括的テストスイート完成
- [ ] ドキュメント更新完了
- [ ] 次作業者への完全な引き継ぎ完了

---

## 📚 参考資料・技術リソース

### プロジェクト内部資料
- `docs/comprehensive_work_instructions.md` - 基本作業指示書
- `docs/design_overview.md` - システム設計概要  
- `docs/register_map.md` - レジスタマップ詳細
- `docs/uart_axi4_protocol.md` - プロトコル仕様

### 外部技術資料
- [UVM 1.2 User Guide](IEEE 1800.2-2017) - UVM基本概念・API
- [DSIM User Manual](https://help.metrics.ca/) - DSIM特有機能・オプション
- [SystemVerilog LRM](IEEE 1800-2017) - SystemVerilog言語仕様
- [AMBA AXI4-Lite Specification](ARM) - AXI4-Liteプロトコル詳細

### 開発環境・ツール
- **シミュレータ**: Metrics Design Automation DSIM v20240422.0.0
- **カバレッジツール**: DSIM内蔵カバレッジ機能
- **波形ビューア**: DSIM MXD形式サポートビューア
- **開発環境**: VSCode + SystemVerilog拡張機能

---

*SystemVerilog検証エンジニアとして、品質至上主義と継続改善の精神でカバレッジ向上を達成します。*  
*段階的アプローチと詳細なチェックリストにより、確実で測定可能な改善を実現します。* 🏆