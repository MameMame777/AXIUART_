# AXIUARTプロジェクト - Claude-4作業指示プロンプト
## 最終更新: 2025年9月20日
## プロジェクト段階: 品質向上・安定化フェーズ (Phase 1)

---

## 🎯 **Claude-4への作業依頼指示**

### **前提情報**
あなたは、AXIUARTプロジェクトの改善作業を担当するSystemVerilog・UVM検証の専門家です。本プロジェクトは、UART-AXI4ブリッジシステムの基盤構築が完成し、現在は品質向上と安定化に集中する重要な段階にあります。

**プロジェクト現状**:
- **RTL実装品質**: 90/100 (軽微な警告解決が必要)
- **検証環境成熟度**: 80/100 (機能カバレッジ向上が急務)
- **ドキュメント完成度**: 90/100 (優秀)
- **総合評価**: 85/100 (プロダクション準備完了レベル)

**コミット状況**: `87f8733` - UVMテンプレート追加完了
**詳細分析**: `docs/project_status_analysis_20250920.md` 参照

---

## 🔴 **Phase 1: 最優先改善作業 (品質向上・安定化)**

### **作業1: RTL品質問題解決** 🚨 **最高優先度**

**目標**: RTLコードの全警告を解決し、商用品質レベル達成

**具体的作業内容**:
```systemverilog
// 1. タイムスケール統一問題解決
// 現在の問題: UVMパッケージ (タイムスケールなし) とRTL (1ns/1ps) の不整合
// 解決方法: 全RTLファイルでタイムスケール仕様を統一

// 2. ラッチ推定警告解決 (以下4ファイル)
// a) rtl/Crc8_Calculator.sv:22 - crc_temp信号
always_comb begin
    crc_temp = 8'h00;  // 初期値設定必要
    // 全条件分岐での値定義を完全化
end

// b) rtl/Uart_Tx.sv:122 - uart_tx_int信号
always_comb begin
    uart_tx_int = 1'b1;  // デフォルト値設定
    // 全ケースでの値割り当て確保
end

// c) rtl/Frame_Parser.sv:329 - data_out信号
always_comb begin
    data_out = 32'h0000_0000;  // 初期値必須
    // 全パス定義の完全化
end

// d) rtl/Uart_Axi4_Bridge.sv:242,258 - 複数信号
// 全コンビネーションロジックでのデフォルト値設定
```

**品質基準**:
- 全DSIMコンパイル警告ゼロ化
- SystemVerilog LRMコンプライアンス100%達成
- 論理合成可能な清潔なRTLコード実現

**検証要件**:
- DSIMでの警告なしコンパイル確認
- 既存テスト (`axiuart_system_test`) 正常実行維持
- 波形レベルでの機能確認実施

---

### **作業2: UVM機能カバレッジ向上** 🚨 **最高優先度**

**目標**: 機能カバレッジ 0.00% → 80%以上達成

**現在の問題**:
```
UVM_INFO: Frame coverage: 0.00%
UVM_INFO: Burst coverage: 0.00%  
UVM_INFO: Error coverage: 0.00%
UVM_INFO: Total coverage: 0.00%
```

**具体的作業内容**:

#### 2-1. **実際のUART通信シーケンス実装**
```systemverilog
// sim/uvm/sequences/uart_protocol_active_sequence.sv - 新規作成
class uart_protocol_active_sequence extends uvm_sequence;
    // 実際のUARTフレーム送信シーケンス
    task body();
        // 1. UART Writeコマンド送信 (0x57 + アドレス + データ + CRC)
        // 2. UART Readコマンド送信 (0x52 + アドレス + CRC) 
        // 3. UARTレスポンス受信・検証
        // 4. AXI4-Liteトランザクション監視・検証
    endtask
endclass
```

#### 2-2. **カバレッジポイント活性化**
```systemverilog
// sim/uvm/env/uart_axi4_coverage.sv - 修正
covergroup uart_frame_coverage;
    // UARTコマンドタイプカバレッジ
    cp_command_type: coverpoint uart_command {
        bins write_cmd = {8'h57};
        bins read_cmd = {8'h52};
        bins invalid_cmd = {[0:255]} iff (uart_command != 8'h57 && uart_command != 8'h52);
    }
    
    // アドレス範囲カバレッジ  
    cp_address: coverpoint axi_address {
        bins reg_space = {[32'h0000_1000:32'h0000_1FFF]};
        bins invalid_space = default;
    }
    
    // データパターンカバレッジ
    cp_data_pattern: coverpoint axi_data {
        bins zero = {32'h0000_0000};
        bins ones = {32'hFFFF_FFFF};
        bins pattern = {[1:32'hFFFF_FFFE]};
    }
endgroup
```

#### 2-3. **エラー注入テストシーケンス**
```systemverilog
// sim/uvm/sequences/error_injection_sequence.sv - 機能化
class error_injection_sequence extends uvm_sequence;
    task body();
        // CRCエラー注入テスト
        // 不正アドレス範囲テスト  
        // タイムアウト条件テスト
        // FIFOオーバーフロー/アンダーフローテスト
    endtask
endclass
```

**検証要件**:
- 機能カバレッジ80%以上達成
- 全カバレッジポイント活性化確認
- DSIMカバレッジレポート生成・検証

---

### **作業3: プロトコル検証強化** 🟡 **高優先度**

**目標**: UART-AXI4変換プロトコルの完全検証実現

**具体的作業内容**:

#### 3-1. **トランザクションレベル監視強化**
```systemverilog
// sim/uvm/env/uart_axi4_predictor.sv - 機能拡張
class uart_axi4_predictor extends uvm_predictor;
    // UARTフレーム→AXI4トランザクション予測
    function void write(uart_frame_transaction t);
        axi4_lite_transaction predicted_axi;
        
        // 1. UARTコマンド解析
        // 2. AXI4アドレス・データ予測
        // 3. 期待レスポンス生成
        // 4. タイミング制約チェック
        
        ap.write(predicted_axi);
    endfunction
endclass
```

#### 3-2. **スコアボード精度向上**
```systemverilog
// sim/uvm/env/uart_axi4_scoreboard.sv - 改良
class uart_axi4_scoreboard extends uvm_scoreboard;
    // 厳密なトランザクションマッチング
    function void check_transaction(uart_frame_transaction uart_trans, 
                                  axi4_lite_transaction axi_trans);
        // 1. アドレス変換正確性チェック
        // 2. データ整合性検証
        // 3. レスポンス時間制約確認
        // 4. エラーコード整合性確認
    endfunction
endclass
```

**品質基準**:
- UART-AXI変換正確性100%確認
- プロトコルタイミング制約遵守確認
- エラーケース完全カバレッジ達成

---

## 🟡 **Phase 2: 機能拡張作業 (中期優先度)**

### **作業4: 高度プロトコル機能実装**

**4-1. フロー制御実装**
```systemverilog
// rtl/Uart_Flow_Control.sv - 新規作成予定
module Uart_Flow_Control (
    input  logic clk,
    input  logic rst,
    input  logic cts_n,      // Clear To Send
    output logic rts_n,      // Request To Send
    // FIFO制御インターフェース
);
```

**4-2. 自動再送機能**
```systemverilog
// rtl/Error_Recovery.sv - 新規作成予定  
module Error_Recovery (
    // CRCエラー検出時の自動再送制御
    // タイムアウト時の再試行制御
);
```

### **作業5: 性能最適化**

**5-1. 高速ボーレート対応**
- 921600bps対応実装
- クロックドメイン最適化
- タイミング制約強化

**5-2. レイテンシ削減**
- パイプライン処理改善
- FIFOバッファ最適化

---

## 🟢 **Phase 3: エコシステム構築 (長期優先度)**

### **作業6: FPGA実装対応**
### **作業7: CI/CD環境構築** 
### **作業8: 商用化準備**

---

## 📋 **作業実行時の品質基準**

### **🔴 必須要件 (違反時は作業やり直し)**
1. **コンパイルクリーン**: DSIMでの警告・エラーゼロ
2. **既存テスト保護**: 全既存テストケースの正常動作維持
3. **コーディング標準遵守**: `.github/copilot-instructions.md`完全準拠
4. **ドキュメント更新**: 変更内容の完全ドキュメント化

### **🟡 推奨品質基準**
1. **カバレッジ目標**: 機能カバレッジ80%以上
2. **パフォーマンス**: テスト実行時間20秒以内維持
3. **可読性**: 十分なコメント・説明追加
4. **再利用性**: モジュラー設計の維持

### **🟢 理想品質基準**  
1. **業界標準準拠**: SystemVerilog LRM/UVM標準100%準拠
2. **商用品質**: プロダクション環境で使用可能なレベル
3. **保守性**: 他の開発者が容易に理解・拡張可能

---

## 🚀 **作業開始時のチェックリスト**

### **事前確認 (作業開始前)**
- [ ] 最新コミット状況確認 (`git log --oneline -5`)
- [ ] 現在の動作状況確認 (`cd sim/uvm && .\run_uvm.ps1 -test axiuart_system_test`)
- [ ] プロジェクト状況レポート読了 (`docs/project_status_analysis_20250920.md`)
- [ ] 作業対象ファイルのバックアップ作成

### **作業中確認**
- [ ] DSIMコンパイル警告監視
- [ ] 既存テスト実行状況確認
- [ ] Git コミット準備 (適切なコミットメッセージ)

### **作業完了確認**
- [ ] 全DSIMコンパイル警告解決確認
- [ ] `axiuart_system_test` 正常実行確認
- [ ] カバレッジレポート生成・確認 (`coverage_report/index.html`)
- [ ] ドキュメント更新完了確認
- [ ] 品質基準達成確認

---

## 💡 **Claude-4への期待事項**

1. **品質への妥協なし**: 警告・エラーは完全解決まで継続
2. **説明責任**: 変更理由・影響範囲の明確な説明
3. **段階的アプローチ**: 大きな変更は小さなステップに分割
4. **後方互換性**: 既存機能への影響最小化
5. **プロフェッショナル水準**: 商用開発と同等の品質基準維持

**期待成果**: AXIUARTプロジェクトが世界クラスのオープンソースIPコアとして成長するための確固たる技術的基盤確立

---
## 🔍 Supplemental Execution & Governance Guidelines (English)

The following additions formalize objective quality gates, workflow discipline, and measurable exit criteria to prevent ambiguity and regression during Phase 1 and beyond. They do not replace the Japanese core instructions above; they refine enforceable expectations.

### 1. Quality Gates & Pass/Fail Metrics

| Category | Metric | Phase 1 Gate | Measurement Method | Failure Action |
|----------|--------|--------------|--------------------|----------------|
| RTL Compile | DSIM warnings | 0 | `run_uvm.ps1 -mode compile` log parse | Block merge |
| Lint (future) | Structural issues | ≤ Minor only | External lint tool (planned) | Create fix ticket |
| Functional Tests | `axiuart_system_test` | 100% pass | DSIM exit code / UVM report | Immediate rollback |
| Functional Coverage | Frame/Burst/Error groups | ≥ 80% | `coverage_report/` summary | Add targeted sequences |
| Code Coverage (optional later) | Line/Toggle | Informational (≥60%) | DSIM metrics | Identify dead code |
| Performance | Test runtime | ≤ 20 s per regression | Timestamp diff | Optimize / waveform scope reduction |
| Documentation | Changed areas updated | 100% | Diff review | Block merge |
| Version Tag (Phase exit) | Phase 1 release tag | `v1.0.0-rc1` | Git annotated tag | Delay release |

### 2. Timescale & Coding Compliance

All SystemVerilog sources (RTL, interfaces, testbench, UVM components) must begin with exactly: `` `timescale 1ns / 1ps `` (spacing preserved). Non‑conforming files: add or fix. Mixed timescales are prohibited (reason: simulation determinism, delta cycles alignment). Any new module must include header comment: purpose, interface summary, reset behavior, assumptions.

### 3. Environment Variable Validation (DSIM)

Mandatory variables before any run:

```text
DSIM_HOME
DSIM_ROOT (may equal DSIM_HOME)
DSIM_LIB_PATH
DSIM_LICENSE (if required)
```

The PowerShell runners must abort with a clear message if any are unset. Add a function `Assert-EnvVar($name)` used uniformly. No hard‑coded absolute paths.

### 4. Branch & Commit Strategy

| Branch | Purpose | Naming Pattern |
|--------|---------|----------------|
| `main` | Stable, tagged releases | N/A |
| `develop` (optional future) | Integration of completed Phase feature sets | N/A |
| Feature | Isolated change set | `feat/<scope>-<short-desc>` |
| Fix | Bug / warning removal | `fix/<area>-<issue>` |
| Verification | Testbench/coverage work | `verif/<component>-<goal>` |

Commit message format:

```text
<type>(<scope>): <concise imperative>

Body: Rationale, impact, references (issue #, doc section).
Footer: BREAKING CHANGE: <details> (if any)
```

Types: `feat`, `fix`, `verif`, `docs`, `refactor`, `perf`, `chore`.

### 5. Change Control Workflow

1. Open tracking issue (Problem statement + acceptance criteria + links to spec/register map).
2. Create branch.
3. Add/update tests FIRST if behavior change.
4. Implement minimal RTL/UVM deltas (avoid unrelated formatting drift).
5. Run local quality gate script (future automation placeholder).
6. Submit PR with: summary, risk assessment, test evidence (log excerpt), coverage delta, checklist.
7. Require review from both RTL and Verification roles (temporarily same engineer if solo—still document both perspectives).
8. Merge only when all gates green.

### 6. Risk & Issue Log (Lightweight)

Maintain a table in `docs/project_status_analysis_*.md` with columns: ID | Date | Category (RTL/UVM/Process) | Description | Impact | Mitigation | Status. Update on every material discovery (e.g., timing assumption violation, coverage blind spot, protocol ambiguity).

### 7. Coverage Methodology Details

Phased activation:

1. Structural collection: instantiate covergroups only after DUT reset deassertion.
2. Sampling policy: explicit `sample()` after each complete UART frame decode and AXI response handshake; avoid implicit clocked sampling to prevent noise.
3. Exclusions: Document any ignored bins in `uvm_verification_review_report.md` with justification (e.g., reserved command codes not generated by protocol).
4. Gap closure loop: (a) Generate coverage report (b) Identify 0-hit bins (c) Design micro-sequence targeting only missing cross/bins (d) Re-run incremental simulation.
5. Exit criterion: No unhit bin without an explicit written waiver.

Recommended additional coverpoints (future): CRC error classification, FIFO occupancy levels (empty / low / high / full), AXI response types (OKAY vs error), inter-frame idle cycle distribution.

### 8. Acceptance Criteria (Phase 1 Completion)

| Area | Criterion | Evidence Source |
|------|----------|-----------------|
| RTL Warnings | Zero | DSIM compile log |
| Latch Inference | Zero unintended | Synthesis lint (planned) + code review |
| Coverage | ≥80% functional | Coverage HTML summary |
| Protocol Accuracy | 100% scoreboarding pass | UVM scoreboard report |
| Docs | Updated & consistent | Git diff + review |
| Repeatability | One-command regression | `run_uvm.ps1` output |
| Waveform Availability | MXD generated per test | `.mxd` files in `sim/uvm` |

### 9. Regression Execution Modes

Provide at minimum:

```pwsh
./run_uvm.ps1 -test axiuart_system_test -seed <n>
./run_uvm.ps1 -test uart_axi4_basic_test -cov enable
```

Add option `-fast` to disable waveform dumping for performance runs (future enhancement). Default remains waveform ON for debug transparency.

### 10. Performance & Resource Discipline

Waveform scope trimming guideline: include DUT hierarchy + interface signals + scoreboard predictive paths; exclude large constant nets. If runtime > 20 s sustained, first action: reduce waveform footprint before altering stimulus pacing.

### 11. Documentation Synchronization Rule

For any RTL register map change: mandatory updates to `register_map.md`, relevant sequence comments, and predictor/scoreboard expectation logic. PR rejected if mismatch found.

### 12. Future Automation Hooks (Planned)

Placeholder scripts to be added under `scripts/`:

- `quality_gate.ps1` (aggregates compile status, coverage extraction, runtime, doc freshness).
- `report_delta.ps1` (summarizes coverage bin deltas between two metrics.db snapshots).

### 13. Waiver Policy

Any deviation (e.g., temporarily reduced coverage due to refactor) requires a dated waiver entry containing: reason, scope, planned removal date. Store in `docs/waivers.md` (create when first needed). Expired waivers cause PR block until resolved.

### 14. Security & Integrity Notes

Avoid inclusion of proprietary IP; verify all third-party PDFs in `reference/` have redistribution rights. No hard-coded license keys in scripts. Environment validation must not echo license contents—only presence.

