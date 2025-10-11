# AXIUART プロジェクトクリーンアップ・品質保証作業指示書

**最終更新**: 2025年10月11日  
**対象**: AXIUART UVM検証プロジェクト  
**基準文書**: uvm_verification_quality_assurance_instructions_20251010.md  
**Phase**: Phase 3完了後のクリーンアップ・Phase 4準備

---

## 🎯 **プロジェクト現状分析結果**

### ✅ 検証環境動作状況 (Phase 3完了確認)

**実行確認済み (2025-10-11 19:42)**:
- **コンパイル**: 成功 (警告のみ、エラーなし)  
- **シミュレーション**: 正常実行 (UVM_ERROR = 0)
- **Enhanced Reporting**: 動作確認済み
- **Phase 3 Scoreboard**: 正常動作
- **カバレッジ**: Frame 19.44%, Total 32.52%
- **波形生成**: MXD形式で正常生成

**検証環境は安定稼働中** - クリーンアップ作業実行可能

### 📊 プロジェクト混乱要因分析

#### **問題の特定**

1. **文書数の異常な多さ**: docs/ディレクトリに**120+個**のMarkdownファイル
2. **日記ファイルの乱立**: 32個の日記ファイル (2025年9-10月)
3. **完了レポートの重複**: 19個の"completion"関連ファイル
4. **作業指示書の複数バージョン**: 12個の"work_instructions"系ファイル
5. **古い波形ファイルの蓄積**: 22個のMXDファイル (最古: 2025-10-10)

#### **品質への影響**

- **情報検索困難**: 関連文書を見つけるのに時間がかかる
- **重複作業リスク**: 似た名前のファイルによる混乱
- **ディスク容量圧迫**: 不要ファイルによる容量消費
- **バージョン管理混乱**: 最新の情報が不明確

---

## 🚀 **Phase 4品質保証重視クリーンアップ戦略**

### **基本方針**

1. **検証環境完全保護**: Phase 3の成果を確実に保護
2. **段階的安全削除**: バックアップ確保後の慎重な削除
3. **品質向上優先**: Phase 4準備に必要な情報のみ保持
4. **トレーサビリティ確保**: 削除ファイルの記録保持

### **保護対象 (絶対削除禁止)**

```
【UVM検証環境コア】
- sim/uvm/ (全体)
- rtl/ (全体)  
- run_uvm.ps1
- enhanced_uart_axi4_base_test.sv

【最新品質保証関連】
- uvm_verification_quality_assurance_instructions_20251010.md
- project_uvm_reporting_guidelines.md
- uvm_verification_quality_assessment_report_20251011.md

【システム設定】
- dsim.env
- .gitignore
- README.md
```

---

## 📋 **クリーンアップ実行計画**

### **Stage 1: バックアップ・安全確保 (優先度: 最高)**

#### **実行タスク**

1. **現在の状態を完全保存**
```powershell
# Git commitで現在の状態を保存
git add -A
git commit -m "Backup before cleanup: Phase 3 complete state (2025-10-11)"

# 重要ファイルのバックアップ作成
New-Item -Path "E:\Nautilus\workspace\fpgawork\AXIUART_\backup_20251011" -ItemType Directory
Copy-Item -Path "docs\*quality*" -Destination "backup_20251011\" -Recurse
Copy-Item -Path "docs\*uvm*" -Destination "backup_20251011\" -Recurse
```

2. **検証環境の動作再確認**
```powershell
# 削除前の最終動作確認
cd "E:\Nautilus\workspace\fpgawork\AXIUART_\sim\exec"
.\run_uvm.ps1 -TestName frame_parser_diagnostic_test -Verbosity UVM_MEDIUM
```

### **Stage 2: 段階的ファイル削除 (優先度: 高)**

#### **削除対象カテゴリ**

**Category A: 古い日記ファイル (削除推奨)**
```
diary_20250915.md  # 2か月前
diary_20250919.md  # 2か月前  
diary_20250920_stage1_complete.md
diary_20250921_phase4_completion.md
diary_20250926.md
diary_20250927.md
diary_20250928.md
diary_20250929.md
diary_20250930.md
```

**Category B: 重複完了レポート (削除推奨)**
```
diary_20251004_flow_control_completion.md
diary_20251005_test_register_uvm_completion.md  
diary_20251006_phase4_completion.md
diary_20251007_phase1_completion.md
diary_20251007_phase1_crc_debugging_completion.md
diary_20251007_phase2_data_alignment_completion.md
diary_20251007_uvm_completion_next_phase.md
diary_20251008_phase3_completion.md
work_instructions_completion_summary.md
phase1_completion_report_20251007.md
```

**Category C: 古い作業指示書 (削除推奨)**
```
comprehensive_work_instructions.md  # 更新版存在
work_handover_20250920.md  # 古いハンドオーバー
work_handover_20250921_phase4.md
fpga_debug_work_plan.md  # FPGA関連は完了済み
fpga_register_debug_work_instructions_20251007.md
rtl_debug_work_plan.md
debug_work_instructions_20251007.md
```

**Category D: 古い分析ファイル (削除推奨)**
```
error_analysis_31_remaining_20251002.md  # 解決済み
correction_mask_fundamental_problem_20251006.md  # 修正済み
correction_mask_root_fix_completion_20251006.md  # 完了済み
critical_issue_discovered.md  # 解決済み
emergency_diagnosis_report_20251010.md  # 緊急対応完了
emergency_discovery_20251006.md
```

**Category E: 古い波形ファイル (削除推奨)**
```
# 2025-10-10の古い波形ファイル (最新2つ以外)
frame_parser_diagnostic_test_20251010_181455.mxd
frame_parser_diagnostic_test_20251010_184347.mxd  
frame_parser_diagnostic_test_20251010_184542.mxd
... (計20個の古い波形ファイル)
```

#### **段階的削除実行手順**

**Step 1: ローリスク削除 (古い日記ファイル)**
```powershell
# Category A: 2か月以上前の日記ファイル
$OldDiaryFiles = @(
    "diary_20250915.md",
    "diary_20250919.md", 
    "diary_20250920_stage1_complete.md",
    "diary_20250921_phase4_completion.md",
    "diary_20250926.md",
    "diary_20250927.md",
    "diary_20250928.md",
    "diary_20250929.md",
    "diary_20250930.md"
)

foreach ($File in $OldDiaryFiles) {
    if (Test-Path "docs\$File") {
        Write-Host "Removing old diary: $File" -ForegroundColor Yellow
        Remove-Item "docs\$File" -Force
    }
}
```

**Step 2: 中リスク削除 (重複完了レポート)**
```powershell
# Category B: 重複完了レポート
$CompletionFiles = @(
    "diary_20251004_flow_control_completion.md",
    "diary_20251005_test_register_uvm_completion.md",
    "diary_20251006_phase4_completion.md",
    "diary_20251007_phase1_completion.md",
    "diary_20251007_phase1_crc_debugging_completion.md",
    "diary_20251007_phase2_data_alignment_completion.md",
    "diary_20251007_uvm_completion_next_phase.md",
    "diary_20251008_phase3_completion.md",
    "work_instructions_completion_summary.md",
    "phase1_completion_report_20251007.md"
)

# 検証環境動作確認後に実行
.\run_uvm.ps1 -TestName frame_parser_diagnostic_test -Verbosity UVM_LOW
if ($LASTEXITCODE -eq 0) {
    foreach ($File in $CompletionFiles) {
        if (Test-Path "docs\$File") {
            Remove-Item "docs\$File" -Force
            Write-Host "Removed completion file: $File" -ForegroundColor Green
        }
    }
}
```

**Step 3: 高リスク削除 (古い作業指示書)**
```powershell
# Category C: 古い作業指示書 (更新版が存在するもののみ削除)
$OldInstructionFiles = @(
    "comprehensive_work_instructions.md",  # _updated版が存在
    "work_handover_20250920.md",
    "work_handover_20250921_phase4.md",
    "fpga_debug_work_plan.md",
    "fpga_register_debug_work_instructions_20251007.md",
    "rtl_debug_work_plan.md",
    "debug_work_instructions_20251007.md"
)

# 慎重に削除 (新しいバージョンが存在することを確認)
foreach ($File in $OldInstructionFiles) {
    if (Test-Path "docs\$File") {
        Write-Host "Checking if newer version exists for: $File" -ForegroundColor Yellow
        # 手動確認推奨
    }
}
```

**Step 4: 最終削除 (古い波形ファイル)**
```powershell
# Category E: 古い波形ファイル (最新2つ以外削除)
cd "archive\waveforms\"
$WaveformFiles = Get-ChildItem -Name "*.mxd" | Sort-Object LastWriteTime -Descending
$FilesToKeep = $WaveformFiles | Select-Object -First 2
$FilesToDelete = $WaveformFiles | Select-Object -Skip 2

foreach ($File in $FilesToDelete) {
    Write-Host "Removing old waveform: $File" -ForegroundColor Red
    Remove-Item $File -Force
}
```

### **Stage 3: 品質保証体制構築 (優先度: 高)**

#### **必須保持ファイル確認**

**Category S: 品質保証コア (保持必須)**
```
uvm_verification_quality_assurance_instructions_20251010.md  # 本作業指示書の基準
project_uvm_reporting_guidelines.md  # 報告標準
uvm_verification_quality_assessment_report_20251011.md  # 品質評価
verification_status_report.md  # プロジェクト状況
```

**Category P: Phase 4準備関連 (保持推奨)**
```
diary_20251009_protocol_verification.md  # プロトコル検証結果
diary_20251009_rxtx_verification_completion.md  # RX/TX検証
diary_20251010_phase1_frame_parser_completion.md  # 最新完了報告
coverage_improvement_plan_20250928.md  # カバレッジ向上計画
coverage_improvement_checklist_20250928.md  # チェックリスト
```

#### **フォルダ構造最適化**

```
docs/
├── core/                          # コア設計情報 (新設)
│   ├── design_overview.md
│   ├── system_architecture.md  
│   └── uart_axi4_protocol.md
├── quality_assurance/             # 品質保証関連 (新設)
│   ├── uvm_verification_quality_assurance_instructions_20251010.md
│   ├── project_uvm_reporting_guidelines.md
│   └── verification_status_report.md  
├── phase4_preparation/            # Phase 4準備 (新設)
│   ├── coverage_improvement_plan_20250928.md
│   └── coverage_improvement_checklist_20250928.md
└── archive/                       # アーカイブ (新設)
    ├── diary_archive/
    └── old_reports/
```

---

## 🔧 **Phase 4準備最適化作業**

### **検証環境最適化**

#### **必須確認項目**

1. **UVM環境安定性確認**
```powershell
# 全コアテストの動作確認
$CoreTests = @(
    "frame_parser_diagnostic_test",
    "uart_axi4_basic_test", 
    "uart_axi4_register_test"
)

foreach ($Test in $CoreTests) {
    Write-Host "Testing: $Test" -ForegroundColor Cyan
    .\run_uvm.ps1 -TestName $Test -Verbosity UVM_MEDIUM
    if ($LASTEXITCODE -ne 0) {
        Write-Error "CRITICAL: $Test failed - cleanup suspended"
        exit 1
    }
}
```

2. **カバレッジ基準値確認**
```powershell
# Phase 4準備のためのカバレッジ基準確認  
# 目標: Frame Coverage > 80%, Total Coverage > 80%
# 現在: Frame 19.44%, Total 32.52% (要改善)
```

### **Phase 4品質目標設定**

#### **定量的品質目標**

| 品質指標 | 現在値 | Phase 4目標 | 達成期限 |
|----------|---------|-------------|----------|
| **Frame Coverage** | 19.44% | **≥ 80%** | 2週間以内 |
| **Total Coverage** | 32.52% | **≥ 80%** | 2週間以内 |
| **UVM_ERROR** | 0 | **0維持** | 常時 |
| **実行時間** | 14.62秒 | **< 20秒** | 1週間以内 |

#### **定性的品質目標**

- **偽陽性完全排除**: 全ての成功判定は3つの独立手法で確認
- **見逃し完全排除**: エラー注入テストで検証環境の感度確認
- **実機レベル検証**: 波形レベル自動解析の実装

---

## 📅 **クリーンアップ実行スケジュール**

### **Phase 4品質保証前倒しスケジュール**

| Stage | 期間 | 主要作業 | 成功基準 |
|-------|------|----------|-----------|
| **Stage 1** | 即座 | バックアップ・安全確保 | Git commit完了 |
| **Stage 2** | 1-2時間 | 段階的ファイル削除 | 検証環境動作確認 |
| **Stage 3** | 2-3時間 | 品質保証体制構築 | フォルダ構造最適化 |
| **Stage 4** | 1日 | Phase 4準備作業 | 品質目標設定 |

**合計期間**: 1-2日 (Phase 4開始を遅らせない)

---

## 🚨 **安全確保・リスク管理**

### **削除前必須確認**

1. **検証環境動作確認**: 各段階で必ずテスト実行
2. **Git commit**: 削除前に現在の状態を保存
3. **バックアップ確保**: 重要ファイルの別途保存
4. **段階的実行**: 一度に大量削除しない

### **緊急復旧手順**

```powershell
# 問題発生時の緊急復旧
git log --oneline -10  # 最近のcommit確認
git reset --hard HEAD~1  # 直前の状態に復旧
git clean -fd  # 未追跡ファイル削除
```

### **品質確保チェックポイント**

- [ ] 各削除段階で検証環境の動作確認
- [ ] UVM_ERROR = 0 維持確認
- [ ] Enhanced Reporting機能維持確認  
- [ ] Phase 3 Scoreboard動作維持確認
- [ ] 波形生成機能維持確認

---

## 📊 **成功基準・完了判定**

### **クリーンアップ成功基準**

1. **ファイル数削減**: docs/ファイル数を120個→60個以下
2. **検証環境安定**: 全コアテストがUVM_ERROR=0で実行
3. **情報整理**: 必要情報への迅速アクセス可能
4. **Phase 4準備**: 品質保証体制の確立

### **Phase 4移行判定基準**

- [ ] クリーンアップ完了確認
- [ ] 検証環境安定性確認  
- [ ] 品質目標設定完了
- [ ] Phase 4作業環境準備完了

---

## 📋 **作業実行チェックリスト**

### **事前準備**
- [ ] 現在の検証環境動作確認 (UVM_ERROR=0)
- [ ] Git status確認・commit準備
- [ ] バックアップディレクトリ作成

### **Stage 1実行**
- [ ] Git commitでバックアップ保存
- [ ] 重要ファイルの別途バックアップ
- [ ] 検証環境の動作再確認

### **Stage 2実行**  
- [ ] Category A (古い日記) 削除実行
- [ ] 動作確認後、Category B (完了レポート) 削除
- [ ] 慎重確認後、Category C (作業指示書) 削除
- [ ] Category E (古い波形) 削除実行

### **Stage 3実行**
- [ ] フォルダ構造最適化実行
- [ ] 必須保持ファイル確認
- [ ] 品質保証体制構築確認

### **完了確認**
- [ ] 全コアテストの動作確認
- [ ] ファイル数削減確認 (目標: 50%削減)
- [ ] Phase 4準備完了確認
- [ ] 最終Git commit実行

---

**この作業指示書により、Phase 3の成果を確実に保護しながら、効率的なプロジェクトクリーンアップとPhase 4品質保証準備を実現します。**

---

## 🎯 **重要: Phase 4品質保証との連携**

このクリーンアップ作業は、`uvm_verification_quality_assurance_instructions_20251010.md`で定義されたPhase 4品質保証作業の前提条件として位置付けられます。

**Phase 4開始前の必須条件**:
- プロジェクト構造の最適化完了
- 検証環境の安定性確保
- 品質目標の明確化
- 作業環境のクリーンアップ

**Phase 4との整合性確保**:
- Level 0-2品質基準の維持
- Enhanced Reporting機能の保護
- Phase 3 Scoreboardの動作保証
- 段階的品質向上の基盤確立

クリーンアップ完了後、即座にPhase 4品質保証作業に移行可能な状態を構築します。