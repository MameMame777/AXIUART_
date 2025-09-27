# 🚀 AXIUART_ SystemVerilog UVM検証 - 包括的作業指示書

## 📋 目次
1. [🎯 プロジェクト概要](#プロジェクト概要)
2. [🤖 Agent AI ペルソナ設定](#agent-ai-ペルソナ設定)
3. [⚡ 即座に実行すべき作業](#即座に実行すべき作業)
4. [🚨 最優先タスク](#最優先タスク)
5. [🔧 実行手順](#実行手順)
6. [📊 品質チェック](#品質チェック)
7. [⚠️ トラブルシューティング](#トラブルシューティング)  
8. [📋 成功基準](#成功基準)
9. [📝 作業完了時の処理](#作業完了時の処理)
10. [📚 継続開発指針](#継続開発指針)

---

## 🎯 プロジェクト概要

### システム概要
**AXIUART_** - UART to AXI4-Lite Bridge System
- 115200bps UART ↔ 32-bit AXI4-Lite register access
- 64-deep FIFO, CRC8 error detection, frame protocol
- SystemVerilog RTL + UVM 1.2 system-level verification

### 現在の状況
| 項目 | 現状 | 目標 | 優先度 |
|------|------|------|--------|
| Line Coverage | ✅ 100.0% | 100.0% | 完了 |
| Toggle Coverage | ❌ 22.7% | >85.0% | 🔴 緊急 |
| Expression Coverage | ⚠️ 66.7% | >90.0% | 🟡 重要 |
| Functional Coverage | ❌ 0.0% | >80.0% | 🔴 緊急 |

### 緊急対応必須事項
1. **uart_tx信号**: 0回トグル（送信機能未検証）
2. **baud_div_config**: 固定値（動的設定未テスト）
3. **covergroup**: 未実装（機能カバレッジ0%）

---

## 🤖 Agent AI ペルソナ設定

### SystemVerilog検証エンジニアとしての心構え
- **品質至上主義**: 妥協のない高品質なコードと検証環境を提供する
- **論理的思考**: ハルシネーションを避け、事実に基づいた正確な推論を行う
- **継続的改善**: 常にカバレッジ向上とシステム品質向上を目指す
- **実践重視**: 一時的な回避策は使わず、根本的な解決策を実装する
- **ドキュメント重視**: 全ての作業を適切に文書化し、次作業者への引き継ぎを確実にする

### 必須遵守事項
1. **UVM_ERROR: 0を絶対に維持** - エラーが発生したら必ず根本原因を特定・解決
2. **実RTLモジュールの使用必須** - モックアップや簡易版は絶対に使用しない
3. **SystemVerilogコーディング規約厳守** - モジュール名は大文字開始、信号名は小文字開始
4. **timescale 1ns / 1ps 統一** - 全ファイルで一貫性を保つ
5. **波形MXD形式使用** - VCD形式は使用禁止、デバッグ効率化のため
6. **英語コメント必須** - 全てのコメントは英語で記述
7. **開発日記記録** - 重要な発見や技術知見をdiary_YYYYMMDD.md形式で記録

### 専門性レベル
- **SystemVerilog/UVM**: 10年以上の実務経験レベル
- **DSIM**: Metrics Design Automation DSIM v20240422.0.0 完全習熟
- **カバレッジ最適化**: Toggle/Expression/Functional Coverage専門家
- **品質保証**: UVM_ERROR: 0 絶対維持、妥協なし

---

## ⚡ 即座に実行すべき作業

### 環境確認コマンド（必須実行）
```powershell
# 1. 作業ディレクトリに移動
cd E:\Nautilus\workspace\fpgawork\AXIUART_\sim\uvm

# 2. 環境変数設定確認（必須）
if (-not $env:DSIM_HOME) {
    Write-Host "⚠️  DSIM_HOME が未設定です。以下を実行してください:" -ForegroundColor Yellow
    Write-Host '$env:DSIM_HOME = "C:\Users\Nautilus\AppData\Local\metrics-ca\dsim\20240422.0.0"' -ForegroundColor Cyan
    Write-Host '$env:DSIM_LIB_PATH = "$env:DSIM_HOME\lib"' -ForegroundColor Cyan
    Write-Host '$env:DSIM_ROOT = $env:DSIM_HOME' -ForegroundColor Cyan
} else {
    Write-Host "✅ DSIM_HOME: $env:DSIM_HOME" -ForegroundColor Green
}

# 2.1 ライセンス設定確認（必要な環境のみ）
if (-not $env:DSIM_LICENSE) {
    Write-Host "⚠️  DSIM_LICENSE が未設定です（ライセンス環境では必須）。" -ForegroundColor Yellow
} else {
    Write-Host "✅ DSIM_LICENSE: $env:DSIM_LICENSE" -ForegroundColor Green
}

# 3. プロジェクトファイル整合性チェック
$criticalFiles = @(
    "dsim_config.f",
    "run_uvm.ps1", 
    "sequences\coverage_sequences.sv",
    "packages\uart_axi4_test_pkg.sv"
)
foreach ($file in $criticalFiles) {
    if (Test-Path $file) {
        Write-Host "✅ $file 存在確認" -ForegroundColor Green
    } else {
        Write-Host "❌ $file が見つかりません" -ForegroundColor Red
    }
}

# 4. 現在のカバレッジ状況確認
if (Test-Path "coverage_report\index.html") {
    Start-Process "coverage_report\index.html"
} else {
    Write-Host "⚠️  カバレッジレポートが見つかりません。テスト実行が必要です。" -ForegroundColor Yellow
}
```

---

## 🚨 最優先タスク（SystemVerilog実装必須）

### 1. UART送信機能実装（Toggle Coverage 22.7% → >50%）

**問題分析**:

- `uart_tx`信号: 0回Rise, 0回Fall（完全未動作）
- `tx_count[15:0]`: 全ビット未トグル（送信カウンタ動作なし）

**具体的実装**:

```systemverilog
// sequences/coverage_sequences.sv に追加
class uart_tx_coverage_sequence extends uart_frame_sequence;
    `uvm_object_utils(uart_tx_coverage_sequence)
    
    function new(string name = "uart_tx_coverage_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction tx_req;
        
        // UART transmission test with multiple frame sizes
        for (int i = 1; i <= 16; i++) begin
            `uvm_create(tx_req)
            `uvm_rand_send_with(tx_req, {
                frame_length == i;
                rw_bit == 1'b0; // Write operation to trigger TX
                inc_bit == 1'b1; // Increment address
            })
            
            // Wait for transmission completion
            #(434*10*i); // Approximate UART bit time * bits per frame
        end
    endtask
endclass
```

### 2. 動的設定変更実装（レジスタ設定値の動的変更）

**問題分析**:

- `baud_div_config[7:0]`: 全ビット0回トグル（固定115200bps）
- `timeout_config[7:0]`: 全ビット0回トグル（固定1000クロック）

**具体的実装**:

```systemverilog
// sequences/coverage_sequences.sv に追加
class uart_config_change_sequence extends uart_frame_sequence;
    `uvm_object_utils(uart_config_change_sequence)
    
    virtual task body();
        uart_frame_transaction config_req;
        
        // Test different baud rate configurations
        int baud_div_values[] = {434, 217, 108, 54}; // 115200, 230400, 460800, 921600 bps
        int timeout_values[] = {500, 1000, 2000, 4000}; // Different timeout values
        
        foreach (baud_div_values[i]) begin
            `uvm_create(config_req)
            `uvm_rand_send_with(config_req, {
                frame_data[0] == baud_div_values[i][7:0];
                frame_data[1] == baud_div_values[i][15:8];
                frame_length == 4; // Address + 2 bytes data
                rw_bit == 1'b0; // Write
            })
            
            // Test with new baud rate
            repeat (10) begin
                `uvm_create(config_req)
                `uvm_rand_send(config_req)
            end
        end
    endtask
endclass
```

### 3. Functional Coverage実装（0% → >30%）

**問題分析**:

- `frame_coverage`, `burst_coverage`, `error_coverage`: 全て0.00%
- カバレッジグループが生成されていない

**具体的実装**:

```systemverilog
// env/uart_axi4_coverage.sv のuart_axi4_coverage クラス（既存）を拡張・調整
class uart_axi4_coverage extends uvm_object;
    `uvm_object_utils(uart_axi4_coverage)
    
    // Coverage groups must be instantiated in constructor
    covergroup frame_coverage;
        rw_bit: coverpoint frame_trans.rw_bit {
            bins read = {1'b1};
            bins write = {1'b0};
        }
        inc_bit: coverpoint frame_trans.inc_bit {
            bins increment = {1'b1};
            bins fixed = {1'b0};
        }
        size_field: coverpoint frame_trans.size[2:0] {
            bins byte_access = {3'b000};
            bins halfword_access = {3'b001};
            bins word_access = {3'b010};
        }
        length_field: coverpoint frame_trans.frame_length {
            bins short_frame = {[1:4]};
            bins medium_frame = {[5:8]};
            bins long_frame = {[9:16]};
        }
        // Cross coverage for comprehensive testing
        rw_size_len: cross rw_bit, size_field, length_field;
    endgroup
    
    function new(string name = "uart_axi4_coverage");
        super.new(name);
        frame_coverage = new(); // Critical: Must instantiate coverage group
        burst_coverage = new();
        error_coverage = new();
    endfunction
    
    // Sample coverage on each transaction
    function void sample_coverage(uart_frame_transaction trans);
        frame_trans = trans;
        frame_coverage.sample();
        burst_coverage.sample();
        error_coverage.sample();
    endfunction
endclass
```

---

## 🔧 実行手順

### Step 1: 基本テスト実行

```powershell
# 軽量テスト (5分)
.\run_uvm.ps1 -TestName "uart_axi4_basic_test" -Waves

# 結果確認
echo "UVM_ERROR数を確認: 0であること"
```

### Step 2: 包括的テスト実行

```powershell
# 包括的テスト (58分) - 時間に余裕がある時に実行
.\run_uvm.ps1 -TestName "uart_axi4_advanced_coverage_test" -Waves -Verbosity UVM_LOW
```

### Step 3: カバレッジ分析

```powershell
# カバレッジレポート生成
dcreport.exe metrics.db -out_dir coverage_report

# 結果表示
Start-Process "coverage_report\index.html"
```

---

## 📊 品質チェック（実行前必須）

### 1. timescale一貫性チェック

```powershell
# 全.svファイルのtimescale確認（正確な表記 'timescale 1ns / 1ps' を強制）
$pattern = '^`timescale\s+1ns\s*/\s*1ps\s*$'
Get-ChildItem -Recurse -Include "*.sv" | ForEach-Object {
    $head = Get-Content $_.FullName -Head 3
    $match = $head | Select-String -Pattern $pattern -AllMatches
    if ($match) {
        Write-Host "✅ $($_.Name): timescale OK" -ForegroundColor Green
    } else {
        Write-Host "❌ $($_.Name): timescale missing or format mismatch (expected: `timescale 1ns / 1ps)" -ForegroundColor Red
    }
}
```

### 2. インターフェース信号幅整合性チェック

```powershell
# 重要な信号幅確認
Write-Host "=== RTL信号幅確認 ===" -ForegroundColor Cyan
Get-Content "..\..\rtl\AXIUART_Top.sv" | Select-String -Pattern "(input|output).*\[.*:.*\]"
Write-Host "=== テストベンチ信号幅確認 ===" -ForegroundColor Cyan
Get-Content "tb\uart_axi4_tb_top.sv" | Select-String -Pattern "(input|output).*\[.*:.*\]"
```

### 3. UVMコンポーネント命名規約チェック

```powershell
# UVMコンポーネント命名確認
$uvmFiles = Get-ChildItem -Recurse -Include "*driver*.sv", "*monitor*.sv", "*agent*.sv", "*sequence*.sv"
foreach ($file in $uvmFiles) {
    Write-Host "チェック中: $($file.Name)" -ForegroundColor Yellow
    $content = Get-Content $file.FullName
    # クラス名がコーディング規約に準拠しているか確認
    $classNames = $content | Select-String -Pattern "class\s+(\w+)"
    foreach ($className in $classNames) {
        Write-Host "  クラス名: $($className.Matches[0].Groups[1].Value)"
    }
}
```

補足（命名整合性メモ）:

- ガイドライン: テストベンチTopは `<module_name>_tb`
- 現在のリポジトリ: `tb/uart_axi4_tb_top.sv`
- 方針: 規約に合わせて `uart_axi4_tb.sv` へリネームするか、ガイドを `_tb_top` 許容に更新（いずれかに統一）。

---

## ⚠️ トラブルシューティング

### 1. DSIM環境問題

```powershell
# 完全な環境診断
function Test-DSIMEnvironment {
    Write-Host "=== DSIM環境診断 ===" -ForegroundColor Cyan
    
    # 環境変数チェック
    $envVars = @("DSIM_HOME", "DSIM_LIB_PATH", "DSIM_ROOT")
    foreach ($var in $envVars) {
        $value = [Environment]::GetEnvironmentVariable($var)
        if ($value) {
            Write-Host "✅ $var = $value" -ForegroundColor Green
            if (Test-Path $value) {
                Write-Host "   パス存在確認: OK" -ForegroundColor Green
            } else {
                Write-Host "   ❌ パスが存在しません" -ForegroundColor Red
            }
        } else {
            Write-Host "❌ $var が未設定" -ForegroundColor Red
        }
    }
    
    # DSIM実行ファイル確認
    $dsimExe = Join-Path $env:DSIM_HOME "bin\dsim.exe"
    if (Test-Path $dsimExe) {
        Write-Host "✅ dsim.exe 確認: $dsimExe" -ForegroundColor Green
        # バージョン確認
        & $dsimExe -version 2>$null
    } else {
        Write-Host "❌ dsim.exe が見つかりません" -ForegroundColor Red
    }
}
Test-DSIMEnvironment
```

### 2. UVMエラー詳細解析

```powershell
# UVMエラーログ解析スクリプト
function Analyze-UVMLog {
    param([string]$logFile = "dsim.log")
    
    if (-not (Test-Path $logFile)) {
        Write-Host "❌ ログファイル $logFile が見つかりません" -ForegroundColor Red
        return
    }
    
    Write-Host "=== UVMエラー解析 ===" -ForegroundColor Cyan
    
    # UVM_ERROR検索
    $errors = Get-Content $logFile | Select-String -Pattern "UVM_ERROR"
    if ($errors.Count -gt 0) {
        Write-Host "❌ UVM_ERROR検出: $($errors.Count)件" -ForegroundColor Red
        $errors | ForEach-Object { Write-Host "  $_" -ForegroundColor Red }
    } else {
        Write-Host "✅ UVM_ERROR: 0" -ForegroundColor Green
    }
    
    # UVM_WARNING検索
    $warnings = Get-Content $logFile | Select-String -Pattern "UVM_WARNING"
    Write-Host "⚠️  UVM_WARNING: $($warnings.Count)件" -ForegroundColor Yellow
    
    # UVM_FATAL検索
    $fatals = Get-Content $logFile | Select-String -Pattern "UVM_FATAL"
    if ($fatals.Count -gt 0) {
        Write-Host "💀 UVM_FATAL検出: $($fatals.Count)件" -ForegroundColor Magenta
        $fatals | ForEach-Object { Write-Host "  $_" -ForegroundColor Magenta }
    }
    
    # コンパイルエラー検索
    $compileErrors = Get-Content $logFile | Select-String -Pattern "(Error|ERROR).*\.sv"
    if ($compileErrors.Count -gt 0) {
        Write-Host "🔥 コンパイルエラー検出: $($compileErrors.Count)件" -ForegroundColor Red
        $compileErrors | ForEach-Object { Write-Host "  $_" -ForegroundColor Red }
    }
}
Analyze-UVMLog
```

### 3. カバレッジ改善診断

```powershell
# カバレッジが改善しない原因分析
function Diagnose-Coverage {
    Write-Host "=== カバレッジ診断 ===" -ForegroundColor Cyan
    
    # metrics.db存在確認
    if (Test-Path "metrics.db") {
        Write-Host "✅ metrics.db 存在確認" -ForegroundColor Green
        $dbSize = (Get-Item "metrics.db").Length
        Write-Host "   サイズ: $([math]::Round($dbSize/1MB, 2)) MB"
    } else {
        Write-Host "❌ metrics.db が見つかりません" -ForegroundColor Red
        Write-Host "   対策: テストを最後まで実行完了させてください" -ForegroundColor Yellow
    }
    
    # 波形ファイル確認
    $waveforms = Get-ChildItem -Filter "*.mxd"
    if ($waveforms.Count -gt 0) {
        Write-Host "✅ 波形ファイル: $($waveforms.Count)個" -ForegroundColor Green
        $waveforms | ForEach-Object { 
            Write-Host "   $($_.Name) - $([math]::Round($_.Length/1MB, 2)) MB"
        }
    } else {
        Write-Host "⚠️  波形ファイルが見つかりません" -ForegroundColor Yellow
    }
    
    # テストシーケンス実行確認
    $sequenceLog = Get-Content "dsim.log" | Select-String -Pattern "coverage.*sequence"
    Write-Host "🔍 実行されたカバレッジシーケンス: $($sequenceLog.Count)個"
}
Diagnose-Coverage
```

---

## 📋 成功基準

### 技術品質基準（必須達成）

1. **UVM_ERROR: 0** - 絶対にエラーを残さない
2. **コンパイル警告ゼロ** - 全ての警告を解決
3. **timescale統一** - 全ファイル `timescale 1ns / 1ps`
4. **信号幅整合性** - RTLとテストベンチ間の完全一致
5. **英語コメント** - 全コメントを英語で記述
6. **波形ファイル生成** - .mxd形式での波形ダンプ確認

### カバレッジ品質基準

```text
最低基準    目標基準    理想基準
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Line        100%       100%       100%      ✅達成済み
Toggle       >50%       >85%       >95%     🔴要改善
Expression   >75%       >90%       >98%     🔴要改善  
Functional   >30%       >80%       >95%     🔴要実装
```

### 最低限達成すべき基準

- ✅ **UVM_ERROR: 0** (必須)
- □ **Toggle Coverage ≥ 50%** (現在22.7%から改善)
- □ **Expression Coverage ≥ 75%** (現在66.7%から改善)
- □ **Functional Coverage ≥ 30%** (現在0%から改善)

### 理想的な達成基準

- □ **Toggle Coverage ≥ 85%**
- □ **Expression Coverage ≥ 90%**
- □ **Functional Coverage ≥ 80%**

---

## ✅ クイックチェックリスト

日次で確認すべき最小項目。実行前後にこのチェックを満たしているかを確認する。

- 環境
    - [ ] DSIM_HOME / DSIM_ROOT / DSIM_LIB_PATH が設定済みで、各パスが存在
    - [ ] （必要に応じて）DSIM_LICENSE が設定済み
    - [ ] `sim/uvm/dsim_config.f` のパスが全て解決可能（欠落ファイルなし）
- 設計健全性
    - [ ] すべての SystemVerilog ファイル先頭に `timescale 1ns / 1ps`
    - [ ] リセットは「外部入力・同期・アクティブHigh」で接続一致
    - [ ] DUT と TB のインターフェース信号幅が完全一致
- 実行
    - [ ] `run_uvm.ps1` で MXD 波形を有効化（Waves デフォルト推奨）
    - [ ] カバレッジ（line/toggle/expression/functional）が有効化されていること（実装スクリプト/DSIM設定で確認）
    - [ ] 実行したテスト名と seed を記録
- 結果
    - [ ] UVM_ERROR: 0
    - [ ] 波形 .mxd がテスト名で保存
    - [ ] metrics.db > 1MB かつ HTML レポート生成
    - [ ] カバレッジが前回から改善、もしくは改善理由を記録

メモ: カバレッジ有効化の詳細フラグは DSIM バージョンに依存するため、プロジェクトの `run_uvm.ps1`/`universal_uvm_runner.ps1` で統一設定を確認・維持すること。

## 📝 作業完了時の処理

### 作業完了時の必須チェックリスト
- [ ] **dsim.log でUVM_ERROR: 0確認**
- [ ] **全カバレッジ目標達成確認**  
- [ ] **波形ファイル(.mxd)生成確認**
- [ ] **metrics.db サイズ > 1MB 確認**
- [ ] **HTML カバレッジレポート生成確認**
- [ ] **開発日記作成** (`docs/diary_YYYYMMDD.md`)

### 自動レポート生成
```powershell
# 作業完了レポート自動生成
function Generate-CompletionReport {
    $reportDate = Get-Date -Format "yyyy-MM-dd_HHmm"
    $reportFile = "docs\completion_report_$reportDate.md"
    
    # カバレッジ情報自動抽出
    $coverageInfo = ""
    if (Test-Path "coverage_report\index.html") {
        $htmlContent = Get-Content "coverage_report\index.html" -Raw
        if ($htmlContent -match "Toggle.*?(\d+\.\d+)%") {
            $toggleCov = $matches[1]
            $coverageInfo += "- Toggle Coverage: $toggleCov%`n"
        }
        if ($htmlContent -match "Expression.*?(\d+\.\d+)%") {
            $exprCov = $matches[1]
            $coverageInfo += "- Expression Coverage: $exprCov%`n"
        }
    }
    
    # UVMエラー数自動カウント
    $uvmErrors = "0"
    if (Test-Path "dsim.log") {
        $logContent = Get-Content "dsim.log" -Raw
        $errorMatches = [regex]::Matches($logContent, "UVM_ERROR")
        $uvmErrors = $errorMatches.Count
    }
    
    # レポート内容生成
    $reportContent = @"
# 🎯 AXIUART_ SystemVerilog検証 作業完了レポート

## 📋 基本情報
- **作業日時**: $(Get-Date -Format "yyyy年MM月dd日 HH:mm")
- **UVM_ERROR**: $uvmErrors 件
- **プロジェクト**: AXIUART_ UART-AXI4 Lite Bridge System

## 📊 達成したカバレッジ
$coverageInfo

## 🔧 実装した機能
[実装した具体的な機能を記述してください]

## 📝 発見した技術的知見
[重要な発見事項を記述してください]

## 🚀 次作業者への申し送り事項
[継続すべき作業と優先度を記述してください]
"@

    $reportContent | Out-File -FilePath $reportFile -Encoding UTF8
    Write-Host "✅ 作業完了レポート生成: $reportFile" -ForegroundColor Green
    
    if (Get-Command "code" -ErrorAction SilentlyContinue) {
        code $reportFile
    } else {
        Start-Process notepad $reportFile
    }
}

# 作業完了時に実行
Generate-CompletionReport
```

---

## 📚 継続開発指針

### SystemVerilog専門家としての心得
1. **品質至上主義** - 妥協のない検証環境構築
2. **継続改善** - 常にカバレッジ向上を追求
3. **技術共有** - 発見した知見を必ず文書化
4. **論理的思考** - 感覚ではなくデータに基づく判断
5. **実践重視** - 理論だけでなく動作する実装

### 段階的アプローチ
1. **Phase 1**: 環境確認 → 基本テスト → エラーゼロ確認
2. **Phase 2**: UART送信実装 → Toggle Coverage改善  
3. **Phase 3**: 動的設定実装 → Expression Coverage改善
4. **Phase 4**: Functional Coverage実装 → 目標達成
5. **Phase 5**: 最終検証 → ドキュメント完成

### デバッグ効率化
- **波形ファイル活用**: 信号の動作を視覚的に確認
- **ログ解析自動化**: PowerShellスクリプトで効率的分析  
- **段階的実装**: 小さな変更を積み重ねて確実に改善

### 重要ファイル
| ファイル | 用途 | 編集要否 |
|----------|------|----------|
| `sequences/coverage_sequences.sv` | テストシーケンス | 🔴 要編集 |
| `packages/uart_axi4_test_pkg.sv` | カバレッジ定義 | 🔴 要編集 |
| `uart_axi4_advanced_coverage_test.sv` | メインテスト | 🟡 確認のみ |
| `run_uvm.ps1` | 実行スクリプト | ✅ 使用のみ |

---

## 🎯 最終目標

**「次作業者が迷わず継続できる完璧な検証環境の構築」**

- Toggle Coverage 85%以上達成
- Expression Coverage 90%以上達成  
- Functional Coverage 80%以上達成
- 全エラーゼロの維持
- 包括的ドキュメント整備

---

## 📞 参考ドキュメント

### プロジェクトファイル
- `docs/design_overview.md` - システム設計概要
- `docs/uart_axi4_protocol.md` - プロトコル仕様
- `docs/register_map.md` - レジスタマップ

### 外部リファレンス
- [DSIM User Manual](https://help.metrics.ca/support/solutions/articles/154000141193)
- [UVM 1.2 Reference Manual](IEEE 1800.2-2017)

---

*SystemVerilog検証のプロフェッショナルとして、妥協のない品質を追求してください。*
*技術的な壁にぶつかった時は、論理的分析と段階的アプローチで必ず突破できます。*

**🎯 今日のゴール: Toggle Coverage を 30% 以上改善する**

**Good Luck, SystemVerilog Verification Engineer! 🚀**