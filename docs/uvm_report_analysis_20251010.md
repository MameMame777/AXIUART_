# UVM Report Analysis Guide

## Report Counts by ID - 詳細解説

### コンポーネント別メッセージ数分析

| ID | 数 | 分類 | 説明 |
|---|---|---|---|
| **[SCOREBOARD]** | 12 | 検証 | スコアボードによる検証結果レポート（最多） |
| **[ENV]** | 10 | 環境 | テスト環境の設定・接続・最終レポート |
| **[DIAG]** | 9 | 診断 | Frame Parser診断テスト専用メッセージ |
| **[BASE_TEST]** | 6 | テスト | ベーステストの設定・トポロジー・結果 |
| **[COVERAGE]** | 6 | カバレッジ | カバレッジ収集・レポート生成 |
| **[UART_DRIVER]** | 1 | ドライバー | UART監視FIFO使用通知 |
| **[UART_MONITOR]** | 1 | モニター | カバレッジコレクター未発見通知 |

### UVMシステムメッセージ
| ID | 数 | 説明 |
|---|---|---|
| **[UVM/RELNOTES]** | 1 | UVMライブラリリリースノート |
| **[UVMTOP]** | 1 | テストベンチトポロジー表示 |
| **[UVM/COMP/NAMECHECK]** | 1 | コンポーネント名前チェック |
| **[NO_DPI_TSTNAME]** | 1 | DPI無効時のテスト名取得 |
| **[RNTST]** | 1 | 実行テスト名表示 |
| **[TPRGED]** | 1 | ファクトリー型名重複警告 |

## テストシナリオ別詳細表示の実現方法

### 1. Verbosity Level調整による詳細化

現在: `UVM_LOW`
推奨: より詳細な検証のため`UVM_MEDIUM`または`UVM_HIGH`

```powershell
# 詳細レポート用コマンド
.\run_uvm.ps1 -TestName frame_parser_diagnostic_test -Verbosity UVM_MEDIUM
```

### 2. カスタムレポートIDの追加

検証コンポーネント毎に専用IDを設定可能:

```systemverilog
// スコアボード内
`uvm_info("SCOREBOARD_MATCH", $sformatf("Frame matched: cmd=0x%02X", cmd), UVM_MEDIUM)
`uvm_info("SCOREBOARD_MISMATCH", $sformatf("Frame mismatch detected"), UVM_LOW)

// Frame Parserテスト内
`uvm_info("FRAME_PARSER_STATE", $sformatf("State: %s", state.name()), UVM_MEDIUM)
`uvm_info("FRAME_PARSER_CRC", $sformatf("CRC validation: %s", result), UVM_MEDIUM)
```

### 3. テストごとのレポート分析スクリプト

```powershell
# レポート分析用関数追加例
function Analyze-UVMReport {
    param([string]$LogFile)
    
    Write-Host "=== UVM Report Analysis ==="
    Select-String "\*\* Report counts by id" -A 20 $LogFile
    
    Write-Host "=== Error Analysis ==="
    Select-String "UVM_ERROR" $LogFile
    
    Write-Host "=== Coverage Summary ==="
    Select-String "coverage.*%" $LogFile
}
```

## 推奨する検証戦略の改善

### Phase 3向けレポート強化

1. **スコアボード詳細化**
   - UART→AXI相関レポート
   - ミスマッチ詳細分析
   - パフォーマンス統計

2. **カバレッジ分析強化**
   - 機能カバレッジ80%以上目標
   - バグ挿入テスト追加
   - エラーシナリオ網羅

3. **自動レポート生成**
   - テスト完了後の自動分析
   - トレンド分析対応
   - CI/CD統合準備

## 今後のテスト実行推奨設定

```powershell
# Phase 3 推奨設定
.\run_uvm.ps1 -TestName <test_name> -Verbosity UVM_MEDIUM -EnableCoverage -GenerateReport
```

この設定により：
- より詳細なコンポーネント別ログ
- カバレッジ詳細レポート  
- 自動レポート生成
- 検証品質の継続的改善

が実現できます。