# MCP Server Optimized UVM Execution Environment

## 概要

`run_uvm.ps1`と同等の機能を持つMCP server最適化版のUVM実行環境を構築しました。MCP serverの`run_in_terminal`機能を活用し、より使いやすく高機能なUVM実行環境を提供します。

## 作成されたファイル

### 1. `mcp_uvm_runner.ps1`
- 元の`run_uvm.ps1`と同等の機能を持つMCP最適化版
- MCP環境向けの詳細ログ出力とセクション化表示
- DSIMの正しいコンパイルオプション対応（`-genimage`）
- Enhanced UVM report analysis機能統合

### 2. `MCPUVMFunctions.psm1`
- MCP server環境で便利に使用できるPowerShellモジュール
- 複数の便利な関数を提供

### 3. `setup_mcp_uvm.ps1`
- MCP環境のセットアップと検証スクリプト
- 環境変数確認、ディレクトリ作成、モジュール読み込み

## 使用方法

### 基本セットアップ

```powershell
# 1. MCP-UVM環境のセットアップ
cd "e:\Nautilus\workspace\fpgawork\AXIUART_\sim\exec"
.\setup_mcp_uvm.ps1

# 2. MCP-UVM関数の読み込み（毎回必要）
Import-Module .\MCPUVMFunctions.psm1 -Force
```

### 利用可能な関数

#### `Invoke-MCPUVMTest`
メインのUVM実行関数（元のrun_uvm.ps1と同等）

```powershell
# 基本実行
Invoke-MCPUVMTest

# 特定のテスト実行
Invoke-MCPUVMTest -TestName "uart_axi4_scoreboard_test"

# 高詳細度での実行
Invoke-MCPUVMTest -TestName "uart_axi4_basic_test" -Verbosity UVM_HIGH

# 波形付きでの実行
Invoke-MCPUVMTest -TestName "uart_axi4_basic_test" -Waves on -Seed 42

# カバレッジ有効での実行
Invoke-MCPUVMTest -TestName "uart_axi4_basic_test" -Coverage on
```

#### `Invoke-MCPUVMQuickTest`
高速反復開発用のクイックテスト

```powershell
# 高速テスト（低詳細度、カバレッジ無効）
Invoke-MCPUVMQuickTest -TestName "uart_axi4_basic_test"
```

#### `Invoke-MCPUVMCompileOnly`
コンパイルのみの実行（構文チェック）

```powershell
# コンパイルチェック
Invoke-MCPUVMCompileOnly
```

#### `Invoke-MCPUVMWithWaves`
デバッグ用の波形付き実行

```powershell
# 波形付きデバッグ実行
Invoke-MCPUVMWithWaves -TestName "uart_axi4_basic_test" -Seed 42
```

#### `Get-MCPUVMStatus`
最近の実行結果確認

```powershell
# 最近のログと波形ファイルを表示
Get-MCPUVMStatus
```

#### `Show-MCPUVMHelp`
ヘルプ表示

```powershell
# 使用方法ヘルプ
Show-MCPUVMHelp
```

## MCP Server環境での利点

### 1. run_in_terminal機能との統合
- MCP serverの`run_in_terminal`機能を使用して、任意の場所からUVM実行可能
- コマンド履歴の自動管理
- 実行状況のリアルタイム監視

### 2. Enhanced Reporting
- MCP環境に最適化されたログ表示
- セクション化された見やすい出力
- カラーコーディングによる状況判別

### 3. 便利な関数群
- 用途別の実行関数（クイックテスト、デバッグ、コンパイルチェック）
- 簡単なコマンド名で複雑な設定を自動化
- 状況確認機能

### 4. 改善された機能
- DSIMの正しいコンパイルオプション対応
- 元のrun_uvm.ps1の問題修正
- エラーハンドリング強化

## 元のrun_uvm.ps1との互換性

すべての元のパラメータをサポート：

| 元のパラメータ | MCP版対応 | 説明 |
|---------------|-----------|------|
| `-Mode` | ✅ | run/compile mode |
| `-TestName` | ✅ | テスト名指定 |
| `-Verbosity` | ✅ | UVM詳細度 |
| `-Seed` | ✅ | シミュレーション seed |
| `-Waves` | ✅ | 波形出力制御 |
| `-Coverage` | ✅ | カバレッジ収集 |
| `-ReportAnalysis` | ✅ | Enhanced報告解析 |
| `-ExtraArgs` | ✅ | 追加引数 |

## 実行例

### MCP server環境での典型的な使用フロー

```powershell
# 1. 環境セットアップ（初回のみ）
cd "e:\Nautilus\workspace\fpgawork\AXIUART_\sim\exec"
.\setup_mcp_uvm.ps1

# 2. モジュール読み込み
Import-Module .\MCPUVMFunctions.psm1 -Force

# 3. クイックテスト実行
Invoke-MCPUVMQuickTest

# 4. 問題があれば詳細実行
Invoke-MCPUVMWithWaves -Verbosity UVM_HIGH

# 5. 結果確認
Get-MCPUVMStatus
```

### 元のrun_uvm.ps1コマンドとの対応

```powershell
# 元のコマンド
.\run_uvm.ps1 -TestName "uart_axi4_basic_test" -Verbosity UVM_HIGH -Waves on -Seed 42

# MCP版対応コマンド
Invoke-MCPUVMTest -TestName "uart_axi4_basic_test" -Verbosity UVM_HIGH -Waves on -Seed 42
```

## 注意事項

1. **モジュールの再読み込み**: PowerShellセッションを開くたびに`Import-Module .\MCPUVMFunctions.psm1 -Force`が必要です。

2. **実行ディレクトリ**: 関数は`e:\Nautilus\workspace\fpgawork\AXIUART_\sim\exec`ディレクトリから実行される必要があります。

3. **RTLレベルの既知問題**: 現在Frame_Parserモジュールにポート接続の問題があります。これはMCP環境の問題ではなく、RTLレベルの修正が必要です。

4. **環境変数**: DSIM関連の環境変数（DSIM_HOME、DSIM_ROOT、DSIM_LIB_PATH）が正しく設定されている必要があります。

5. **ライセンス**: DSIMライセンスが有効である必要があります。

6. **パラメータの型**: 文字列パラメータは引用符で囲む必要があります（例：`-Coverage "off"`）。

## 今後の拡張可能性

- バックグラウンド実行のサポート
- 並列テスト実行
- より詳細なカバレッジ分析
- 自動レポート生成
- CI/CD統合

---

**この環境により、MCP serverでrun_uvm.ps1と同等以上の機能を持つUVM実行環境が利用可能になりました。**