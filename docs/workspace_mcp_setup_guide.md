# ワークスペース専用MCP-UVM環境設定ガイド

## 概要
このワークスペースには、システムに影響を与えることなく、セッション専用でMCP-UVM機能を読み込む安全な仕組みが設定されています。

## 安全性の特徴
- ✅ **システム全体に影響なし**: PowerShellプロファイルやレジストリを変更しません
- ✅ **セッション限定**: 現在のPowerShellセッションにのみ適用
- ✅ **ワークスペース専用**: このプロジェクト内でのみ動作
- ✅ **可逆性**: PowerShellを閉じれば全ての変更が消失

## 使用方法

### 方法1: 手動実行（推奨）
```powershell
# ワークスペースルートで実行
.\workspace_init.ps1
```

### 方法2: VS Code タスクを使用
1. VS Code で `Ctrl+Shift+P`
2. `Tasks: Run Task` を選択
3. `Initialize Workspace MCP-UVM Environment` を実行

### 方法3: UVMディレクトリから直接実行
```powershell
# UVMディレクトリで実行
cd sim\uvm
..\..\workspace_init.ps1
```

## 動作確認方法
```powershell
# MCP-UVM機能の確認
Test-WorkspaceMCPUVM

# 利用可能なコマンド表示
Show-WorkspaceHelp
```

## トラブルシューティング

### Q: MCP関数が見つからない
```powershell
# 解決方法: ワークスペース環境を再初期化
.\workspace_init.ps1
```

### Q: 別のPowerShellセッションで使いたい
```powershell
# 解決方法: 新しいセッションで再度実行
.\workspace_init.ps1
```

### Q: システムに影響があるか心配
A: このスクリプトは以下を行いません：
- PowerShellプロファイルの変更
- レジストリの変更
- 環境変数の永続的変更
- システムファイルの変更

## 利用可能なコマンド一覧

### ワークスペース専用コマンド
- `Set-UVMWorkingDirectory` - UVMディレクトリに移動
- `Set-RTLWorkingDirectory` - RTLディレクトリに移動
- `Set-WorkspaceRoot` - ワークスペースルートに移動
- `Test-WorkspaceMCPUVM` - MCP-UVM機能確認
- `Show-WorkspaceHelp` - ヘルプ表示

### MCP-UVM機能（workspace_init.ps1実行後）
- `Invoke-MCPUVMTest` - UVMテスト実行
- `Invoke-MCPUVMQuickTest` - 高速テスト実行
- `Invoke-MCPUVMCompileOnly` - コンパイルのみ実行
- `Get-MCPUVMStatus` - シミュレーション状態確認
- `Show-MCPUVMHelp` - MCP-UVM専用ヘルプ

## 注意事項
- PowerShellセッションを終了すると、全ての設定がリセットされます
- 新しいPowerShellセッションを開始するたびに `workspace_init.ps1` の実行が必要です
- システム管理者権限は不要です