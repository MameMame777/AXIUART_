# DSIM UVM Model Context Protocol (MCP) Server

## 概要

このMCPサーバーは、DSIM SystemVerilog UVMシミュレーションを Model Context Protocol (MCP) を通じて実行できるようにします。従来のPowerShellスクリプトベースのアプローチに代わり、標準化されたMCPインターフェースを提供します。

## 特徴

### 🚀 主要機能
- **UVMシミュレーション実行**: 完全なDSIMシミュレーション制御
- **環境検証**: DSIM環境の自動検証
- **テスト発見**: 利用可能なUVMテストの自動検出
- **ログ管理**: シミュレーションログの取得と分析
- **カバレッジレポート**: 自動カバレッジレポート生成

### 🛠️ MCPツール一覧

1. **run_uvm_simulation**
   - DSIMを使用したUVMシミュレーション実行
   - パラメータ: test_name, mode, verbosity, waves, coverage, seed, timeout

2. **check_dsim_environment**
   - DSIM環境設定の検証
   - DSIM_HOME、実行ファイル、ライセンスの確認

3. **list_available_tests**
   - プロジェクト内の利用可能なUVMテストクラス一覧

4. **get_simulation_logs**
   - シミュレーションログの取得と分析
   - パラメータ: log_type, test_name

5. **generate_coverage_report**
   - カバレッジ分析レポートの生成
   - パラメータ: format (html/text/xml)

## セットアップ

### 1. 依存関係のインストール

```powershell
cd e:\Nautilus\workspace\fpgawork\AXIUART_\mcp_server
python setup.py
```

### 2. 環境変数の設定

以下の環境変数が必要です：

```
DSIM_HOME=C:\Users\Nautilus\AppData\Local\metrics-ca\dsim\20240422.0.0
DSIM_ROOT=C:\Users\Nautilus\AppData\Local\metrics-ca\dsim\20240422.0.0
DSIM_LIB_PATH=C:\Users\Nautilus\AppData\Local\metrics-ca\dsim\20240422.0.0\lib
```

### 3. MCPサーバー起動

#### 方法1: 直接起動
```powershell
python dsim_uvm_server.py --workspace e:\Nautilus\workspace\fpgawork\AXIUART_
```

#### 方法2: ランチャースクリプト使用
```powershell
start_mcp_server.bat
```

## 使用方法

### MCP設定ファイル

`mcp_config.json`を参考にMCPクライアントを設定：

```json
{
  "mcpServers": {
    "dsim-uvm": {
      "command": "python",
      "args": [
        "e:\\Nautilus\\workspace\\fpgawork\\AXIUART_\\mcp_server\\dsim_uvm_server.py",
        "--workspace",
        "e:\\Nautilus\\workspace\\fpgawork\\AXIUART_"
      ]
    }
  }
}
```

### ツール使用例

#### 基本的なUVMテスト実行
```json
{
  "name": "run_uvm_simulation",
  "arguments": {
    "test_name": "uart_axi4_basic_test",
    "mode": "run",
    "verbosity": "UVM_MEDIUM",
    "waves": true,
    "coverage": true
  }
}
```

#### 環境確認
```json
{
  "name": "check_dsim_environment",
  "arguments": {}
}
```

#### カバレッジレポート生成
```json
{
  "name": "generate_coverage_report",
  "arguments": {
    "format": "html"
  }
}
```

## 従来システムとの比較

### 従来のPowerShell "MCP-UVM"システム
- ✅ ワークスペース固有の設定
- ✅ 簡単なセットアップ
- ❌ 標準化されていないインターフェース
- ❌ プラットフォーム依存

### 新しいMCPサーバー
- ✅ 標準化されたModel Context Protocol
- ✅ プラットフォーム独立
- ✅ 拡張性の高いアーキテクチャ
- ✅ 他のMCPクライアントとの統合可能
- ⚠️ 初期セットアップがやや複雑

## トラブルシューティング

### MCPパッケージインポートエラー
```powershell
pip install mcp
```

### DSIM環境エラー
1. DSIM_HOME環境変数を確認
2. DSIMライセンスファイルの確認
3. `check_dsim_environment`ツールで詳細診断

### シミュレーション実行エラー
1. dsim_config.fファイルの存在確認
2. テストファイルのパス確認
3. ログファイルでエラー詳細確認

## 開発者情報

### ファイル構成
```
mcp_server/
├── dsim_uvm_server.py      # メインMCPサーバー
├── setup.py                # セットアップスクリプト
├── requirements.txt        # Python依存関係
├── mcp_config.json        # MCP設定例
├── start_mcp_server.bat   # Windows起動スクリプト
└── README.md              # このファイル
```

### 拡張方法
1. `DSIMSimulationServer`クラスに新しいメソッド追加
2. `_setup_tools()`で新しいツール登録
3. 対応するハンドラー実装

### ログレベル調整
```python
logging.basicConfig(level=logging.DEBUG)  # 詳細ログ
```

## 参考資料

- [Model Context Protocol仕様](https://modelcontextprotocol.io/)
- [DSIM User Manual](https://help.metrics.ca/support/solutions/articles/154000141193-user-guide-dsim-user-manual)
- [UVM Verification Plan](../docs/uvm_verification_plan.md)