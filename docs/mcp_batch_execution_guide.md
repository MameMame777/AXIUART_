# MCP一括実行機能ガイド

## 📚 概要

MCPサーバーに**バッチ実行機能**を追加しました。コンパイルと実行を自動的に順次実行します。

## 🚀 実行モード

### 1. **バッチモード（推奨・デフォルト）**
コンパイル → 実行を自動実行

```bash
# 基本的な使い方（デフォルトでバッチモード）
python mcp_server/mcp_client.py --workspace . --tool run_uvm_simulation --test-name uart_axi4_basic_test

# 明示的にバッチモードを指定
python mcp_server/mcp_client.py --workspace . --tool run_uvm_simulation --test-name uart_axi4_basic_test --mode batch

# 波形生成とカバレッジ付き
python mcp_server/mcp_client.py --workspace . --tool run_uvm_simulation --test-name uart_axi4_basic_test --mode batch --waves --coverage

# タイムアウトのカスタマイズ
python mcp_server/mcp_client.py --workspace . --tool run_uvm_simulation --test-name uart_axi4_basic_test --mode batch --compile-timeout 180 --timeout 600
```

### 2. **コンパイルのみモード**
コンパイルのみ実行（構文チェック用）

```bash
python mcp_server/mcp_client.py --workspace . --tool run_uvm_simulation --test-name uart_axi4_basic_test --mode compile
```

### 3. **実行のみモード**
既にコンパイル済みのイメージを使って実行

```bash
python mcp_server/mcp_client.py --workspace . --tool run_uvm_simulation --test-name uart_axi4_basic_test --mode run
```

## 🎯 バッチモードの動作フロー

```
┌─────────────────────────────────────────────┐
│ Phase 1: コンパイル (compile_timeout)       │
│   - Verbosity: UVM_LOW                     │
│   - 波形/カバレッジ: 無効                   │
│   - タイムアウト: 120秒（デフォルト）       │
└─────────────────────────────────────────────┘
              ↓ (成功時)
┌─────────────────────────────────────────────┐
│ 待機: 2秒（ライセンス解放待ち）             │
└─────────────────────────────────────────────┘
              ↓
┌─────────────────────────────────────────────┐
│ Phase 2: シミュレーション実行 (run_timeout) │
│   - Verbosity: ユーザー指定                 │
│   - 波形/カバレッジ: ユーザー指定           │
│   - タイムアウト: 300秒（デフォルト）       │
└─────────────────────────────────────────────┘
```

## 📊 パラメータ一覧

| パラメータ | デフォルト | 説明 |
|-----------|----------|------|
| `--mode` | `batch` | 実行モード: `batch`, `compile`, `run` |
| `--test-name` | 必須 | UVMテスト名 |
| `--verbosity` | `UVM_MEDIUM` | UVMログレベル |
| `--waves` | `False` | 波形生成を有効化 |
| `--coverage` | `False` | カバレッジ収集を有効化 |
| `--compile-timeout` | `120` | コンパイルタイムアウト（秒） |
| `--timeout` | `300` | 実行タイムアウト（秒） |
| `--plusarg` | なし | DSIMプラスアーギュメント（複数可） |

## 💡 使用例

### 例1: 基本的なテスト実行
```bash
python mcp_server/mcp_client.py \
  --workspace . \
  --tool run_uvm_simulation \
  --test-name uart_axi4_basic_test
```

### 例2: 詳細ログと波形生成
```bash
python mcp_server/mcp_client.py \
  --workspace . \
  --tool run_uvm_simulation \
  --test-name uart_axi4_basic_test \
  --verbosity UVM_HIGH \
  --waves
```

### 例3: カバレッジ収集付き
```bash
python mcp_server/mcp_client.py \
  --workspace . \
  --tool run_uvm_simulation \
  --test-name uart_axi4_protocol_test \
  --coverage \
  --timeout 600
```

### 例4: コンパイルのみ（構文チェック）
```bash
python mcp_server/mcp_client.py \
  --workspace . \
  --tool run_uvm_simulation \
  --test-name uart_axi4_basic_test \
  --mode compile \
  --compile-timeout 180
```

### 例5: プラスアーギュメント付き
```bash
python mcp_server/mcp_client.py \
  --workspace . \
  --tool run_uvm_simulation \
  --test-name uart_axi4_basic_test \
  --plusarg SIM_TIMEOUT_MS=120000 \
  --plusarg ENABLE_DEBUG=1
```

## 🔧 MCP Server直接呼び出し

MCP Serverを直接使う場合：

```python
# Batch execution (推奨)
result = await session.call_tool("run_uvm_simulation_batch", {
    "test_name": "uart_axi4_basic_test",
    "verbosity": "UVM_MEDIUM",
    "waves": True,
    "coverage": False,
    "compile_timeout": 120,
    "run_timeout": 300
})

# Compile only
result = await session.call_tool("run_uvm_simulation", {
    "test_name": "uart_axi4_basic_test",
    "mode": "compile",
    "verbosity": "UVM_LOW",
    "timeout": 120
})

# Run only
result = await session.call_tool("run_uvm_simulation", {
    "test_name": "uart_axi4_basic_test",
    "mode": "run",
    "verbosity": "UVM_MEDIUM",
    "waves": True,
    "timeout": 300
})
```

## 📋 返却される結果

### バッチモード成功時
```json
{
  "status": "success",
  "phase": "batch_complete",
  "message": "Batch execution completed: compile + run successful",
  "compile_result": { /* コンパイル結果 */ },
  "run_result": { /* 実行結果 */ },
  "test_name": "uart_axi4_basic_test",
  "verbosity": "UVM_MEDIUM",
  "waves": false,
  "coverage": false,
  "seed": 1
}
```

### コンパイル失敗時
```json
{
  "status": "error",
  "phase": "compile",
  "error_type": "compilation_failed",
  "message": "Batch execution aborted: compilation failed",
  "compile_result": { /* エラー詳細 */ },
  "run_result": null
}
```

## ⚠️ 注意事項

1. **ライセンス制限**: DSIM maxLeases=1の環境では、バッチモードでも2秒の待機時間が必要
2. **タイムアウト設定**: 大規模テストでは `--compile-timeout` と `--timeout` を適切に調整
3. **デフォルト動作**: `--mode` を省略すると自動的にバッチモードで実行
4. **後方互換性**: 既存の `--mode compile` / `--mode run` も引き続き使用可能

## 🎉 利点

- ✅ **簡潔なコマンド**: 1回のコマンドで完全なテスト実行
- ✅ **自動ライセンス管理**: コンパイルと実行の間に自動待機
- ✅ **エラーハンドリング**: コンパイル失敗時は実行をスキップ
- ✅ **完全な結果**: 両フェーズの詳細な結果を取得
- ✅ **オプション分離**: 必要に応じてコンパイルのみ/実行のみも可能
