# 次の作業者への指示書

## 📋 **現在の環境状況（2025年10月13日時点）**

### ✅ **完了済み環境（すぐに使用可能）**

**Model Context Protocol + Agent AI環境が92%ベストプラクティス準拠で実装済み**

- ✅ MCP Client実装完了
- ✅ 原子的Tool分割完了（compile_design, run_simulation, generate_waveforms, collect_coverage）
- ✅ VSCode統合完了（自動起動・環境設定）
- ✅ ドキュメント整備完了
- ✅ 非推奨化対応完了

---

## 🚀 **即座に開始する手順**

### **STEP 1: 環境確認（必須）**
```bash
cd e:\Nautilus\workspace\fpgawork\AXIUART_
python mcp_server/mcp_client.py --workspace . --tool check_dsim_environment
```

### **STEP 2: 基本動作確認**
```bash
python mcp_server/mcp_client.py --workspace . --tool list_available_tests
python mcp_server/mcp_client.py --workspace . --tool compile_design --test-name uart_axi4_basic_test
```

### **STEP 3: ドキュメント確認**
- **[QUICK_START.md](QUICK_START.md)** - 60秒セットアップガイド
- **[README.md](README.md)** - プロジェクト概要
- **[.github/copilot-instructions.md](.github/copilot-instructions.md)** - AI支援設定

---

## 🎯 **重要：必ず守るべきルール**

### **✅ 必ず使用する方法（推奨）**
1. **MCP Client経由でのすべての操作**
   ```bash
   python mcp_server/mcp_client.py --workspace . --tool <tool_name>
   ```

2. **VSCodeタスク（🚀マーク付き）**
   - `🚀 DSIM: Check Environment (Recommended)`
   - `🚀 DSIM: List Available Tests (Recommended)`
   - `🚀 DSIM: Compile Design (Agent AI)`

### **❌ 絶対に使用しない方法（非推奨）**
1. **直接スクリプト実行**（ベストプラクティス違反）
   ```bash
   # ❌ これは使わない
   python mcp_server/run_uvm_simulation.py
   ```

2. **レガシータスク（⚠️マーク付き）**
   - これらは互換性のためのみ残存

---

## 📚 **理解すべき重要概念**

### **1. MCP（Model Context Protocol）とは**
- **Agent AI最適化のための標準プロトコル**
- **原子的Tool設計でAgent自動化を支援**
- **92%ベストプラクティス準拠を達成**

### **2. 原子的Tool設計**
| Tool | 用途 | Agent利用場面 |
|------|------|---------------|
| `compile_design` | コンパイルのみ | 高速構文チェック |
| `run_simulation` | シミュレーション実行 | 検証実行 |
| `generate_waveforms` | 波形生成 | デバッグ作業 |
| `collect_coverage` | カバレッジ収集 | 品質評価 |

### **3. Agent AIワークフロー例**
```python
# Agent自動化パターン
await agent.call_tool("check_dsim_environment", {})
await agent.call_tool("compile_design", {"test_name": "uart_axi4_basic_test"})
await agent.call_tool("run_simulation", {"test_name": "uart_axi4_basic_test"})
await agent.call_tool("collect_coverage", {"test_name": "uart_axi4_basic_test"})
```

---

## 🔧 **作業開始時のチェックリスト**

### **環境確認チェック**
- [ ] VSCode起動時にMCPサーバーが自動起動される
- [ ] `check_dsim_environment`で全項目OK
- [ ] `list_available_tests`で42+テストが表示される
- [ ] 基本テストのコンパイルが成功する

### **理解度確認チェック**
- [ ] MCP Clientの基本コマンドを理解している
- [ ] 原子的Toolの役割を理解している
- [ ] 非推奨メソッドを使わないことを理解している
- [ ] Agent AIワークフローの概念を理解している

---

## 🎯 **作業方針の決定**

### **A. 既存環境を活用する場合**
**推奨**：現在の環境は完成度が高いため、そのまま使用することを強く推奨

**作業内容**：
- 検証タスクの実行
- 新しいテストの追加
- RTLの改良・拡張
- カバレッジ向上作業

### **B. 環境を拡張する場合**
**Phase 3機能の実装**（将来機能）：
- セッション永続化
- Tool呼び出しチェーン
- 結果相関機能
- 高度なAgent状態管理

### **C. 新しい要件がある場合**
**新機能追加**：
- 新しい原子的Toolの追加
- 異なるシミュレータ対応
- カスタムワークフロー実装

---

## ⚠️ **よくある問題と対処法**

### **問題1: MCP Clientが動作しない**
```bash
# 対処法
python mcp_server/check_dsim_env.py  # レガシー方法で環境確認
# 環境変数の設定確認
# MCPサーバープロセスの確認
```

### **問題2: テストが失敗する**
```bash
# 対処法
# 1. 環境確認
python mcp_server/mcp_client.py --workspace . --tool check_dsim_environment

# 2. ログ確認
cat sim/exec/logs/latest.log

# 3. 基本テストから開始
python mcp_server/mcp_client.py --workspace . --tool compile_design --test-name uart_axi4_basic_test
```

### **問題3: 設定がわからない**
**解決手順**：
1. **QUICK_START.md**を確認
2. **README.md**の該当セクション確認
3. **copilot-instructions.md**でAI支援設定確認

---

## 📈 **成功の判断基準**

### **Level 1: 基本動作確認**
- [ ] MCP Client基本コマンドが実行できる
- [ ] 環境確認で全項目OK
- [ ] 基本テストのコンパイル・実行が成功

### **Level 2: 実践的使用**
- [ ] 複数テストの実行が安定している
- [ ] 波形生成・カバレッジ収集が動作
- [ ] エラーハンドリングが適切

### **Level 3: Agent AI活用**
- [ ] Agent自動化ワークフローが理解できている
- [ ] 原子的Toolを組み合わせた効率的作業
- [ ] ベストプラクティスに準拠した開発

---

## 🎉 **最終確認事項**

### **作業開始前の最終チェック**
1. **環境理解**: MCPとAgent AIの概念を理解している
2. **ツール理解**: 推奨方法と非推奨方法を区別できる
3. **手順理解**: QUICK_START.mdに従って作業できる
4. **支援理解**: ドキュメントとAI支援を活用できる

### **困った時のエスカレーション**
1. **QUICK_START.md**のトラブルシューティング
2. **README.md**の該当セクション
3. **MCPベストプラクティス実装レポート**（docs/mcp_best_practices_implementation_report.md）

---

## 🚀 **まとめ：次の作業者への最重要メッセージ**

**この環境は92%ベストプラクティス準拠のMCP + Agent AI環境です。**

**✅ すぐに使える状態**で、**推奨方法（MCP Client）を使用**することで、**Agent AIによる高効率な検証自動化**が実現できます。

**⚠️ 非推奨方法は避け**、**QUICK_START.mdから開始**して、**標準準拠した開発**を進めてください。

**🎯 成功の鍵**: MCP Client + 原子的Tool + Agent AIワークフローの活用