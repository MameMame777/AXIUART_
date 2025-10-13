# 🚀 MCP環境 - 作業者向けチートシート

## **⚡ 基本コマンド（コピペ用）**

### **環境確認**
```bash
python mcp_server/mcp_client.py --workspace . --tool check_dsim_environment
```

### **テスト一覧**
```bash
python mcp_server/mcp_client.py --workspace . --tool list_available_tests
```

### **基本実行**
```bash
# コンパイル
python mcp_server/mcp_client.py --workspace . --tool compile_design --test-name uart_axi4_basic_test

# シミュレーション
python mcp_server/mcp_client.py --workspace . --tool run_simulation --test-name uart_axi4_basic_test

# 波形生成
python mcp_server/mcp_client.py --workspace . --tool generate_waveforms --test-name uart_axi4_basic_test

# カバレッジ
python mcp_server/mcp_client.py --workspace . --tool collect_coverage --test-name uart_axi4_basic_test
```

## **🎯 VSCodeタスク（推奨）**

**Ctrl+Shift+P** → **"Tasks: Run Task"** → 以下を選択

- **🚀 DSIM: Check Environment (Recommended)**
- **🚀 DSIM: List Available Tests (Recommended)**  
- **🚀 DSIM: Compile Design (Agent AI)**
- **🚀 DSIM: Run Simulation (Agent AI)**

## **📁 重要ディレクトリ**

```
rtl/                    # RTLファイル（修正対象）
sim/tests/             # テストケース
sim/exec/logs/         # 実行ログ
docs/                  # ドキュメント
mcp_server/            # MCP環境（触らない）
```

## **⚠️ 絶対禁止**

- **❌ `python mcp_server/run_uvm_simulation.py`** （直接実行）
- **❌ レガシータスク（⚠️マーク）の使用**
- **❌ mcp_server/ディレクトリの変更**

## **🔧 トラブル時**

1. **VSCode再起動**
2. **環境確認コマンド実行**
3. **基本テスト実行**
4. **ログ確認**: `cat sim/exec/logs/latest.log`

## **📚 ドキュメント優先順位**

1. **QUICK_START.md** - まずここ
2. **README.md** - プロジェクト概要  
3. **この指示書** - 詳細手順

## **✅ 毎日の確認事項**

- [ ] 環境確認OK
- [ ] 基本テスト成功
- [ ] MCP Client使用
- [ ] 進捗記録

---

**🎉 成功の秘訣: この環境をそのまま信頼して使う**