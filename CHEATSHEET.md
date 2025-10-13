# 🚀 FastMCP Enhanced環境 - 作業者向けチートシート (Phase 1)

## **⚡ 基本コマンド（コピペ用）- 最新版**

### **⭐ 超高速環境確認（推奨）**
```bash
# 全ツールテスト（最速）
python mcp_server/dsim_uvm_server.py --workspace . --test-tools
```

### **🔍 詳細診断（デバッグ用）**
```bash
# 環境確認 + テスト一覧を一括取得
python -c "
import asyncio
from mcp_server.dsim_uvm_server import setup_workspace, check_dsim_environment, list_available_tests
setup_workspace('.')
print('=== Environment ===')
print(asyncio.run(check_dsim_environment()))
print('\n=== 48+ Available Tests ===')
print(asyncio.run(list_available_tests()))
"
```

### **⚡ Legacy MCP Client（互換性維持）**
```bash
# 基本実行（従来通り）
python mcp_server/mcp_client.py --workspace . --tool check_dsim_environment
python mcp_server/mcp_client.py --workspace . --tool compile_design --test-name uart_axi4_basic_test
python mcp_server/mcp_client.py --workspace . --tool run_simulation --test-name uart_axi4_basic_test
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