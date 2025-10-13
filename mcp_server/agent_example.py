# MCP + Agent AI環境 使用方法ガイド

## 🎯 3つの使用レベル

### 🚀 **レベル1：Agent AI最適化（推奨）**

#### **基本使用パターン**
```bash
# ワークスペースに移動
cd e:\Nautilus\workspace\fpgawork\AXIUART_

# 環境確認（必須）
python mcp_server/mcp_client.py --workspace . --tool check_dsim_environment

# 利用可能テスト確認
python mcp_server/mcp_client.py --workspace . --tool list_available_tests
```

#### **原子的Tool使用（Agent最適化）**
```bash
# 1. デザインコンパイル（高速）
python mcp_server/mcp_client.py --workspace . --tool compile_design \
  --test-name uart_axi4_basic_test --verbosity UVM_LOW --timeout 120

# 2. シミュレーション実行
python mcp_server/mcp_client.py --workspace . --tool run_simulation \
  --test-name uart_axi4_basic_test --verbosity UVM_MEDIUM --timeout 300

# 3. 波形生成（デバッグ用）
python mcp_server/mcp_client.py --workspace . --tool generate_waveforms \
  --test-name uart_axi4_basic_test --format mxd --depth all

# 4. カバレッジ収集（解析用）
python mcp_server/mcp_client.py --workspace . --tool collect_coverage \
  --test-name uart_axi4_basic_test
```

#### **Agent自動化例**
```python
# Agent AIが実行可能なワークフロー
async def agent_verification_workflow(test_name):
    # Step 1: 環境確認
    env_result = await agent.call_tool("check_dsim_environment", {})
    
    # Step 2: コンパイル
    compile_result = await agent.call_tool("compile_design", {
        "test_name": test_name,
        "verbosity": "UVM_LOW"
    })
    
    # Step 3: シミュレーション実行
    if compile_result.success:
        sim_result = await agent.call_tool("run_simulation", {
            "test_name": test_name,
            "verbosity": "UVM_MEDIUM"
        })
    
    # Step 4: 結果解析
    if sim_result.success:
        coverage_result = await agent.call_tool("collect_coverage", {
            "test_name": test_name
        })
    
    return analysis_report
```

---

### ⚡ **レベル2：VSCodeタスク（GUI操作）**

#### **利用可能なMCPタスク**
VSCodeで `Ctrl+Shift+P` → `Tasks: Run Task` を選択：

1. **DSIM: Check Environment (MCP)** - 環境確認
2. **DSIM: List Available Tests (MCP)** - テスト一覧
3. **DSIM: Run Basic Test (Compile Only - MCP)** - コンパイルテスト
4. **DSIM: Run Basic Test (Full Simulation - MCP)** - フルシミュレーション

#### **タスク実行手順**
1. VSCode開起動（MCPサーバー自動起動）
2. `Ctrl+Shift+P` でコマンドパレット開く
3. `Tasks: Run Task` 選択
4. 目的のMCPタスクを選択
5. 結果をターミナルで確認

---

### 🔧 **レベル3：レガシー互換（非推奨）**

#### **直接実行（非推奨警告付き）**
```bash
# ⚠️ 非推奨：直接スクリプト実行
python mcp_server/run_uvm_simulation.py --test_name uart_axi4_basic_test --mode compile

# 警告メッセージが表示されます：
# "Direct script execution is deprecated. Use MCP client instead."
```

---

## 📋 **実際の使用例**

### **シナリオ1：基本的な検証作業**

```bash
# 1. 環境確認
python mcp_server/mcp_client.py --workspace . --tool check_dsim_environment
# 出力: [OK] DSIM_HOME, [OK] UVM Directory, etc.

# 2. 利用可能テスト確認
python mcp_server/mcp_client.py --workspace . --tool list_available_tests
# 出力: uart_axi4_basic_test, uart_axi4_comprehensive_test, etc.

# 3. 基本テスト実行
python mcp_server/mcp_client.py --workspace . --tool run_simulation \
  --test-name uart_axi4_basic_test --verbosity UVM_MEDIUM
```

### **シナリオ2：デバッグ作業**

```bash
# 1. コンパイル確認
python mcp_server/mcp_client.py --workspace . --tool compile_design \
  --test-name uart_axi4_basic_test

# 2. 波形付きシミュレーション
python mcp_server/mcp_client.py --workspace . --tool generate_waveforms \
  --test-name uart_axi4_basic_test --format mxd

# 3. 波形ファイル確認
ls sim/exec/*.mxd
```

### **シナリオ3：カバレッジ解析**

```bash
# 1. カバレッジ付きテスト実行
python mcp_server/mcp_client.py --workspace . --tool collect_coverage \
  --test-name uart_axi4_comprehensive_test

# 2. カバレッジレポート生成
python mcp_server/mcp_client.py --workspace . --tool generate_coverage_report \
  --format html
```

---

## 🎯 **Agent AI開発者向け使用方法**

### **MCP プロトコル直接使用**

真のAgent AIでは、MCPプロトコルを直接使用します：

<function_calls>
<invoke name="create_file">
<parameter name="content">#!/usr/bin/env python3
"""
Agent AI向けMCP使用例
真のModel Context Protocol通信でのUVM検証自動化
"""

import asyncio
from mcp.client.session import ClientSession
from mcp.client.stdio import stdio_client
import subprocess
import sys

async def agent_mcp_example():
    """Agent AIがMCPサーバーを直接使用する例"""
    
    # MCPサーバー起動
    server_cmd = [
        sys.executable,
        "mcp_server/dsim_uvm_server.py", 
        "--workspace", "."
    ]
    
    server_process = subprocess.Popen(
        server_cmd,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True
    )
    
    try:
        # MCP接続
        async with stdio_client(server_process.stdout, server_process.stdin) as (read_stream, write_stream):
            session = ClientSession(read_stream, write_stream)
            await session.initialize()
            
            # Tool一覧取得
            tools = await session.list_tools()
            print(f"Available tools: {[tool.name for tool in tools.tools]}")
            
            # 環境確認
            env_result = await session.call_tool("check_dsim_environment", {})
            print("Environment check:", env_result.content[0].text)
            
            # 原子的Tool使用例
            # 1. コンパイル
            compile_result = await session.call_tool("compile_design", {
                "test_name": "uart_axi4_basic_test",
                "verbosity": "UVM_LOW",
                "timeout": 120
            })
            
            # 2. シミュレーション実行
            if "SUCCESS" in compile_result.content[0].text:
                sim_result = await session.call_tool("run_simulation", {
                    "test_name": "uart_axi4_basic_test",
                    "verbosity": "UVM_MEDIUM",
                    "timeout": 300
                })
                
                # 3. カバレッジ収集
                if "SUCCESS" in sim_result.content[0].text:
                    coverage_result = await session.call_tool("collect_coverage", {
                        "test_name": "uart_axi4_basic_test",
                        "coverage_types": ["line", "branch", "toggle"]
                    })
                    
                    print("Coverage result:", coverage_result.content[0].text)
    
    finally:
        server_process.terminate()

if __name__ == "__main__":
    asyncio.run(agent_mcp_example())