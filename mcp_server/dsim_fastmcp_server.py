#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FastMCP Unified DSIM Server - Production Ready Implementation
完全統一されたFastMCP 2.12.4ベースのDSIM UVMサーバー

Created: October 14, 2025
Architecture: FastMCP 2.12.4 → Unified Tools → DSIM Environment
Purpose: 実用的な専門家レベルのMCPサーバー実装
"""

import asyncio
import json
import logging
import os
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Union, Literal
import argparse
from datetime import datetime

if sys.platform == "win32":
    asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())

# FastMCP 2.12.4 imports
from fastmcp import FastMCP

# Configure logging 
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[logging.StreamHandler(sys.stderr)]
)
logger = logging.getLogger("dsim-fastmcp-unified")

# ===============================================================================
# Global State Management
# ===============================================================================

# Global workspace path
_workspace_path: Optional[Path] = None

def set_workspace_path(path: str) -> None:
    """Set the global workspace path"""
    global _workspace_path
    _workspace_path = Path(path)

def get_workspace_path() -> Path:
    """Get the global workspace path"""
    if _workspace_path is None:
        raise ValueError("Workspace path not initialized")
    return _workspace_path

# ===============================================================================
# Core Utility Functions
# ===============================================================================

def call_existing_script(script_name: str, args: List[str]) -> Dict[str, Any]:
    """
    既存のPythonスクリプトを呼び出し、結果を構造化して返す
    """
    try:
        workspace = get_workspace_path()
        script_path = workspace / "mcp_server" / script_name
        cmd = [sys.executable, str(script_path)] + args
        
        logger.info(f"Executing: {' '.join(cmd)}")
        
        result = subprocess.run(
            cmd, 
            capture_output=True, 
            text=True, 
            timeout=300,
            cwd=str(workspace)
        )
        
        return {
            "success": result.returncode == 0,
            "exit_code": result.returncode,
            "stdout": result.stdout,
            "stderr": result.stderr,
            "command": ' '.join(cmd),
            "timestamp": datetime.now().isoformat()
        }
        
    except subprocess.TimeoutExpired:
        return {
            "success": False,
            "exit_code": -1,
            "stdout": "",
            "stderr": "Command timed out after 300 seconds",
            "command": script_name,
            "timestamp": datetime.now().isoformat()
        }
    except Exception as e:
        return {
            "success": False,
            "exit_code": -1,
            "stdout": "",
            "stderr": f"Execution error: {str(e)}",
            "command": script_name,
            "timestamp": datetime.now().isoformat()
        }

# ===============================================================================
# FastMCP Server and Tools Setup
# ===============================================================================

def create_fastmcp_server() -> FastMCP:
    """
    FastMCP サーバーを専門家レベルの設定で作成
    """
    mcp = FastMCP(
        name="DSIM-UVM-Unified-Server",
        instructions="""
        統一DSIM UVMシミュレーション環境サーバー。
        
        このサーバーは以下の機能を提供します：
        - DSIM環境の自動検証と診断
        - UVMテストの実行とコンパイル
        - 波形生成（MXD形式）とカバレッジ収集
        - テスト一覧とステータス監視
        - エラー診断と推奨事項
        
        実行方式：
        1. 環境確認 → 2. テスト選択 → 3. 実行 → 4. 結果確認
        """
    )
    
    # ===============================================================================
    # Tool Definitions
    # ===============================================================================
    
    @mcp.tool
    def check_dsim_environment() -> Dict[str, Any]:
        """
        DSIM環境の詳細診断を実行
        
        Returns:
            環境ステータスの詳細情報
        """
        result = call_existing_script("check_dsim_env.py", [])
        
        # 既存スクリプトの出力を解析してStructured Dataを作成
        if result["success"]:
            # 成功時の詳細解析
            status_data = {
                "status": "OK",
                "dsim_home": os.environ.get("DSIM_HOME"),
                "dsim_license": os.environ.get("DSIM_LICENSE"),
                "details": {
                    "raw_output": result["stdout"],
                    "environment_variables": {
                        "DSIM_HOME": os.environ.get("DSIM_HOME"),
                        "DSIM_ROOT": os.environ.get("DSIM_ROOT"),
                        "DSIM_LIB_PATH": os.environ.get("DSIM_LIB_PATH")
                    }
                },
                "recommendations": ["Environment properly configured"]
            }
        else:
            # エラー時の診断
            status_data = {
                "status": "ERROR",
                "dsim_home": os.environ.get("DSIM_HOME"),
                "dsim_license": os.environ.get("DSIM_LICENSE"),
                "details": {
                    "error_output": result["stderr"],
                    "exit_code": result["exit_code"]
                },
                "recommendations": [
                    "Check DSIM_HOME environment variable",
                    "Verify DSIM installation",
                    "Check license configuration"
                ]
            }
        
        return status_data

    @mcp.tool
    def list_available_tests() -> Dict[str, Any]:
        """
        利用可能なUVMテストの一覧を取得
        
        Returns:
            テスト一覧とメタデータ
        """
        result = call_existing_script("list_available_tests.py", [])
        
        if result["success"]:
            # テスト一覧の解析（既存スクリプトの出力形式に合わせて）
            tests_data = {
                "status": "success",
                "tests": [],
                "total_count": 0,
                "categories": ["basic", "advanced", "stress"],
                "raw_output": result["stdout"]
            }
            
            # 出力からテスト名を抽出（既存スクリプトの出力形式を解析）
            lines = result["stdout"].split('\n')
            test_names = []
            for line in lines:
                if "test" in line.lower() and line.strip():
                    test_names.append(line.strip())
            
            tests_data["tests"] = test_names
            tests_data["total_count"] = len(test_names)
            
        else:
            tests_data = {
                "status": "error",
                "tests": [],
                "total_count": 0,
                "error": result["stderr"]
            }
        
        return tests_data

    @mcp.tool
    def run_uvm_simulation(
        test_name: str,
        mode: str = "run",
        verbosity: str = "UVM_MEDIUM",
        waves: bool = True,
        coverage: bool = False,
        seed: Optional[int] = None,
        timeout: int = 300
    ) -> Dict[str, Any]:
        """
        UVMシミュレーションを実行（既存のrun_uvm_simulation.pyを活用）
        
        Args:
            test_name: テスト名
            mode: 実行モード ("compile" または "run")
            verbosity: UVM詳細レベル
            waves: 波形生成を有効化
            coverage: カバレッジ収集を有効化  
            seed: ランダムシード
            timeout: タイムアウト秒数
            
        Returns:
            シミュレーション実行結果
        """
        # 既存スクリプトの引数形式に変換
        args = [
            "--test_name", test_name,
            "--mode", mode,
            "--verbosity", verbosity,
            "--timeout", str(timeout)
        ]
        
        if waves:
            args.append("--waves")
        if coverage:
            args.append("--coverage")
        if seed is not None:
            args.extend(["--seed", str(seed)])
        
        result = call_existing_script("run_uvm_simulation.py", args)
        
        # 結果の拡張（FastMCP用の構造化）
        enhanced_result = {
            **result,
            "test_name": test_name,
            "mode": mode,
            "verbosity": verbosity,
            "waveforms_enabled": waves,
            "coverage_enabled": coverage,
            "seed": seed
        }
        
        # 成功/失敗の詳細解析
        if result["success"]:
            enhanced_result["analysis"] = {
                "compilation_status": "PASS" if "compilation" in result["stdout"].lower() else "UNKNOWN",
                "simulation_status": "PASS" if "UVM_ERROR: 0" in result["stdout"] else "CHECK_REQUIRED",
                "waveform_generated": waves and "mxd" in result["stdout"].lower()
            }
        else:
            enhanced_result["analysis"] = {
                "error_type": "RUNTIME_ERROR" if result["exit_code"] != 0 else "UNKNOWN",
                "suggested_actions": [
                    "Check test name spelling",
                    "Verify DSIM environment",
                    "Review error messages in stderr"
                ]
            }
        
        return enhanced_result

    @mcp.tool
    def compile_design_only(
        test_name: str, 
        verbosity: str = "UVM_LOW", 
        timeout: int = 120
    ) -> Dict[str, Any]:
        """
        設計のコンパイルのみを実行（高速構文チェック用）
        
        Args:
            test_name: テスト名
            verbosity: 詳細レベル  
            timeout: タイムアウト秒数
            
        Returns:
            コンパイル結果
        """
        return run_uvm_simulation(
            test_name=test_name,
            mode="compile",
            verbosity=verbosity,
            waves=False,
            coverage=False,
            timeout=timeout
        )

    @mcp.tool  
    def get_simulation_logs(log_type: str = "latest") -> Dict[str, Any]:
        """
        シミュレーションログの取得と解析
        
        Args:
            log_type: 取得するログの種類 ("latest", "all", "errors")
            
        Returns:
            ログデータ
        """
        logs_data = {
            "log_type": log_type,
            "timestamp": datetime.now().isoformat(),
            "logs": [],
            "summary": {}
        }
        
        try:
            # シミュレーションディレクトリのログファイルを探索
            workspace = get_workspace_path()
            sim_dir = workspace / "sim" / "exec"
            if sim_dir.exists():
                log_files = list(sim_dir.glob("*.log"))
                log_files.extend(sim_dir.glob("dsim.log"))
                
                for log_file in log_files:
                    if log_file.exists():
                        with open(log_file, 'r', encoding='utf-8', errors='ignore') as f:
                            content = f.read()
                            logs_data["logs"].append({
                                "file": str(log_file.name),
                                "content": content[-2000:],  # 最後の2000文字
                                "size": len(content)
                            })
                
                logs_data["summary"] = {
                    "files_found": len(log_files),
                    "status": "success"
                }
            else:
                logs_data["summary"] = {
                    "files_found": 0,
                    "status": "no_simulation_directory",
                    "message": f"Simulation directory not found: {sim_dir}"
                }
                
        except Exception as e:
            logs_data["summary"] = {
                "status": "error",
                "error": str(e)
            }
        
        return logs_data

    return mcp

# ===============================================================================
# Server Execution and Configuration
# ===============================================================================

def main():
    """メイン実行関数"""
    parser = argparse.ArgumentParser(description="FastMCP Unified DSIM Server")
    parser.add_argument("--workspace", required=True, help="Workspace directory path")
    parser.add_argument("--transport", choices=["stdio", "http"], default="stdio", 
                       help="Transport method")
    parser.add_argument("--host", default="localhost", help="HTTP host (for HTTP transport)")
    parser.add_argument("--port", type=int, default=8000, help="HTTP port (for HTTP transport)")
    parser.add_argument("--debug", action="store_true", help="Enable debug logging")
    
    args = parser.parse_args()
    
    if args.debug:
        logging.getLogger().setLevel(logging.DEBUG)
        logger.debug("Debug logging enabled")
    
    # ワークスペースパスを設定
    set_workspace_path(args.workspace)
    
    # FastMCP server initialization
    mcp = create_fastmcp_server()
    
    logger.info(f"Starting FastMCP Unified Server (transport: {args.transport})")
    logger.info(f"Workspace: {args.workspace}")
    
    # Server execution based on transport
    if args.transport == "stdio":
        logger.info("Starting STDIO transport...")
        try:
            mcp.run(transport="stdio", show_banner=True)
        except KeyboardInterrupt:
            logger.info("Server stopped by user")
        except Exception as e:
            logger.error(f"Server error: {e}")
            sys.exit(1)
    elif args.transport == "http":
        logger.info(f"Starting HTTP transport on {args.host}:{args.port}")
        mcp.run(transport="streamable-http", host=args.host, port=args.port)

if __name__ == "__main__":
    main()