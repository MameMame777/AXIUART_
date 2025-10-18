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
import logging
import os
import re
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Union, Literal
import argparse
from datetime import datetime

if sys.platform == "win32":
    asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())

# FastMCP 2.12.4 imports
from fastmcp import FastMCP
from dsim_uvm_server import (
    setup_workspace as dsim_setup_workspace,
    check_dsim_environment as dsim_check_environment_async,
    run_uvm_simulation as dsim_run_uvm_simulation_async,
    DSIMError,
)

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
# Core Utility Helpers
# ===============================================================================

def _load_test_metadata(tests_dir: Path) -> List[Dict[str, str]]:
    """Collect metadata for each *_test.sv file in the tests directory."""
    test_entries: List[Dict[str, str]] = []

    for test_file in sorted(tests_dir.glob("*_test.sv")):
        entry: Dict[str, str] = {
            "file": test_file.name,
            "class": test_file.stem,
            "description": "No description available",
            "status": "ok",
        }

        try:
            content = test_file.read_text(encoding="utf-8")
        except Exception as exc:  # pragma: no cover - file IO failure
            entry["description"] = f"Unable to read file ({exc})"
            entry["status"] = "error"
            test_entries.append(entry)
            continue

        class_match = re.search(r"class\s+(\w+)\s+extends", content)
        if class_match:
            entry["class"] = class_match.group(1)

        desc_match = re.search(r"//\s*Description:\s*(.+)", content, re.IGNORECASE)
        if desc_match:
            entry["description"] = desc_match.group(1).strip()

        test_entries.append(entry)

    return test_entries


def _format_test_report(tests_dir: Path, tests: List[Dict[str, str]]) -> str:
    """Generate a human-readable test discovery report."""
    lines: List[str] = [
        "[INFO] Available UVM Tests Discovery Report",
        "=" * 60,
        f"Search Directory: {tests_dir}",
        f"Found {len(tests)} test files",
        "",
    ]

    for index, test in enumerate(tests, 1):
        lines.append(f"{index:2d}. {test['class']}")
        lines.append(f"    File: {test['file']}")
        lines.append(f"    Description: {test['description']}")
        if test["status"] != "ok":
            lines.append(f"    Status: {test['status']}")
        lines.append("")

    lines.append("=" * 60)
    lines.append("[OK] Test Discovery Complete")
    lines.append("[INFO] Use test class names (not file names) with run_uvm_simulation")

    return "\n".join(lines)


def _analyze_simulation_output(output: str, waves: bool) -> Dict[str, Union[bool, str]]:
    """Extract useful status indicators from DSIM output text."""
    has_uvm_errors = "UVM_ERROR" in output and "UVM_ERROR: 0" not in output
    passed = "TEST PASSED" in output or "UVM_ERROR: 0" in output

    return {
        "test_passed": passed,
        "uvm_errors_present": has_uvm_errors,
        "waveform_hint": waves and (".mxd" in output.lower() or "waves" in output.lower()),
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
    
    workspace = get_workspace_path()
    dsim_setup_workspace(str(workspace))

    async def _execute_simulation(
        test_name: str,
        mode: Literal["compile", "run", "elaborate"],
        verbosity: Literal[
            "UVM_NONE",
            "UVM_LOW",
            "UVM_MEDIUM",
            "UVM_HIGH",
            "UVM_FULL",
            "UVM_DEBUG",
        ],
        waves: bool,
        coverage: bool,
        seed: Optional[int],
        timeout: int,
        plusargs: Optional[List[str]] = None,
    ) -> Dict[str, Any]:
        effective_seed = seed if seed is not None else 1

        try:
            output_text = await dsim_run_uvm_simulation_async(
                test_name=test_name,
                mode=mode,
                verbosity=verbosity,
                waves=waves,
                coverage=coverage,
                seed=effective_seed,
                timeout=timeout,
                plusargs=plusargs,
            )
        except DSIMError as exc:  # pragma: no cover - delegated diagnostics
            return {
                "status": "error",
                "error_type": exc.error_type,
                "message": exc.message,
                "suggestion": exc.suggestion,
                "exit_code": exc.exit_code if exc.exit_code is not None else -1,
            }

        analysis = _analyze_simulation_output(output_text, waves)

        return {
            "status": "success",
            "output": output_text,
            "analysis": analysis,
            "test_name": test_name,
            "mode": mode,
            "verbosity": verbosity,
            "waves": waves,
            "coverage": coverage,
            "seed": effective_seed,
            "timeout": timeout,
            "plusargs": plusargs or [],
        }

    @mcp.tool
    async def check_dsim_environment() -> Dict[str, Any]:
        """Run the DSIM environment diagnostic using the unified server."""
        try:
            report_text = await dsim_check_environment_async()
            return {
                "status": "success",
                "report": report_text,
                "environment_variables": {
                    "DSIM_HOME": os.environ.get("DSIM_HOME", ""),
                    "DSIM_ROOT": os.environ.get("DSIM_ROOT", ""),
                    "DSIM_LIB_PATH": os.environ.get("DSIM_LIB_PATH", ""),
                    "DSIM_LICENSE": os.environ.get("DSIM_LICENSE", ""),
                },
            }
        except DSIMError as exc:  # pragma: no cover - delegated diagnostics
            return {
                "status": "error",
                "error_type": exc.error_type,
                "message": exc.message,
                "suggestion": exc.suggestion,
                "exit_code": exc.exit_code if exc.exit_code is not None else -1,
            }

    @mcp.tool
    def list_available_tests() -> Dict[str, Any]:
        """Enumerate available UVM tests without spawning helper scripts."""
        tests_dir = workspace / "sim" / "uvm" / "tests"

        if not tests_dir.exists():
            return {
                "status": "error",
                "message": f"UVM tests directory not found: {tests_dir}",
                "tests": [],
                "total_count": 0,
            }

        tests = _load_test_metadata(tests_dir)
        report = _format_test_report(tests_dir, tests)

        ok_tests = [test for test in tests if test["status"] == "ok"]

        return {
            "status": "success",
            "total_count": len(ok_tests),
            "tests": tests,
            "report": report,
        }

    @mcp.tool
    async def run_uvm_simulation(
        test_name: str,
        mode: Literal["compile", "run", "elaborate"] = "run",
        verbosity: Literal[
            "UVM_NONE",
            "UVM_LOW",
            "UVM_MEDIUM",
            "UVM_HIGH",
            "UVM_FULL",
            "UVM_DEBUG",
    ] = "UVM_MEDIUM",
    waves: bool = False,
        coverage: bool = False,
        seed: Optional[int] = None,
        timeout: int = 300,
        plusargs: Optional[List[str]] = None,
    ) -> Dict[str, Any]:
        """Execute a DSIM UVM simulation via the unified async API."""
        return await _execute_simulation(
            test_name=test_name,
            mode=mode,
            verbosity=verbosity,
            waves=waves,
            coverage=coverage,
            seed=seed,
            timeout=timeout,
            plusargs=plusargs,
        )

    @mcp.tool
    async def compile_design_only(
        test_name: str,
        verbosity: Literal["UVM_NONE", "UVM_LOW", "UVM_MEDIUM", "UVM_HIGH"] = "UVM_LOW",
        timeout: int = 120,
    ) -> Dict[str, Any]:
        """Run a compile-only pass using the unified simulation path."""
        return await _execute_simulation(
            test_name=test_name,
            mode="compile",
            verbosity=verbosity,
            waves=False,
            coverage=False,
            seed=1,
            timeout=timeout,
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
        logs_data: Dict[str, Any] = {
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