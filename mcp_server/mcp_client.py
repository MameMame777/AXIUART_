#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
MCP Client for DSIM UVM Simulation
Pure Model Context Protocol client implementation for Agent AI integration

Created: October 13, 2025
Purpose: Replace direct script execution with MCP protocol communication
Architecture: Agent AI → MCP Client → MCP Server → DSIM Tools
"""

import asyncio
import logging
import sys
import argparse
from pathlib import Path
import subprocess
import json

# Windows asyncio workaround: use selector event loop to avoid Proactor pipe bugs
if sys.platform == "win32":
    asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())

# Configure stdout/stderr encoding for Windows compatibility
if sys.platform == "win32":
    import io
    sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
    sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding='utf-8')

# MCP Client imports
try:
    from mcp.client.session import ClientSession
    from mcp.client.stdio import stdio_client, StdioServerParameters
    from mcp.types import TextContent
except ImportError as e:
    print(f"Error: MCP client package not found. Install with: pip install mcp", file=sys.stderr)
    sys.exit(1)

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
logger = logging.getLogger("mcp-client")

async def main():
    """Main entry point for MCP client"""
    parser = argparse.ArgumentParser(description="DSIM UVM MCP Client")
    parser.add_argument("--workspace", type=str, default=".", help="Workspace path")
    parser.add_argument("--tool", type=str, required=True, help="Tool name to execute")
    parser.add_argument("--test-name", type=str, help="Test name for simulation")
    parser.add_argument("--mode", type=str, default="run", choices=["compile", "run"], help="Simulation mode")
    parser.add_argument("--verbosity", type=str, default="UVM_MEDIUM", help="UVM verbosity level")
    parser.add_argument("--waves", action="store_true", help="Generate waveforms")
    parser.add_argument("--coverage", action="store_true", help="Collect coverage")
    parser.add_argument("--timeout", type=int, default=300, help="Timeout in seconds")
    
    args = parser.parse_args()
    
    workspace_path = Path(args.workspace).resolve()
    
    server_script = workspace_path / "mcp_server" / "dsim_fastmcp_server.py"

    env = {
        "DSIM_HOME": "C:\\Users\\Nautilus\\AppData\\Local\\metrics-ca\\dsim\\20240422.0.0",
        "DSIM_ROOT": "C:\\Users\\Nautilus\\AppData\\Local\\metrics-ca\\dsim\\20240422.0.0", 
        "DSIM_LIB_PATH": "C:\\Users\\Nautilus\\AppData\\Local\\metrics-ca\\dsim\\20240422.0.0\\lib",
        "DSIM_LICENSE": "C:\\Users\\Nautilus\\AppData\\Local\\metrics-ca\\dsim-license.json"
    }
    
    # Update with current environment
    import os
    env.update(os.environ)
    
    server_parameters = StdioServerParameters(
        command=sys.executable,
        args=[str(server_script), "--workspace", str(workspace_path)],
        env=env,
        cwd=str(workspace_path / "mcp_server"),
        encoding="utf-8",
        encoding_error_handler="replace"
    )

    try:
        async with stdio_client(server_parameters) as (read_stream, write_stream):
            async with ClientSession(read_stream, write_stream) as session:
                await session.initialize()

                tools_result = await session.list_tools()
                available_tools = [tool.name for tool in tools_result.tools]
                logger.info(f"Available tools: {available_tools}")

                if args.tool not in available_tools:
                    logger.error(f"Tool '{args.tool}' not available. Available tools: {available_tools}")
                    sys.exit(1)

                # Prepare arguments based on tool
                tool_args: dict[str, object]
                if args.tool == "run_uvm_simulation":
                    tool_args = {
                        "test_name": args.test_name or "uart_axi4_basic_test",
                        "mode": args.mode,
                        "verbosity": args.verbosity,
                        "waves": args.waves,
                        "coverage": args.coverage,
                        "timeout": args.timeout
                    }
                elif args.tool == "compile_design" or args.tool == "compile_design_only":
                    tool_args = {
                        "test_name": args.test_name or "uart_axi4_basic_test",
                        "verbosity": args.verbosity,
                        "timeout": args.timeout
                    }
                elif args.tool == "run_simulation":
                    tool_args = {
                        "test_name": args.test_name or "uart_axi4_basic_test",
                        "verbosity": args.verbosity,
                        "timeout": args.timeout
                    }
                else:
                    tool_args = {}

                result = await session.call_tool(args.tool, tool_args)

                print("\n" + "=" * 50)
                print(f"MCP Tool Result: {args.tool}")
                print("=" * 50)

                if result.content:
                    for content in result.content:
                        if isinstance(content, TextContent):
                            response_text = content.text
                            try:
                                parsed = json.loads(response_text)
                                print(json.dumps(parsed, indent=2))
                            except json.JSONDecodeError:
                                print(response_text)
                        else:
                            print(str(content))
                else:
                    print("No content returned")

    except Exception as e:
        logger.error(f"MCP communication error: {e}", exc_info=True)
        # Fallback to direct FastMCP execution
        print(f"\n{'-'*50}")
        print("MCP Client failed, using direct FastMCP execution:")
        print(f"{'-'*50}")
            
        # Execute existing scripts directly instead of FastMCP server
        if args.tool == "check_dsim_environment":
            try:
                direct_result = subprocess.run(
                    [sys.executable, str(workspace_path / "mcp_server" / "check_dsim_env.py")],
                    capture_output=True,
                    text=True,
                    env=env,
                    timeout=args.timeout
                )

                if direct_result.returncode == 0:
                    print("✅ Direct script execution successful:")
                    print("Environment Check Result:")
                    print(direct_result.stdout)
                else:
                    print("❌ Direct script execution failed:")
                    print(direct_result.stderr)
                    sys.exit(1)
            except Exception as direct_error:
                print(f"❌ Direct execution error: {direct_error}")
                sys.exit(1)

        elif args.tool == "compile_design":
            try:
                test_name = getattr(args, "test_name", None) or "uart_axi4_basic_test"
                verbosity = getattr(args, "verbosity", "UVM_LOW")
                timeout = getattr(args, "timeout", 120)

                direct_result = subprocess.run(
                    [
                        sys.executable,
                        str(workspace_path / "mcp_server" / "run_uvm_simulation.py"),
                        "--test_name",
                        test_name,
                        "--mode",
                        "compile",
                        "--verbosity",
                        verbosity,
                        "--timeout",
                        str(timeout),
                    ],
                    capture_output=True,
                    text=True,
                    env=env,
                    timeout=timeout,
                )

                if direct_result.returncode == 0:
                    print("✅ Direct compile execution successful:")
                    print("Compile Result:")
                    print(direct_result.stdout)
                else:
                    print("❌ Direct compile execution failed:")
                    print(direct_result.stderr)
                    sys.exit(1)
            except Exception as direct_error:
                print(f"❌ Direct compile execution error: {direct_error}")
                sys.exit(1)

        elif args.tool == "list_available_tests":
            try:
                direct_result = subprocess.run(
                    [sys.executable, str(workspace_path / "mcp_server" / "list_available_tests.py")],
                    capture_output=True,
                    text=True,
                    env=env,
                    timeout=args.timeout,
                )

                if direct_result.returncode == 0:
                    print("✅ Direct test list execution successful:")
                    print("Available Tests:")
                    print(direct_result.stdout)
                else:
                    print("❌ Direct test list execution failed:")
                    print(direct_result.stderr)
                    sys.exit(1)
            except Exception as direct_error:
                print(f"❌ Direct test list execution error: {direct_error}")
                sys.exit(1)

        else:
            print(f"❌ Tool '{args.tool}' fallback not implemented")
            print("Available fallback tools: check_dsim_environment, compile_design, list_available_tests")
            sys.exit(1)

    except KeyboardInterrupt:
        logger.info("Interrupted by user")

if __name__ == "__main__":
    asyncio.run(main())