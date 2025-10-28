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
import json
from pathlib import Path
from typing import Any, Sequence, cast

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
    parser.add_argument("--mode", type=str, default="batch", choices=["compile", "run", "batch"], 
                       help="Execution mode: compile (compile only), run (run only), batch (compile+run, default)")
    parser.add_argument("--verbosity", type=str, default="UVM_MEDIUM", help="UVM verbosity level")
    parser.add_argument("--waves", dest="waves", action="store_true", help="Enable waveform generation (default)")
    parser.add_argument("--no-waves", dest="waves", action="store_false", help="Disable waveform generation")
    parser.set_defaults(waves=True)
    parser.add_argument("--wave-format", type=str, default="MXD", choices=["MXD", "VCD"],
                       help="Waveform format: MXD (binary, default) or VCD (text, portable)")
    parser.add_argument("--coverage", action="store_true", help="Collect coverage")
    parser.add_argument("--timeout", type=int, default=300, help="Timeout in seconds (for run phase in batch mode)")
    parser.add_argument("--compile-timeout", type=int, default=120, help="Compile timeout in seconds (batch mode only)")
    parser.add_argument("--plusarg", action="append", default=[], help="DSIM plus-argument (e.g. SIM_TIMEOUT_MS=60000). Repeat for multiple values")
    parser.add_argument("--path", type=str, help="File path for analysis tools")
    parser.add_argument("--test-scenario", type=str, default="", help="Name of test scenario for waveform/debug configuration")
    
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

                # Prepare arguments based on tool and mode
                tool_args: dict[str, object]
                
                # Direct batch tool invocation
                scenario_plusarg = args.test_scenario.strip()

                if args.tool == "run_uvm_simulation_batch":
                    actual_tool = "run_uvm_simulation_batch"
                    tool_args = {
                        "test_name": args.test_name or "uart_axi4_basic_test",
                        "verbosity": args.verbosity,
                        "waves": args.waves,
                        "wave_format": args.wave_format,
                        "coverage": args.coverage,
                        "compile_timeout": args.compile_timeout,
                        "run_timeout": args.timeout
                    }
                    if args.plusarg:
                        tool_args["plusargs"] = list(args.plusarg)
                    logger.info(f"Using batch tool directly: {actual_tool}")
                
                # Batch mode: use run_uvm_simulation_batch tool
                elif args.mode == "batch" and args.tool == "run_uvm_simulation":
                    actual_tool = "run_uvm_simulation_batch"
                    tool_args = {
                        "test_name": args.test_name or "uart_axi4_basic_test",
                        "verbosity": args.verbosity,
                        "waves": args.waves,
                        "wave_format": args.wave_format,
                        "coverage": args.coverage,
                        "compile_timeout": args.compile_timeout,
                        "run_timeout": args.timeout
                    }
                    if args.plusarg:
                        tool_args["plusargs"] = list(args.plusarg)
                    logger.info(f"Using batch mode: {actual_tool}")
                
                # Compile or run mode: use run_uvm_simulation with mode parameter
                elif args.tool == "run_uvm_simulation":
                    actual_tool = args.tool
                    waves_setting = args.waves
                    if args.mode == "compile":
                        waves_setting = False
                    tool_args = {
                        "test_name": args.test_name or "uart_axi4_basic_test",
                        "mode": args.mode if args.mode != "batch" else "run",
                        "verbosity": args.verbosity,
                        "waves": waves_setting,
                        "wave_format": args.wave_format,
                        "coverage": args.coverage,
                        "timeout": args.timeout
                    }
                    if args.plusarg:
                        tool_args["plusargs"] = list(args.plusarg)
                
                elif args.tool == "compile_design" or args.tool == "compile_design_only":
                    actual_tool = args.tool
                    tool_args = {
                        "test_name": args.test_name or "uart_axi4_basic_test",
                        "verbosity": args.verbosity,
                        "timeout": args.timeout
                    }
                elif args.tool == "run_simulation":
                    actual_tool = args.tool
                    tool_args = {
                        "test_name": args.test_name or "uart_axi4_basic_test",
                        "verbosity": args.verbosity,
                        "timeout": args.timeout
                    }
                else:
                    actual_tool = args.tool
                    tool_args = {}
                    if args.path:
                        tool_args["path"] = args.path

                if scenario_plusarg:
                    scenario_entry = f"TEST_SCENARIO={scenario_plusarg}"
                    plusargs_list: list[str] = []
                    if "plusargs" in tool_args:
                        existing_plusargs = tool_args["plusargs"]
                        if isinstance(existing_plusargs, list):
                            sequence_value = cast(Sequence[Any], existing_plusargs)
                            plusargs_list = [str(item) for item in sequence_value]
                        else:
                            plusargs_list = [str(existing_plusargs)]
                    plusargs_list.append(scenario_entry)
                    tool_args["plusargs"] = plusargs_list

                result = await session.call_tool(actual_tool, tool_args)

                print("\n" + "=" * 50)
                print(f"MCP Tool Result: {actual_tool}")
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

    except KeyboardInterrupt:
        logger.info("Interrupted by user")
    except Exception as exc:
        logger.error("MCP communication error: %s", exc, exc_info=True)
        print(
            "ERROR: MCP communication failed. Ensure the FastMCP server is running and reachable.",
            file=sys.stderr,
        )
        sys.exit(1)

if __name__ == "__main__":
    asyncio.run(main())