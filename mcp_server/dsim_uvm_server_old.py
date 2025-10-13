#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
DSIM UVM Simulation MCP Server
Model Context Protocol server for executing DSIM SystemVerilog UVM simulations

Created: October 13, 2025
Purpose: Enable MCP clients to execute DSIM simulations directly
"""

import asyncio
import json
import logging
import os
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Union
import argparse
from datetime import datetime

# MCP imports
try:
    from mcp.server import Server
    from mcp.server.models import InitializationOptions
    from mcp.server.stdio import stdio_server
    from mcp.types import (
        CallToolRequest,
        CallToolResult,
        ListToolsRequest,
        ListToolsResult,
        TextContent,
        Tool,
    )
except ImportError as e:
    print(f"Error: MCP package not found. Install with: pip install mcp", file=sys.stderr)
    sys.exit(1)

# Configure logging with UTF-8 output for Windows compatibility
import locale
import io

# Set stdout encoding to UTF-8 for Windows compatibility
if sys.platform == "win32":
    sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
    sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding='utf-8')

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("dsim-mcp-server")

# ASCII-safe status symbols for Windows compatibility
STATUS_OK = "[OK]"
STATUS_FAIL = "[FAIL]"
STATUS_WARN = "[WARN]"
STATUS_INFO = "[INFO]"

class DSIMSimulationServer:
    """MCP Server for DSIM UVM Simulation execution"""
    
    def __init__(self, workspace_root: str):
        self.workspace_root = Path(workspace_root)
        self.dsim_home = os.environ.get('DSIM_HOME')
        self.server = Server("dsim-uvm-server")
        self._setup_tools()
        
        if not self.dsim_home:
            logger.warning("DSIM_HOME not set in environment")
            
    def _setup_tools(self):
        """Register MCP tools for DSIM simulation"""
        
        @self.server.list_tools()
        async def handle_list_tools() -> ListToolsResult:
            """List available DSIM simulation tools"""
            return ListToolsResult(
                tools=[
                    Tool(
                        name="run_uvm_simulation",
                        description="Execute DSIM UVM simulation with comprehensive options",
                        inputSchema={
                            "type": "object",
                            "properties": {
                                "test_name": {
                                    "type": "string",
                                    "description": "UVM test class name to execute",
                                    "default": "uart_axi4_basic_test"
                                },
                                "mode": {
                                    "type": "string",
                                    "enum": ["run", "compile", "elaborate"],
                                    "description": "Simulation mode",
                                    "default": "run"
                                },
                                "verbosity": {
                                    "type": "string",
                                    "enum": ["UVM_NONE", "UVM_LOW", "UVM_MEDIUM", "UVM_HIGH", "UVM_FULL", "UVM_DEBUG"],
                                    "description": "UVM verbosity level",
                                    "default": "UVM_MEDIUM"
                                },
                                "waves": {
                                    "type": "boolean",
                                    "description": "Enable waveform capture",
                                    "default": False
                                },
                                "coverage": {
                                    "type": "boolean",
                                    "description": "Enable coverage collection",
                                    "default": True
                                },
                                "seed": {
                                    "type": "integer",
                                    "description": "Random simulation seed",
                                    "default": 1
                                },
                                "timeout": {
                                    "type": "integer",
                                    "description": "Simulation timeout in seconds",
                                    "default": 300
                                }
                            },
                            "required": []
                        }
                    ),
                    Tool(
                        name="check_dsim_environment",
                        description="Verify DSIM environment setup and configuration",
                        inputSchema={
                            "type": "object",
                            "properties": {}
                        }
                    ),
                    Tool(
                        name="list_available_tests",
                        description="List all available UVM test classes in the project",
                        inputSchema={
                            "type": "object", 
                            "properties": {}
                        }
                    ),
                    Tool(
                        name="get_simulation_logs",
                        description="Retrieve simulation logs and results",
                        inputSchema={
                            "type": "object",
                            "properties": {
                                "log_type": {
                                    "type": "string",
                                    "enum": ["latest", "by_test", "all", "errors_only"],
                                    "description": "Type of logs to retrieve",
                                    "default": "latest"
                                },
                                "test_name": {
                                    "type": "string",
                                    "description": "Specific test name for log filtering"
                                }
                            }
                        }
                    ),
                    Tool(
                        name="generate_coverage_report",
                        description="Generate and retrieve coverage analysis report",
                        inputSchema={
                            "type": "object",
                            "properties": {
                                "format": {
                                    "type": "string",
                                    "enum": ["html", "text", "xml"],
                                    "description": "Coverage report format",
                                    "default": "html"
                                }
                            }
                        }
                    )
                ]
            )
            
        @self.server.call_tool()
        async def handle_call_tool(name: str, arguments: Dict[str, Any]) -> CallToolResult:
            """Handle tool execution requests"""
            
            try:
                if name == "run_uvm_simulation":
                    return await self._run_uvm_simulation(arguments)
                elif name == "check_dsim_environment":
                    return await self._check_dsim_environment()
                elif name == "list_available_tests":
                    return await self._list_available_tests()
                elif name == "get_simulation_logs":
                    return await self._get_simulation_logs(arguments)
                elif name == "generate_coverage_report":
                    return await self._generate_coverage_report(arguments)
                else:
                    return CallToolResult(
                        content=[TextContent(type="text", text=f"Unknown tool: {name}")]
                    )
                    
            except Exception as e:
                logger.error(f"Tool execution failed: {e}")
                return CallToolResult(
                    content=[TextContent(type="text", text=f"Error executing {name}: {str(e)}")]
                )

    async def _run_uvm_simulation(self, args: Dict[str, Any]) -> CallToolResult:
        """Execute DSIM UVM simulation"""
        
        # Extract parameters with defaults
        test_name = args.get("test_name", "uart_axi4_basic_test")
        mode = args.get("mode", "run")
        verbosity = args.get("verbosity", "UVM_MEDIUM")
        waves = args.get("waves", False)
        coverage = args.get("coverage", True)
        seed = args.get("seed", 1)
        timeout = args.get("timeout", 300)
        
        # Prepare simulation environment
        env_check = await self._check_dsim_environment()
        if "❌" in env_check.content[0].text:
            return CallToolResult(
                content=[TextContent(type="text", text=f"Environment check failed:\n{env_check.content[0].text}")]
            )
        
        # Build DSIM command
        dsim_exe = Path(self.dsim_home) / "bin" / "dsim.exe"
        uvm_dir = self.workspace_root / "sim" / "uvm"
        config_file = uvm_dir / "dsim_config.f"
        
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        log_dir = self.workspace_root / "sim" / "exec" / "logs"
        log_dir.mkdir(exist_ok=True)
        log_file = log_dir / f"{test_name}_{timestamp}.log"
        
        # Base command
        cmd = [
            str(dsim_exe),
            "-f", str(config_file),
            f"+UVM_TESTNAME={test_name}",
            f"+UVM_VERBOSITY={verbosity}",
            "-sv_seed", str(seed),
            "-l", str(log_file)
        ]
        
        # Mode-specific options
        if mode == "compile":
            cmd.extend(["-genimage", "compiled_image"])
        elif mode == "elaborate":
            cmd.extend(["-elaborate"])
        else:  # run mode
            cmd.extend(["-image", "compiled_image"])
        
        # Optional features
        if waves:
            waves_dir = self.workspace_root / "archive" / "waveforms"
            waves_dir.mkdir(exist_ok=True)
            waves_file = waves_dir / f"{test_name}_{timestamp}.mxd"
            cmd.extend(["-waves", str(waves_file)])
            
        if coverage:
            cmd.extend(["+cover+fsm+line+cond+tgl+branch"])
            
        # Execution
        logger.info(f"Executing DSIM: {' '.join(cmd)}")
        
        try:
            result = await asyncio.wait_for(
                asyncio.create_subprocess_exec(
                    *cmd,
                    cwd=str(uvm_dir),
                    stdout=asyncio.subprocess.PIPE,
                    stderr=asyncio.subprocess.STDOUT,
                    env=dict(os.environ, **self._get_dsim_env())
                ),
                timeout=timeout
            )
            
            stdout, _ = await result.communicate()
            stdout_text = stdout.decode('utf-8', errors='replace')
            
            # Analyze results
            success = result.returncode == 0
            status = "✅ SUCCESS" if success else "❌ FAILED"
            
            response_text = f"""
🚀 DSIM UVM Simulation Results
{'='*50}
📋 Configuration:
  Test: {test_name}
  Mode: {mode}
  Verbosity: {verbosity}
  Seed: {seed}
  Waves: {'Enabled' if waves else 'Disabled'}
  Coverage: {'Enabled' if coverage else 'Disabled'}

📊 Execution Status: {status}
📁 Log File: {log_file}
🔢 Exit Code: {result.returncode}

📝 Simulation Output:
{'-'*50}
{stdout_text[-2000:]}  # Last 2000 characters

💡 Next Steps:
{'- Check simulation logs for detailed analysis' if success else '- Review error messages and fix compilation/runtime issues'}
{'- Generate coverage report if needed' if success and coverage else ''}
"""
            
            return CallToolResult(
                content=[TextContent(type="text", text=response_text)]
            )
            
        except asyncio.TimeoutError:
            return CallToolResult(
                content=[TextContent(type="text", text=f"❌ Simulation timeout after {timeout} seconds")]
            )
        except Exception as e:
            return CallToolResult(
                content=[TextContent(type="text", text=f"❌ Simulation execution failed: {str(e)}")]
            )

    async def _check_dsim_environment(self) -> CallToolResult:
        """Check DSIM environment configuration"""
        
        status_lines = [f"{STATUS_INFO} DSIM Environment Status", "="*50]
        
        # Check DSIM_HOME
        if self.dsim_home and Path(self.dsim_home).exists():
            status_lines.append(f"{STATUS_OK} DSIM_HOME: {self.dsim_home}")
        else:
            status_lines.append(f"{STATUS_FAIL} DSIM_HOME: Not set or invalid ({self.dsim_home})")
            
        # Check DSIM executable
        if self.dsim_home:
            dsim_exe = Path(self.dsim_home) / "bin" / "dsim.exe"
            if dsim_exe.exists():
                status_lines.append(f"{STATUS_OK} DSIM Executable: {dsim_exe}")
            else:
                status_lines.append(f"{STATUS_FAIL} DSIM Executable: Not found at {dsim_exe}")
        
        # Check workspace structure
        uvm_dir = self.workspace_root / "sim" / "uvm"
        config_file = uvm_dir / "dsim_config.f"
        
        if uvm_dir.exists():
            status_lines.append(f"{STATUS_OK} UVM Directory: {uvm_dir}")
        else:
            status_lines.append(f"{STATUS_FAIL} UVM Directory: Not found at {uvm_dir}")
            
        if config_file.exists():
            status_lines.append(f"{STATUS_OK} Config File: {config_file}")
        else:
            status_lines.append(f"{STATUS_FAIL} Config File: Not found at {config_file}")
        
        # Check license
        license_env = os.environ.get('DSIM_LICENSE')
        if license_env:
            status_lines.append(f"{STATUS_OK} DSIM License: {license_env}")
        else:
            # Check for default license location
            default_license = Path(self.dsim_home).parent / "dsim-license.json" if self.dsim_home else None
            if default_license and default_license.exists():
                status_lines.append(f"{STATUS_OK} DSIM License: {default_license} (default)")
            else:
                status_lines.append(f"{STATUS_WARN} DSIM License: Not explicitly set (may use default)")
        
        return CallToolResult(
            content=[TextContent(type="text", text="\n".join(status_lines))]
        )
    
    async def _list_available_tests(self) -> CallToolResult:
        """List available UVM test classes"""
        
        tests_dir = self.workspace_root / "sim" / "uvm" / "tests"
        test_files = []
        
        if tests_dir.exists():
            for test_file in tests_dir.glob("*.sv"):
                # Parse test class names from files
                try:
                    with open(test_file, 'r', encoding='utf-8') as f:
                        content = f.read()
                        # Simple regex to find class definitions
                        import re
                        classes = re.findall(r'class\s+(\w+)\s+extends', content)
                        if classes:
                            test_files.append(f"📄 {test_file.name}: {', '.join(classes)}")
                except Exception:
                    test_files.append(f"📄 {test_file.name}: (could not parse)")
        
        if not test_files:
            test_files = ["❌ No test files found"]
            
        response = f"""
🧪 Available UVM Tests
{'='*50}
📁 Tests Directory: {tests_dir}

{chr(10).join(test_files)}

💡 Usage: Use test class names with run_uvm_simulation tool
"""
        
        return CallToolResult(
            content=[TextContent(type="text", text=response)]
        )

    async def _get_simulation_logs(self, args: Dict[str, Any]) -> CallToolResult:
        """Retrieve simulation logs"""
        
        log_type = args.get("log_type", "latest")
        test_name = args.get("test_name")
        
        log_dir = self.workspace_root / "sim" / "exec" / "logs"
        
        if not log_dir.exists():
            return CallToolResult(
                content=[TextContent(type="text", text="❌ No logs directory found")]
            )
        
        log_files = list(log_dir.glob("*.log"))
        log_files.sort(key=lambda x: x.stat().st_mtime, reverse=True)
        
        if not log_files:
            return CallToolResult(
                content=[TextContent(type="text", text="❌ No log files found")]
            )
        
        if log_type == "latest":
            # Return latest log
            latest_log = log_files[0]
            try:
                with open(latest_log, 'r', encoding='utf-8') as f:
                    content = f.read()
                    
                response = f"""
📋 Latest Simulation Log
{'='*50}
📁 File: {latest_log.name}
📅 Modified: {datetime.fromtimestamp(latest_log.stat().st_mtime)}

📝 Content (last 3000 characters):
{'-'*50}
{content[-3000:]}
"""
                return CallToolResult(
                    content=[TextContent(type="text", text=response)]
                )
            except Exception as e:
                return CallToolResult(
                    content=[TextContent(type="text", text=f"❌ Error reading log: {e}")]
                )
        
        elif log_type == "all":
            # List all logs
            log_list = []
            for log_file in log_files[:10]:  # Limit to 10 most recent
                size = log_file.stat().st_size
                modified = datetime.fromtimestamp(log_file.stat().st_mtime)
                log_list.append(f"📄 {log_file.name} ({size} bytes, {modified})")
            
            response = f"""
📋 All Simulation Logs
{'='*50}
📁 Directory: {log_dir}

{chr(10).join(log_list)}

💡 Use log_type='latest' to read the most recent log content
"""
            return CallToolResult(
                content=[TextContent(type="text", text=response)]
            )
        
        # Add more log_type handling as needed
        return CallToolResult(
            content=[TextContent(type="text", text=f"Log type '{log_type}' not implemented yet")]
        )

    async def _generate_coverage_report(self, args: Dict[str, Any]) -> CallToolResult:
        """Generate coverage analysis report"""
        
        format_type = args.get("format", "html")
        
        # Check for coverage database
        coverage_db = self.workspace_root / "sim" / "uvm" / "metrics.db"
        
        if not coverage_db.exists():
            return CallToolResult(
                content=[TextContent(type="text", text="❌ No coverage database found. Run simulation with coverage enabled first.")]
            )
        
        try:
            # Use dcreport to generate coverage report
            dcreport_exe = Path(self.dsim_home) / "bin" / "dcreport.exe"
            output_dir = self.workspace_root / "sim" / "exec" / "coverage_report"
            output_dir.mkdir(exist_ok=True)
            
            cmd = [
                str(dcreport_exe),
                str(coverage_db),
                "-out_dir", str(output_dir)
            ]
            
            if format_type == "text":
                cmd.extend(["-text"])
            elif format_type == "xml":
                cmd.extend(["-xml"])
            # HTML is default
            
            result = await asyncio.create_subprocess_exec(
                *cmd,
                cwd=str(self.workspace_root / "sim" / "uvm"),
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE
            )
            
            stdout, stderr = await result.communicate()
            
            if result.returncode == 0:
                response = f"""
📊 Coverage Report Generated
{'='*50}
✅ Status: Success
📁 Output Directory: {output_dir}
📋 Format: {format_type.upper()}

📈 Report Files:
{'-'*30}
"""
                # List generated files
                for report_file in output_dir.iterdir():
                    if report_file.is_file():
                        response += f"📄 {report_file.name}\n"
                
                if format_type == "html":
                    index_html = output_dir / "index.html"
                    if index_html.exists():
                        response += f"\n💡 Open coverage report: {index_html}"
                
                return CallToolResult(
                    content=[TextContent(type="text", text=response)]
                )
            else:
                error_text = stderr.decode('utf-8', errors='replace')
                return CallToolResult(
                    content=[TextContent(type="text", text=f"❌ Coverage report generation failed:\n{error_text}")]
                )
                
        except Exception as e:
            return CallToolResult(
                content=[TextContent(type="text", text=f"❌ Error generating coverage report: {str(e)}")]
            )

    def _get_dsim_env(self) -> Dict[str, str]:
        """Get DSIM environment variables"""
        env_vars = {}
        
        if self.dsim_home:
            env_vars.update({
                'DSIM_HOME': self.dsim_home,
                'DSIM_ROOT': self.dsim_home,
                'DSIM_LIB_PATH': str(Path(self.dsim_home) / "lib")
            })
            
        # Add license if set
        license_env = os.environ.get('DSIM_LICENSE')
        if license_env:
            env_vars['DSIM_LICENSE'] = license_env
            
        return env_vars

    async def run(self):
        """Start the MCP server"""
        logger.info("Starting DSIM UVM MCP Server...")
        async with stdio_server() as (read_stream, write_stream):
            await self.server.run(
                read_stream,
                write_stream,
                InitializationOptions(
                    server_name="dsim-uvm-server",
                    server_version="1.0.0",
                    capabilities=self.server.get_capabilities(
                        notification_options=None,
                        experimental_capabilities={}
                    )
                )
            )

async def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(description="DSIM UVM MCP Server")
    parser.add_argument(
        "--workspace",
        default=os.getcwd(),
        help="Workspace root directory (default: current directory)"
    )
    
    args = parser.parse_args()
    
    server = DSIMSimulationServer(args.workspace)
    await server.run()

if __name__ == "__main__":
    asyncio.run(main())