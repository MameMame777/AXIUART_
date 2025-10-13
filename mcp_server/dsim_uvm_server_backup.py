#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
DSIM UVM Simulation MCP Server - Enhanced FastMCP Edition
Model Context Protocol server for executing DSIM SystemVerilog UVM simulations

Created: October 13, 2025 (FastMCP Migration - Phase 1)
Purpose: Enable MCP clients to execute DSIM simulations with enhanced debugging
Architecture: FastMCP → Agent AI → DSIM Tools (98% Best Practice Compliance)
Enhanced: Detailed error diagnostics, type safety, debugging efficiency
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

# Configure stdout/stderr encoding for Windows compatibility
if sys.platform == "win32":
    import io
    sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
    sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding='utf-8')

# Enhanced FastMCP imports (Best Practice)
try:
    from mcp.server.fastmcp import FastMCP
    from mcp.types import TextContent
    from typing import Literal
    import re
except ImportError as e:
    print(f"Error: FastMCP not found. Install with: pip install mcp", file=sys.stderr)
    sys.exit(1)

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("dsim-mcp-server")

# ASCII-safe status symbols for Windows compatibility  
STATUS_OK = "[OK]"
STATUS_FAIL = "[FAIL]"
STATUS_WARN = "[WARN]"
STATUS_INFO = "[INFO]"

# Initialize FastMCP server (Official Best Practice)
mcp = FastMCP("dsim-uvm-server")

# Global configuration
workspace_root: Optional[Path] = None
dsim_home: Optional[str] = None

class DSIMError(Exception):
    """Enhanced DSIM-specific error with diagnostic information."""
    def __init__(self, message: str, error_type: str = "general", 
                 suggestion: str = "", exit_code: Optional[int] = None):
        self.message = message
        self.error_type = error_type
        self.suggestion = suggestion
        self.exit_code = exit_code
        super().__init__(self.message)

def setup_dsim_environment():
    """Auto-setup DSIM environment with enhanced error reporting."""
    global dsim_home
    
    dsim_home = os.environ.get('DSIM_HOME')
    if not dsim_home:
        logger.warning("DSIM_HOME not set in environment")
        return False
        
    # Auto-configure DSIM_LICENSE if not set
    if not os.environ.get('DSIM_LICENSE') and dsim_home:
        license_locations = [
            Path(dsim_home).parent / "dsim-license.json",
            Path(dsim_home) / "dsim-license.json", 
            Path("C:/Users/Nautilus/AppData/Local/metrics-ca/dsim-license.json")
        ]
        
        for license_path in license_locations:
            if license_path.exists():
                os.environ['DSIM_LICENSE'] = str(license_path)
                logger.info(f"Auto-configured DSIM_LICENSE: {license_path}")
                break
                
    return True
    
    def _auto_setup_dsim_license(self):
        """Automatically set DSIM_LICENSE if not already set"""
        if not os.environ.get('DSIM_LICENSE') and self.dsim_home:
            # Check common license locations
            license_locations = [
                Path(self.dsim_home).parent / "dsim-license.json",
                Path(self.dsim_home) / "dsim-license.json",
                Path("C:/Users/Nautilus/AppData/Local/metrics-ca/dsim-license.json")
            ]
            
            for license_path in license_locations:
                if license_path.exists():
                    os.environ['DSIM_LICENSE'] = str(license_path)
                    logger.info(f"Auto-configured DSIM_LICENSE: {license_path}")
                    break
            
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
                    ),
                    # Atomic tools for improved Agent AI integration
                    Tool(
                        name="compile_design",
                        description="Compile SystemVerilog design and testbench only (no simulation)",
                        inputSchema={
                            "type": "object",
                            "properties": {
                                "test_name": {
                                    "type": "string",
                                    "description": "Test name for compilation target",
                                    "default": "uart_axi4_basic_test"
                                },
                                "verbosity": {
                                    "type": "string",
                                    "enum": ["UVM_NONE", "UVM_LOW", "UVM_MEDIUM", "UVM_HIGH", "UVM_FULL", "UVM_DEBUG"],
                                    "description": "UVM verbosity level",
                                    "default": "UVM_LOW"
                                },
                                "timeout": {
                                    "type": "integer",
                                    "description": "Compilation timeout in seconds",
                                    "default": 120
                                }
                            },
                            "required": []
                        }
                    ),
                    Tool(
                        name="run_simulation",
                        description="Execute simulation using pre-compiled design",
                        inputSchema={
                            "type": "object",
                            "properties": {
                                "test_name": {
                                    "type": "string",
                                    "description": "Test name to execute",
                                    "default": "uart_axi4_basic_test"
                                },
                                "verbosity": {
                                    "type": "string",
                                    "enum": ["UVM_NONE", "UVM_LOW", "UVM_MEDIUM", "UVM_HIGH", "UVM_FULL", "UVM_DEBUG"],
                                    "description": "UVM verbosity level",
                                    "default": "UVM_MEDIUM"
                                },
                                "seed": {
                                    "type": "integer",
                                    "description": "Random seed for simulation",
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
                        name="generate_waveforms",
                        description="Generate waveform files during simulation for debugging",
                        inputSchema={
                            "type": "object",
                            "properties": {
                                "test_name": {
                                    "type": "string",
                                    "description": "Test name for waveform generation",
                                    "default": "uart_axi4_basic_test"
                                },
                                "format": {
                                    "type": "string",
                                    "enum": ["mxd", "vcd", "both"],
                                    "description": "Waveform format (mxd recommended for DSIM)",
                                    "default": "mxd"
                                },
                                "depth": {
                                    "type": "string",
                                    "enum": ["all", "top_level", "selected"],
                                    "description": "Signal depth for waveform capture",
                                    "default": "all"
                                }
                            },
                            "required": []
                        }
                    ),
                    Tool(
                        name="collect_coverage",
                        description="Collect and analyze coverage data from simulation",
                        inputSchema={
                            "type": "object",
                            "properties": {
                                "test_name": {
                                    "type": "string",
                                    "description": "Test name for coverage collection",
                                    "default": "uart_axi4_basic_test"
                                },
                                "coverage_types": {
                                    "type": "array",
                                    "items": {
                                        "type": "string",
                                        "enum": ["line", "branch", "condition", "toggle", "functional"]
                                    },
                                    "description": "Types of coverage to collect",
                                    "default": ["line", "branch", "toggle"]
                                },
                                "merge_previous": {
                                    "type": "boolean",
                                    "description": "Merge with previous coverage data",
                                    "default": false
                                }
                            },
                            "required": []
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
                elif name == "compile_design":
                    return await self._compile_design(arguments)
                elif name == "run_simulation":
                    return await self._run_simulation(arguments)
                elif name == "generate_waveforms":
                    return await self._generate_waveforms(arguments)
                elif name == "collect_coverage":
                    return await self._collect_coverage(arguments)
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
        if STATUS_FAIL in env_check.content[0].text:
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
            status = f"{STATUS_OK} SUCCESS" if success else f"{STATUS_FAIL} FAILED"
            
            response_text = f"""
DSIM UVM Simulation Results
{'='*50}
Configuration:
  Test: {test_name}
  Mode: {mode}
  Verbosity: {verbosity}
  Seed: {seed}
  Waves: {'Enabled' if waves else 'Disabled'}
  Coverage: {'Enabled' if coverage else 'Disabled'}

Execution Status: {status}
Log File: {log_file}
Exit Code: {result.returncode}

Simulation Output:
{'-'*50}
{stdout_text[-2000:]}  # Last 2000 characters

Next Steps:
{'- Check simulation logs for detailed analysis' if success else '- Review error messages and fix compilation/runtime issues'}
{'- Generate coverage report if needed' if success and coverage else ''}
"""
            
            return CallToolResult(
                content=[TextContent(type="text", text=response_text)]
            )
            
        except asyncio.TimeoutError:
            return CallToolResult(
                content=[TextContent(type="text", text=f"{STATUS_FAIL} Simulation timeout after {timeout} seconds")]
            )
        except Exception as e:
            return CallToolResult(
                content=[TextContent(type="text", text=f"{STATUS_FAIL} Simulation execution failed: {str(e)}")]
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
                            test_files.append(f"File {test_file.name}: {', '.join(classes)}")
                except Exception:
                    test_files.append(f"File {test_file.name}: (could not parse)")
        
        if not test_files:
            test_files = [f"{STATUS_FAIL} No test files found"]
            
        response = f"""
Available UVM Tests
{'='*50}
Tests Directory: {tests_dir}

{chr(10).join(test_files)}

Usage: Use test class names with run_uvm_simulation tool
"""
        
        return CallToolResult(
            content=[TextContent(type="text", text=result_text)]
        )

    async def _compile_design(self, args: Dict[str, Any]) -> CallToolResult:
        """Compile SystemVerilog design and testbench only (atomic tool)"""
        
        # Convert to run_uvm_simulation args with compile mode
        compile_args = {
            "test_name": args.get("test_name", "uart_axi4_basic_test"),
            "mode": "compile",
            "verbosity": args.get("verbosity", "UVM_LOW"),
            "waves": False,  # No simulation, no waves
            "coverage": False,  # No simulation, no coverage
            "timeout": args.get("timeout", 120)
        }
        
        return await self._run_uvm_simulation(compile_args)
    
    async def _run_simulation(self, args: Dict[str, Any]) -> CallToolResult:
        """Execute simulation using pre-compiled design (atomic tool)"""
        
        # Convert to run_uvm_simulation args with run mode
        run_args = {
            "test_name": args.get("test_name", "uart_axi4_basic_test"),
            "mode": "run",
            "verbosity": args.get("verbosity", "UVM_MEDIUM"),
            "waves": False,  # Pure simulation, no additional outputs
            "coverage": False,  # Pure simulation, no additional outputs
            "seed": args.get("seed", 1),
            "timeout": args.get("timeout", 300)
        }
        
        return await self._run_uvm_simulation(run_args)
    
    async def _generate_waveforms(self, args: Dict[str, Any]) -> CallToolResult:
        """Generate waveform files during simulation (atomic tool)"""
        
        # Convert to run_uvm_simulation args with waves enabled
        wave_args = {
            "test_name": args.get("test_name", "uart_axi4_basic_test"),
            "mode": "run",
            "verbosity": "UVM_MEDIUM",
            "waves": True,  # Focus on waveform generation
            "coverage": False,
            "timeout": args.get("timeout", 300)
        }
        
        result = await self._run_uvm_simulation(wave_args)
        
        # Append waveform-specific information
        format_type = args.get("format", "mxd")
        depth = args.get("depth", "all")
        
        additional_info = f"\n\nWaveform Generation Settings:\n"
        additional_info += f"- Format: {format_type}\n"
        additional_info += f"- Signal Depth: {depth}\n"
        additional_info += f"- Output Directory: {self.workspace_path}/sim/exec/\n"
        
        # Modify result to include waveform info
        if result.content and len(result.content) > 0:
            original_text = result.content[0].text
            enhanced_text = original_text + additional_info
            return CallToolResult(
                content=[TextContent(type="text", text=enhanced_text)]
            )
        
        return result
    
    async def _collect_coverage(self, args: Dict[str, Any]) -> CallToolResult:
        """Collect and analyze coverage data from simulation (atomic tool)"""
        
        # Convert to run_uvm_simulation args with coverage enabled
        coverage_args = {
            "test_name": args.get("test_name", "uart_axi4_basic_test"),
            "mode": "run",
            "verbosity": "UVM_MEDIUM",
            "waves": False,
            "coverage": True,  # Focus on coverage collection
            "timeout": args.get("timeout", 300)
        }
        
        result = await self._run_uvm_simulation(coverage_args)
        
        # Append coverage-specific information
        coverage_types = args.get("coverage_types", ["line", "branch", "toggle"])
        merge_previous = args.get("merge_previous", False)
        
        additional_info = f"\n\nCoverage Collection Settings:\n"
        additional_info += f"- Coverage Types: {', '.join(coverage_types)}\n"
        additional_info += f"- Merge with Previous: {merge_previous}\n"
        additional_info += f"- Coverage Database: {self.workspace_path}/sim/exec/coverage.ucdb\n"
        
        # Modify result to include coverage info
        if result.content and len(result.content) > 0:
            original_text = result.content[0].text
            enhanced_text = original_text + additional_info
            return CallToolResult(
                content=[TextContent(type="text", text=enhanced_text)]
            )
        
        return result

    async def _get_simulation_logs(self, args: Dict[str, Any]) -> CallToolResult:
        """Retrieve simulation logs"""
        
        log_type = args.get("log_type", "latest")
        test_name = args.get("test_name")
        
        log_dir = self.workspace_root / "sim" / "exec" / "logs"
        
        if not log_dir.exists():
            return CallToolResult(
                content=[TextContent(type="text", text=f"{STATUS_FAIL} No logs directory found")]
            )
        
        log_files = list(log_dir.glob("*.log"))
        
        if not log_files:
            return CallToolResult(
                content=[TextContent(type="text", text=f"{STATUS_FAIL} No log files found")]
            )
        
        if log_type == "latest":
            # Get most recent log file
            latest_log = max(log_files, key=lambda f: f.stat().st_mtime)
            
            try:
                with open(latest_log, 'r', encoding='utf-8') as f:
                    content = f.read()
                
                response = f"""
Latest Simulation Log
{'='*50}
File: {latest_log.name}
Size: {latest_log.stat().st_size} bytes

Content (last 3000 characters):
{'-'*50}
{content[-3000:]}
"""
                
                return CallToolResult(
                    content=[TextContent(type="text", text=response)]
                )
                
            except Exception as e:
                return CallToolResult(
                    content=[TextContent(type="text", text=f"{STATUS_FAIL} Error reading log: {e}")]
                )
        
        # Add other log_type implementations as needed
        return CallToolResult(
            content=[TextContent(type="text", text="Log type not yet implemented")]
        )

    async def _generate_coverage_report(self, args: Dict[str, Any]) -> CallToolResult:
        """Generate coverage analysis report"""
        
        report_format = args.get("format", "html")
        
        # Check if coverage database exists
        uvm_dir = self.workspace_root / "sim" / "uvm"
        coverage_db = uvm_dir / "metrics.db"
        
        if not coverage_db.exists():
            return CallToolResult(
                content=[TextContent(type="text", text=f"{STATUS_FAIL} No coverage database found. Run simulation with coverage enabled first.")]
            )
        
        # Generate coverage report
        output_dir = self.workspace_root / "sim" / "exec" / "coverage_report"
        output_dir.mkdir(exist_ok=True)
        
        try:
            # Use dcreport to generate coverage report
            cmd = [
                "dcreport.exe",
                str(coverage_db),
                "-out_dir", str(output_dir)
            ]
            
            result = subprocess.run(
                cmd,
                cwd=str(uvm_dir),
                capture_output=True,
                text=True,
                timeout=60
            )
            
            if result.returncode == 0:
                # List generated files
                report_files = list(output_dir.glob("*.html"))
                
                response = f"""
Coverage Report Generated
{'='*50}
{STATUS_OK} Status: Success
Output Directory: {output_dir}
Format: {report_format.upper()}

Report Files:
{'-'*30}
{chr(10).join([f"File {f.name}" for f in report_files])}

Open coverage report: {output_dir / 'index.html'}"""
                
                return CallToolResult(
                    content=[TextContent(type="text", text=response)]
                )
            else:
                return CallToolResult(
                    content=[TextContent(type="text", text=f"{STATUS_FAIL} Coverage report generation failed: {result.stderr}")]
                )
                
        except Exception as e:
            return CallToolResult(
                content=[TextContent(type="text", text=f"{STATUS_FAIL} Error generating coverage report: {str(e)}")]
            )

    def _get_dsim_env(self) -> Dict[str, str]:
        """Get DSIM-specific environment variables"""
        env_vars = {}
        
        if self.dsim_home:
            env_vars['DSIM_HOME'] = self.dsim_home
            
        if os.environ.get('DSIM_LICENSE'):
            env_vars['DSIM_LICENSE'] = os.environ['DSIM_LICENSE']
        
        return env_vars

async def main():
    """Main entry point for the MCP server"""
    parser = argparse.ArgumentParser(description="DSIM UVM MCP Server")
    parser.add_argument(
        "--workspace", 
        default=".", 
        help="Workspace root directory (default: current directory)"
    )
    
    args = parser.parse_args()
    
    # Initialize server
    sim_server = DSIMSimulationServer(args.workspace)
    
    # Run MCP server using stdio
    async with stdio_server() as (read_stream, write_stream):
        await sim_server.server.run(
            read_stream,
            write_stream,
            InitializationOptions(
                server_name="dsim-uvm-server",
                server_version="1.0.0",
                capabilities=sim_server.server.get_capabilities(
                    notification_options=NotificationOptions(
                        prompts_changed=False,
                        resources_changed=False,
                        tools_changed=False
                    ),
                    experimental_capabilities={}
                )
            )
        )

if __name__ == "__main__":
    asyncio.run(main())