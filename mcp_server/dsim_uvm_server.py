#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
DSIM UVM Simulation MCP Server - FastMCP Edition
Model Context Protocol server for executing DSIM SystemVerilog UVM simulations

Created: October 13, 2025 (FastMCP Migration)
Purpose: Enable MCP clients to execute DSIM simulations with enhanced debugging
Architecture: FastMCP → Agent AI → DSIM Tools (92% → 98% Best Practice Compliance)
"""

import asyncio
import logging
import os
import subprocess
import sys
from pathlib import Path
from typing import List, Optional, Literal
import argparse
from datetime import datetime
import re

if sys.platform == "win32":
    asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())

# Configure stdout/stderr encoding for Windows compatibility  
if sys.platform == "win32":
    import io
    sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
    sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding='utf-8')

# FastMCP imports (Latest Best Practice)
try:
    from mcp.server.fastmcp import FastMCP
except ImportError as e:
    print(f"Error: FastMCP not found. Install with: pip install mcp", file=sys.stderr)
    sys.exit(1)

# Configure enhanced logging with detailed formatting
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler(sys.stderr),  # MCP best practice: use stderr for logging
    ]
)
logger = logging.getLogger("dsim-fastmcp-server")

# ASCII-safe status symbols for Windows compatibility
STATUS_OK = "[OK]"
STATUS_FAIL = "[FAIL]" 
STATUS_WARN = "[WARN]"
STATUS_INFO = "[INFO]"

# Initialize FastMCP server (Official Best Practice Pattern)
mcp = FastMCP("dsim-uvm-server")

# Global configuration
workspace_root: Optional[Path] = None
dsim_home: Optional[str] = None
MAX_LOG_FILES = 50  # keep the most recent DSIM log files to control disk usage

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

class DSIMError(Exception):
    """Enhanced DSIM-specific error with diagnostic information."""
    def __init__(self, message: str, error_type: str = "general", 
                 suggestion: str = "", exit_code: Optional[int] = None):
        self.message = message
        self.error_type = error_type
        self.suggestion = suggestion
        self.exit_code = exit_code
        super().__init__(self.message)


def cleanup_old_logs(log_dir: Path, max_logs: int = MAX_LOG_FILES) -> None:
    """Remove older DSIM log files while keeping the newest max_logs entries."""
    if max_logs <= 0 or not log_dir.exists():
        return

    try:
        log_files = sorted(
            (p for p in log_dir.glob("*.log") if p.is_file()),
            key=lambda file_path: file_path.stat().st_mtime,
            reverse=True,
        )
    except OSError as exc:
        logger.warning("Failed to examine DSIM log directory: %s", exc)
        return

    for old_file in log_files[max_logs:]:
        try:
            old_file.unlink()
            logger.info("Removed old DSIM log: %s", old_file.name)
        except OSError as exc:
            logger.warning("Unable to delete DSIM log %s: %s", old_file.name, exc)

def parse_dsim_error(stderr_output: str, exit_code: int) -> DSIMError:
    """Parse DSIM error output and provide specific diagnostics."""
    
    if "No such file or directory" in stderr_output:
        return DSIMError(
            "DSIM executable not found",
            "environment",
            "Check DSIM_HOME environment variable and ensure DSIM is properly installed",
            exit_code
        )
    elif "License" in stderr_output or "license" in stderr_output:
        return DSIMError(
            "DSIM license issue detected",
            "license", 
            "Verify DSIM_LICENSE environment variable points to valid license file",
            exit_code
        )
    elif "UVM_ERROR" in stderr_output:
        uvm_errors = re.findall(r'UVM_ERROR[^\n]*', stderr_output)
        return DSIMError(
            f"UVM simulation errors detected: {len(uvm_errors)} errors",
            "simulation",
            "Check testbench logic and UVM configuration. Review simulation logs for details",
            exit_code
        )
    elif "Compilation failed" in stderr_output or "compile error" in stderr_output:
        return DSIMError(
            "SystemVerilog compilation failed", 
            "compilation",
            "Check RTL syntax and file paths in dsim_config.f",
            exit_code
        )
    elif "timeout" in stderr_output.lower():
        return DSIMError(
            "Simulation timeout occurred",
            "timeout",
            "Increase timeout value or check for infinite loops in testbench",
            exit_code
        )
    else:
        return DSIMError(
            f"DSIM execution failed with exit code {exit_code}",
            "unknown",
            "Check DSIM logs for detailed error information",
            exit_code
        )

def _run_subprocess_sync(cmd: List[str], timeout: int, cwd: Path) -> subprocess.CompletedProcess[bytes]:
    """Run subprocess synchronously to support Windows event loop limitations."""
    return subprocess.run(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        cwd=cwd,
        timeout=timeout,
        check=False
    )


async def execute_dsim_command(cmd: List[str], timeout: int = 300) -> str:
    """Execute DSIM command with enhanced error handling and diagnostics."""
    
    logger.info(f"Executing DSIM: {' '.join(cmd)}")
    
    if workspace_root is None:
        raise DSIMError(
            "Workspace root not configured",
            "configuration",
            "Call setup_workspace before invoking DSIM commands",
        )

    try:
        loop = asyncio.get_running_loop()
        logger.debug(f"Current asyncio loop: {type(loop)}")
        # Execute with timeout and capture output
        # Change working directory to sim/uvm for correct relative path resolution
        uvm_work_dir = workspace_root / "sim" / "uvm"

        if sys.platform == "win32":
            completed = await asyncio.to_thread(
                _run_subprocess_sync,
                cmd,
                timeout,
                uvm_work_dir
            )
            stdout: bytes = completed.stdout
            stderr: bytes = completed.stderr
            return_code = completed.returncode
        else:
            process = await asyncio.create_subprocess_exec(
                *cmd,
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE,
                cwd=uvm_work_dir
            )
            stdout, stderr = await asyncio.wait_for(
                process.communicate(), 
                timeout=timeout
            )
            return_code = process.returncode
        
        stdout_text = stdout.decode('utf-8', errors='replace')
        stderr_text = stderr.decode('utf-8', errors='replace')
        
        if return_code != 0:
            # Parse and enhance error information
            dsim_error = parse_dsim_error(stderr_text, return_code)
            error_msg = f"""
{STATUS_FAIL} DSIM Execution Failed

Error Type: {dsim_error.error_type.upper()}
Exit Code: {dsim_error.exit_code}
Message: {dsim_error.message}

Suggestion: {dsim_error.suggestion}

Command: {' '.join(cmd)}
Working Directory: {uvm_work_dir}

STDERR Output:
{stderr_text}

STDOUT Output: 
{stdout_text}
            """.strip()
            
            raise DSIMError(error_msg, dsim_error.error_type, dsim_error.suggestion, dsim_error.exit_code)
        
        # Success case with detailed output
        result = f"""
{STATUS_OK} DSIM Execution Successful

Command: {' '.join(cmd)}
Exit Code: 0
Working Directory: {uvm_work_dir}

Output:
{stdout_text}

{f'Warnings/Info: {stderr_text}' if stderr_text.strip() else 'No warnings or additional info'}
        """.strip()
        
        logger.info("DSIM command completed successfully")
        return result
        
    except DSIMError:
        raise
    except subprocess.TimeoutExpired:
        raise DSIMError(
            f"DSIM command timed out after {timeout} seconds",
            "timeout", 
            f"Increase timeout value (current: {timeout}s) or optimize testbench for faster execution"
        )
    except asyncio.TimeoutError:
        raise DSIMError(
            f"DSIM command timed out after {timeout} seconds",
            "timeout", 
            f"Increase timeout value (current: {timeout}s) or optimize testbench for faster execution"
        )
    except FileNotFoundError as e:
        raise DSIMError(
            f"DSIM executable not found: {str(e)}",
            "environment",
            "Verify DSIM_HOME environment variable and PATH configuration"
        )
    except Exception as e:
        logger.exception("Unexpected error during DSIM execution")
        raise DSIMError(
            f"Unexpected error during DSIM execution: {type(e).__name__}: {str(e)}",
            "system",
            "Check system resources and DSIM installation integrity"
        )

# FastMCP Tool Definitions with Enhanced Type Safety and Documentation

@mcp.tool()
async def run_uvm_simulation(
    test_name: str = "uart_axi4_basic_test",
    mode: Literal["run", "compile", "elaborate"] = "run", 
    verbosity: Literal["UVM_NONE", "UVM_LOW", "UVM_MEDIUM", "UVM_HIGH", "UVM_FULL", "UVM_DEBUG"] = "UVM_MEDIUM",
    waves: bool = False,
    coverage: bool = True,
    seed: int = 1,
    timeout: int = 300
) -> str:
    """Execute DSIM UVM simulation with comprehensive options and enhanced error diagnostics.
    
    Args:
        test_name: UVM test class name to execute (default: uart_axi4_basic_test)
        mode: Simulation mode - run (full sim), compile (syntax check), elaborate (build only)
        verbosity: UVM verbosity level for detailed debugging output
        waves: Enable waveform capture (MXD format) for signal analysis
        coverage: Enable coverage collection for verification metrics  
        seed: Random simulation seed for reproducible results
        timeout: Maximum execution time in seconds before timeout
        
    Returns:
        Detailed simulation results with enhanced error diagnostics
        
    Raises:
        DSIMError: Enhanced DSIM-specific errors with actionable suggestions
    """
    
    # Environment validation
    if not setup_dsim_environment():
        raise DSIMError(
            "DSIM environment not properly configured",
            "environment", 
            "Set DSIM_HOME environment variable to DSIM installation directory"
        )
    if workspace_root is None:
        raise DSIMError(
            "Workspace root not configured",
            "configuration",
            "Call setup_workspace before invoking DSIM tools",
        )
    if dsim_home is None:
        raise DSIMError(
            "DSIM_HOME not set",
            "environment",
            "Set DSIM_HOME environment variable to point at the DSIM install directory",
        )
    
    # Build DSIM command with validation
    dsim_exe = Path(dsim_home) / "bin" / "dsim.exe"
    if not dsim_exe.exists():
        raise DSIMError(
            f"DSIM executable not found at {dsim_exe}",
            "environment",
            f"Verify DSIM installation in {dsim_home}"
        )
        
    uvm_dir = workspace_root / "sim" / "uvm"
    config_file = uvm_dir / "dsim_config.f"
    
    if not config_file.exists():
        raise DSIMError(
            f"DSIM configuration file not found: {config_file}",
            "configuration",
            "Ensure dsim_config.f exists in sim/uvm directory"
        )
    
    # Create timestamped log directory and prune older entries to limit clutter
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_dir = workspace_root / "sim" / "exec" / "logs"  
    log_dir.mkdir(parents=True, exist_ok=True)
    cleanup_old_logs(log_dir)
    
    # Use correct relative path from sim/uvm working directory
    # sim/uvm -> ../exec/logs (one level up to sim, then exec/logs)
    log_file_relative = f"../exec/logs/{test_name}_{timestamp}.log"
    
    # Build command with enhanced options
    # Use relative config file path since we're executing from sim/uvm directory
    cmd = [
        str(dsim_exe),
        "-f", "dsim_config.f",
        f"+UVM_TESTNAME={test_name}",
        f"+UVM_VERBOSITY={verbosity}",
        "-sv_seed", str(seed),
        "-l", log_file_relative
    ]
    
    # Mode-specific options
    if mode == "compile":
        cmd.extend(["-genimage", "compiled_image"])
    elif mode == "elaborate": 
        cmd.extend(["-elaborate"])
    else:  # run mode
        cmd.extend(["-image", "compiled_image"])
    
    # Enhanced feature options
    waves_file: Optional[Path] = None
    if waves:
        waves_dir = workspace_root / "archive" / "waveforms"
        waves_dir.mkdir(parents=True, exist_ok=True)
        waves_file = waves_dir / f"{test_name}_{timestamp}.mxd"
        cmd.extend(["-waves", str(waves_file)])
        
    if coverage:
        cmd.extend(["+cover+fsm+line+cond+tgl+branch"])
    
    # Execute with enhanced error handling
    try:
        result = await execute_dsim_command(cmd, timeout)
        
        # Add success summary with file locations
        success_summary = f"""
{STATUS_OK} UVM Simulation Completed Successfully

Test: {test_name}
Mode: {mode} 
Verbosity: {verbosity}
Log File: {log_file_relative}
{f'Waveform: {waves_file}' if waves_file else 'Waveforms: Disabled'}
Coverage: {'Enabled' if coverage else 'Disabled'}
Seed: {seed}

{result}
        """.strip()
        
        return success_summary
        
    except DSIMError as e:
        # Re-raise with additional context
        enhanced_error = f"""
{STATUS_FAIL} UVM Simulation Failed

Test Configuration:
- Test Name: {test_name}
- Mode: {mode}
- Verbosity: {verbosity}  
- Seed: {seed}
- Timeout: {timeout}s

{str(e)}

Log File: {log_file_relative} (may contain additional details)
        """.strip()
        
        raise DSIMError(enhanced_error, e.error_type, e.suggestion, e.exit_code)

@mcp.tool()
async def check_dsim_environment() -> str:
    """Verify DSIM environment setup and configuration with detailed diagnostics.
    
    Returns:
        Comprehensive environment status report with specific recommendations
    """
    
    report = [f"{STATUS_INFO} DSIM Environment Diagnostic Report"]
    report.append("=" * 50)
    
    # Check DSIM_HOME
    dsim_home_val = os.environ.get('DSIM_HOME')
    if dsim_home_val:
        dsim_path = Path(dsim_home_val)
        if dsim_path.exists():
            report.append(f"{STATUS_OK} DSIM_HOME: {dsim_home_val}")
            
            # Check DSIM executable
            dsim_exe = dsim_path / "bin" / "dsim.exe"
            if dsim_exe.exists():
                report.append(f"{STATUS_OK} DSIM Executable: {dsim_exe}")
            else:
                report.append(f"{STATUS_FAIL} DSIM Executable not found: {dsim_exe}")
                report.append(f"{STATUS_WARN} Check DSIM installation integrity")
        else:
            report.append(f"{STATUS_FAIL} DSIM_HOME path does not exist: {dsim_home_val}")
            report.append(f"{STATUS_WARN} Verify DSIM installation directory")
    else:
        report.append(f"{STATUS_FAIL} DSIM_HOME not set")
        report.append(f"{STATUS_WARN} Set DSIM_HOME to DSIM installation directory")
    
    # Check DSIM_LICENSE
    dsim_license = os.environ.get('DSIM_LICENSE')
    if dsim_license:
        license_path = Path(dsim_license)
        if license_path.exists():
            report.append(f"{STATUS_OK} DSIM_LICENSE: {dsim_license}")
        else:
            report.append(f"{STATUS_FAIL} DSIM license file not found: {dsim_license}")
            report.append(f"{STATUS_WARN} Verify license file location")
    else:
        report.append(f"{STATUS_WARN} DSIM_LICENSE not set (may use default)")
    
    # Check workspace structure
    if workspace_root:
        uvm_dir = workspace_root / "sim" / "uvm"
        config_file = uvm_dir / "dsim_config.f"
        
        if config_file.exists():
            report.append(f"{STATUS_OK} DSIM Config: {config_file}")
        else:
            report.append(f"{STATUS_FAIL} DSIM Config not found: {config_file}")
            report.append(f"{STATUS_WARN} Ensure dsim_config.f exists in sim/uvm/")
            
        # Check log directory
        log_dir = workspace_root / "sim" / "exec" / "logs"
        report.append(f"{STATUS_OK} Log Directory: {log_dir} {'(exists)' if log_dir.exists() else '(will be created)'}")
    else:
        report.append(f"{STATUS_FAIL} Workspace root not configured")
    
    # Environment summary
    report.append("=" * 50)
    
    all_checks = [line for line in report if STATUS_FAIL in line]
    if not all_checks:
        report.append(f"{STATUS_OK} Environment Status: READY")
        report.append(f"{STATUS_INFO} All DSIM components properly configured")
    else:
        report.append(f"{STATUS_FAIL} Environment Status: ISSUES DETECTED")
        report.append(f"{STATUS_WARN} Fix {len(all_checks)} issues before running simulations")
    
    return "\n".join(report)

@mcp.tool()
async def list_available_tests() -> str:
    """List all available UVM test classes in the project with enhanced discovery.
    
    Returns:
        Comprehensive list of UVM tests with file locations and descriptions
    """
    
    if not workspace_root:
        return f"{STATUS_FAIL} Workspace root not configured"
    
    uvm_tests_dir = workspace_root / "sim" / "uvm" / "tests"
    
    if not uvm_tests_dir.exists():
        return f"{STATUS_FAIL} UVM tests directory not found: {uvm_tests_dir}"
    
    test_files = list(uvm_tests_dir.glob("*_test.sv"))
    
    if not test_files:
        return f"{STATUS_WARN} No UVM test files found in {uvm_tests_dir}"
    
    report = [f"{STATUS_INFO} Available UVM Tests Discovery Report"]
    report.append("=" * 60)
    report.append(f"Search Directory: {uvm_tests_dir}")
    report.append(f"Found {len(test_files)} test files")
    report.append("")
    
    for i, test_file in enumerate(sorted(test_files), 1):
        test_name = test_file.stem  # Remove .sv extension
        
        # Try to extract class name and description from file
        try:
            content = test_file.read_text(encoding='utf-8')
            
            # Look for class declaration
            class_match = re.search(r'class\s+(\w+)\s+extends', content)
            class_name = class_match.group(1) if class_match else test_name
            
            # Look for description comment
            desc_match = re.search(r'//\s*Description:\s*(.+)', content, re.IGNORECASE)
            description = desc_match.group(1).strip() if desc_match else "No description available"
            
            report.append(f"{i:2d}. {class_name}")
            report.append(f"    File: {test_file.name}")
            report.append(f"    Description: {description}")
            report.append("")
            
        except Exception as e:
            report.append(f"{i:2d}. {test_name}")
            report.append(f"    File: {test_file.name}")
            report.append(f"    Status: Could not read file ({str(e)})")
            report.append("")
    
    report.append("=" * 60)
    report.append(f"{STATUS_OK} Test Discovery Complete")
    report.append(f"{STATUS_INFO} Use test class names (not file names) with run_uvm_simulation")
    
    return "\n".join(report)

@mcp.tool()
async def compile_design(
    test_name: str = "uart_axi4_basic_test",
    verbosity: Literal["UVM_NONE", "UVM_LOW", "UVM_MEDIUM", "UVM_HIGH"] = "UVM_LOW", 
    timeout: int = 120
) -> str:
    """Compile SystemVerilog design and testbench only (no simulation execution).
    
    Fast syntax and elaboration checking for development workflow.
    
    Args:
        test_name: Test name for compilation target
        verbosity: UVM verbosity level (lower for faster compilation)
        timeout: Compilation timeout in seconds
        
    Returns:
        Compilation results with enhanced error diagnostics
    """
    
    return await run_uvm_simulation(
        test_name=test_name,
        mode="compile",
        verbosity=verbosity,
        waves=False,
        coverage=False,
        seed=1,
        timeout=timeout
    )

@mcp.tool()
async def run_simulation(
    test_name: str = "uart_axi4_basic_test",
    verbosity: Literal["UVM_NONE", "UVM_LOW", "UVM_MEDIUM", "UVM_HIGH", "UVM_FULL", "UVM_DEBUG"] = "UVM_MEDIUM",
    seed: int = 1,
    timeout: int = 300
) -> str:
    """Execute simulation using pre-compiled design for faster iteration.
    
    Args:
        test_name: Test name to execute
        verbosity: UVM verbosity level for debugging detail
        seed: Random seed for reproducible results
        timeout: Simulation timeout in seconds
        
    Returns:
        Simulation results with enhanced diagnostics
    """
    
    return await run_uvm_simulation(
        test_name=test_name,
        mode="run", 
        verbosity=verbosity,
        waves=False,
        coverage=True,
        seed=seed,
        timeout=timeout
    )

@mcp.tool()
async def generate_waveforms(
    test_name: str = "uart_axi4_basic_test",
    format: Literal["mxd", "vcd", "both"] = "mxd",
    depth: Literal["all", "top_level", "selected"] = "all",
    timeout: int = 300
) -> str:
    """Generate waveform files during simulation for debugging and analysis.
    
    Args:
        test_name: Test name for waveform generation
        format: Waveform format (mxd recommended for DSIM)
        depth: Signal depth for waveform capture
        timeout: Simulation timeout in seconds
        
    Returns:
        Waveform generation results with file locations
    """
    
    result = await run_uvm_simulation(
        test_name=test_name,
        mode="run",
        verbosity="UVM_MEDIUM", 
        waves=True,
        coverage=True,
        seed=1,
        timeout=timeout
    )
    
    # Add waveform-specific information
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    if workspace_root is None:
        raise DSIMError(
            "Workspace root not configured",
            "configuration",
            "Call setup_workspace before invoking DSIM tools",
        )
    current_workspace = workspace_root
    waves_dir = current_workspace / "archive" / "waveforms"
    expected_file = waves_dir / f"{test_name}_{timestamp}.mxd"
    
    waveform_info = f"""

{STATUS_INFO} Waveform Generation Summary:
- Format: {format.upper()}
- Depth: {depth}
- Expected Location: {expected_file}
- Viewer: Use DSIM waveform viewer or compatible MXD viewer

{result}
    """.strip()
    
    return waveform_info

def setup_workspace(workspace_path: str):
    """Setup workspace configuration with validation."""
    global workspace_root
    
    workspace_root = Path(workspace_path)
    if not workspace_root.exists():
        raise DSIMError(
            f"Workspace directory does not exist: {workspace_path}",
            "configuration",
            "Ensure the workspace path is correct and accessible"
        )
        
    logger.info(f"Workspace configured: {workspace_root}")

def main():
    """Enhanced main function with better argument handling and diagnostics."""
    
    parser = argparse.ArgumentParser(
        description="DSIM UVM MCP Server - FastMCP Edition",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s --workspace /path/to/project
  %(prog)s --workspace /path/to/project --debug
        """
    )
    
    parser.add_argument(
        "--workspace", 
        required=True,
        help="Workspace root directory containing the UVM project"
    )
    parser.add_argument(
        "--debug",
        action="store_true", 
        help="Enable debug logging for detailed diagnostics"
    )
    parser.add_argument(
        "--test-tools",
        action="store_true",
        help="Test MCP server tools and exit"
    )
    
    args = parser.parse_args()
    
    # Configure debug logging
    if args.debug:
        logging.getLogger().setLevel(logging.DEBUG)
        logger.debug("Debug logging enabled")
    
    try:
        # Setup workspace
        setup_workspace(args.workspace)
        
        # Setup DSIM environment
        if not setup_dsim_environment():
            logger.warning("DSIM environment setup incomplete - some tools may not work")
        
        if args.test_tools:
            # Test mode - validate tools and exit
            logger.info("Testing MCP server tools...")
            
            # Test environment check
            env_result = asyncio.run(check_dsim_environment())
            print("Environment Check Result:")
            print(env_result)
            print("\nMCP Server tools test completed")
            return
        
        # Start MCP server
        logger.info(f"Starting DSIM UVM FastMCP server for workspace: {workspace_root}")
        logger.info("Enhanced with detailed error diagnostics and debugging support")
        
        # Run FastMCP server with stdio transport
        mcp.run(transport='stdio')
        
    except Exception as e:
        logger.error(f"Failed to start MCP server: {str(e)}")
        sys.exit(1)

if __name__ == "__main__":
    main()