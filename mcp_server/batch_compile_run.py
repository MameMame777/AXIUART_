#!/usr/bin/env python3
"""
Batch Compile-and-Run Script for DSIM UVM Tests
Executes compile phase followed immediately by run phase
Author: AI Agent
Date: 2025-10-18
"""

import sys
import argparse
import subprocess
import time
from pathlib import Path

def run_mcp_tool(workspace, tool, test_name, mode, verbosity="UVM_MEDIUM", waves=True, coverage=False, timeout=300):
    """Execute MCP client with specified parameters"""
    cmd = [
        sys.executable,
        str(workspace / "mcp_server" / "mcp_client.py"),
        "--workspace", str(workspace),
        "--tool", tool,
        "--test-name", test_name,
        "--mode", mode,
        "--verbosity", verbosity,
        "--timeout", str(timeout)
    ]
    
    if waves:
        cmd.append("--waves")
    else:
        cmd.append("--no-waves")
    if coverage:
        cmd.append("--coverage")
    
    print(f"\n{'='*60}")
    print(f"Executing: {' '.join(cmd)}")
    print(f"{'='*60}\n")
    
    result = subprocess.run(cmd, capture_output=False, text=True)
    return result.returncode

def main():
    parser = argparse.ArgumentParser(description="Batch compile-and-run for DSIM UVM tests")
    parser.add_argument("--test-name", required=True, help="UVM test name to execute")
    parser.add_argument("--verbosity", default="UVM_MEDIUM", help="UVM verbosity level (default: UVM_MEDIUM)")
    parser.add_argument("--waves", dest="waves", action="store_true", help="Enable waveform generation (default)")
    parser.add_argument("--no-waves", dest="waves", action="store_false", help="Disable waveform generation")
    parser.set_defaults(waves=True)
    parser.add_argument("--coverage", action="store_true", help="Enable coverage collection")
    parser.add_argument("--compile-timeout", type=int, default=120, help="Compile timeout in seconds (default: 120)")
    parser.add_argument("--run-timeout", type=int, default=300, help="Run timeout in seconds (default: 300)")
    parser.add_argument("--workspace", type=Path, default=Path.cwd(), help="Workspace root directory")
    
    args = parser.parse_args()
    
    print("="*60)
    print("DSIM UVM Batch Compile-and-Run")
    print("="*60)
    print(f"Test Name:        {args.test_name}")
    print(f"Verbosity:        {args.verbosity}")
    print(f"Waveforms:        {'Enabled' if args.waves else 'Disabled'}")
    print(f"Coverage:         {'Enabled' if args.coverage else 'Disabled'}")
    print(f"Compile Timeout:  {args.compile_timeout}s")
    print(f"Run Timeout:      {args.run_timeout}s")
    print("="*60)
    
    # Phase 1: Compile
    print("\n[PHASE 1] COMPILING...")
    compile_result = run_mcp_tool(
        workspace=args.workspace,
        tool="run_uvm_simulation",
        test_name=args.test_name,
        mode="compile",
        verbosity="UVM_LOW",  # Low verbosity for compile
        waves=False,
        timeout=args.compile_timeout
    )
    
    if compile_result != 0:
        print("\n❌ COMPILATION FAILED")
        print(f"Exit code: {compile_result}")
        return compile_result
    
    print("\n✅ COMPILATION SUCCESSFUL")
    
    # Small delay to ensure license release
    print("\nWaiting 2 seconds for license release...")
    time.sleep(2)
    
    # Phase 2: Run
    print("\n[PHASE 2] RUNNING SIMULATION...")
    run_result = run_mcp_tool(
        workspace=args.workspace,
        tool="run_uvm_simulation",
        test_name=args.test_name,
        mode="run",
        verbosity=args.verbosity,
        waves=args.waves,
        coverage=args.coverage,
        timeout=args.run_timeout
    )
    
    if run_result != 0:
        print("\n❌ SIMULATION FAILED")
        print(f"Exit code: {run_result}")
        return run_result
    
    print("\n✅ SIMULATION SUCCESSFUL")
    print("\n" + "="*60)
    print("BATCH EXECUTION COMPLETED SUCCESSFULLY")
    print("="*60)
    
    return 0

if __name__ == "__main__":
    sys.exit(main())
