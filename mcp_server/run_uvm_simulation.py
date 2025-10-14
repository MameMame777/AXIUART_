#!/usr/bin/env python3
"""DSIM UVM Simulation Runner Script (DEPRECATED - USE MCP CLIENT)

DEPRECATION WARNING:
This direct execution approach violates MCP best practices.
Please use MCP client instead:
    python mcp_server/mcp_client.py --tool run_uvm_simulation
"""

import warnings
import asyncio
import sys
import os
from pathlib import Path
import argparse

if sys.platform == "win32":
    asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())

# Deprecation warning
warnings.warn(
    "Direct script execution is deprecated. Use 'python mcp_server/mcp_client.py --tool run_uvm_simulation' instead.",
    DeprecationWarning,
    stacklevel=2
)

print("WARNING: This script is deprecated!")
print("Use MCP protocol instead:")
print("    python mcp_server/mcp_client.py --workspace . --tool run_uvm_simulation")
print("="*70)

# Add mcp_server to path
sys.path.append(os.path.dirname(__file__))

from dsim_uvm_server import setup_workspace, run_uvm_simulation  # type: ignore

async def main():
    parser = argparse.ArgumentParser(description='Run DSIM UVM Simulation')
    parser.add_argument('--test_name', required=True, help='Test name to run')
    parser.add_argument('--mode', default='run', choices=['compile', 'run'], help='Simulation mode')
    parser.add_argument('--verbosity', default='UVM_MEDIUM', help='UVM verbosity level')
    parser.add_argument('--waves', action='store_true', help='Enable waveform generation')
    parser.add_argument('--coverage', action='store_true', help='Enable coverage collection')
    parser.add_argument('--timeout', type=int, default=300, help='Timeout in seconds')
    
    args = parser.parse_args()
    
    workspace = Path(__file__).resolve().parents[1]
    setup_workspace(str(workspace))

    result = await run_uvm_simulation(
        test_name=args.test_name,
        mode=args.mode,
        verbosity=args.verbosity,
        waves=args.waves,
        coverage=args.coverage,
        timeout=args.timeout
    )

    print(result)

if __name__ == "__main__":
    asyncio.run(main())