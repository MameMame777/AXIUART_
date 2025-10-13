#!/usr/bin/env python3
"""DSIM Environment Check Script"""

import asyncio
import sys
import os

# Add mcp_server to path
sys.path.append(os.path.dirname(__file__))

from dsim_uvm_server import DSIMSimulationServer

async def main():
    workspace = os.path.dirname(os.path.dirname(__file__))
    server = DSIMSimulationServer(workspace)
    result = await server._check_dsim_environment()
    
    for content in result.content:
        print(content.text)

if __name__ == "__main__":
    asyncio.run(main())