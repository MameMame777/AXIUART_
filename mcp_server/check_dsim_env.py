#!/usr/bin/env python3
"""DSIM Environment Check Script"""

import asyncio
import sys
from pathlib import Path

if sys.platform == "win32":
    asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())

# Add mcp_server to path
sys.path.append(str(Path(__file__).parent))

from dsim_uvm_server import setup_workspace, check_dsim_environment  # type: ignore


async def main() -> None:
    workspace = Path(__file__).resolve().parents[1]
    setup_workspace(str(workspace))
    report = await check_dsim_environment()
    print(report)


if __name__ == "__main__":
    asyncio.run(main())