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
import json
import logging
import sys
import argparse
from pathlib import Path
from typing import Any, Dict, List, Optional
import subprocess
import signal
import time

# Configure stdout/stderr encoding for Windows compatibility
if sys.platform == "win32":
    import io
    sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
    sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding='utf-8')

# MCP Client imports
try:
    from mcp.client.session import ClientSession
    from mcp.client.stdio import stdio_client
    from mcp.types import CallToolRequest, TextContent
except ImportError as e:
    print(f"Error: MCP client package not found. Install with: pip install mcp", file=sys.stderr)
    sys.exit(1)

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
logger = logging.getLogger("mcp-client")

class DSIMMCPClient:
    """MCP Client for DSIM UVM simulation tools"""
    
    def __init__(self, workspace_path: Path):
        self.workspace_path = workspace_path
        self.mcp_server_path = workspace_path / "mcp_server" / "dsim_uvm_server.py"
        self.session: Optional[ClientSession] = None
        self.server_process: Optional[subprocess.Popen] = None
        
    async def start_server(self) -> bool:
        """Start the MCP server process"""
        try:
            # Start MCP server process
            cmd = [
                sys.executable,
                str(self.mcp_server_path),
                "--workspace",
                str(self.workspace_path)
            ]
            
            env = {
                "DSIM_HOME": "C:\\Users\\Nautilus\\AppData\\Local\\metrics-ca\\dsim\\20240422.0.0",
                "DSIM_ROOT": "C:\\Users\\Nautilus\\AppData\\Local\\metrics-ca\\dsim\\20240422.0.0", 
                "DSIM_LIB_PATH": "C:\\Users\\Nautilus\\AppData\\Local\\metrics-ca\\dsim\\20240422.0.0\\lib",
                "DSIM_LICENSE": "C:\\Users\\Nautilus\\AppData\\Local\\metrics-ca\\dsim-license.json"
            }
            
            # Update with current environment
            import os
            env.update(os.environ)
            
            logger.info(f"Starting MCP server: {' '.join(cmd)}")
            self.server_process = subprocess.Popen(
                cmd,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                env=env,
                text=True
            )
            
            # Give server time to start
            await asyncio.sleep(2)
            
            if self.server_process.poll() is not None:
                stderr_output = self.server_process.stderr.read() if self.server_process.stderr else ""
                logger.error(f"MCP server failed to start. Exit code: {self.server_process.poll()}")
                logger.error(f"Error output: {stderr_output}")
                return False
                
            logger.info("MCP server started successfully")
            return True
            
        except Exception as e:
            logger.error(f"Failed to start MCP server: {e}")
            return False
    
    async def connect(self) -> bool:
        """Connect to the MCP server"""
        try:
            if not self.server_process:
                logger.error("MCP server not started")
                return False
                
            # Create stdio client session
            read, write = self.server_process.stdout, self.server_process.stdin
            
            async with stdio_client(read, write) as (read_stream, write_stream):
                self.session = ClientSession(read_stream, write_stream)
                
                # Initialize session
                await self.session.initialize()
                logger.info("Connected to MCP server successfully")
                return True
                
        except Exception as e:
            logger.error(f"Failed to connect to MCP server: {e}")
            return False
    
    async def list_tools(self) -> List[Dict[str, Any]]:
        """List available tools from MCP server"""
        try:
            if not self.session:
                logger.error("Not connected to MCP server")
                return []
                
            result = await self.session.list_tools()
            tools = [{"name": tool.name, "description": tool.description} for tool in result.tools]
            logger.info(f"Available tools: {[tool['name'] for tool in tools]}")
            return tools
            
        except Exception as e:
            logger.error(f"Failed to list tools: {e}")
            return []
    
    async def call_tool(self, tool_name: str, arguments: Dict[str, Any]) -> Dict[str, Any]:
        """Call a tool via MCP protocol"""
        try:
            if not self.session:
                logger.error("Not connected to MCP server")
                return {"error": "Not connected to MCP server"}
                
            logger.info(f"Calling tool: {tool_name} with args: {arguments}")
            
            result = await self.session.call_tool(tool_name, arguments)
            
            # Extract content from result
            if result.content and len(result.content) > 0:
                content = result.content[0]
                if hasattr(content, 'text'):
                    response_text = content.text
                    try:
                        # Try to parse as JSON
                        response_data = json.loads(response_text)
                        logger.info(f"Tool {tool_name} completed successfully")
                        return response_data
                    except json.JSONDecodeError:
                        # Return as plain text
                        return {"status": "success", "output": response_text}
                        
            return {"status": "success", "content": str(result.content)}
            
        except Exception as e:
            logger.error(f"Failed to call tool {tool_name}: {e}")
            return {"error": str(e)}
    
    async def stop_server(self):
        """Stop the MCP server process"""
        if self.server_process:
            try:
                self.server_process.terminate()
                await asyncio.sleep(1)
                if self.server_process.poll() is None:
                    self.server_process.kill()
                logger.info("MCP server stopped")
            except Exception as e:
                logger.error(f"Error stopping MCP server: {e}")

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
    
    # MCP server command
    cmd = [
        sys.executable,
        str(workspace_path / "mcp_server" / "dsim_uvm_server.py"),
        "--workspace",
        str(workspace_path)
    ]
    
    env = {
        "DSIM_HOME": "C:\\Users\\Nautilus\\AppData\\Local\\metrics-ca\\dsim\\20240422.0.0",
        "DSIM_ROOT": "C:\\Users\\Nautilus\\AppData\\Local\\metrics-ca\\dsim\\20240422.0.0", 
        "DSIM_LIB_PATH": "C:\\Users\\Nautilus\\AppData\\Local\\metrics-ca\\dsim\\20240422.0.0\\lib",
        "DSIM_LICENSE": "C:\\Users\\Nautilus\\AppData\\Local\\metrics-ca\\dsim-license.json"
    }
    
    # Update with current environment
    import os
    env.update(os.environ)
    
    try:
        logger.info(f"Starting MCP server: {' '.join(cmd)}")
        
        # Start MCP server process
        server_process = subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=env,
            text=True
        )
        
        # Give server time to start
        await asyncio.sleep(2)
        
        if server_process.poll() is not None:
            stderr_output = server_process.stderr.read() if server_process.stderr else ""
            logger.error(f"MCP server failed to start. Exit code: {server_process.poll()}")
            logger.error(f"Error output: {stderr_output}")
            sys.exit(1)
            
        logger.info("MCP server started successfully")
        
        # Connect using stdio communication
        async with stdio_client(server_process.stdout, server_process.stdin) as (read_stream, write_stream):
            session = ClientSession(read_stream, write_stream)
            await session.initialize()
            
            # List available tools
            tools_result = await session.list_tools()
            available_tools = [tool.name for tool in tools_result.tools]
            logger.info(f"Available tools: {available_tools}")
            
            if args.tool not in available_tools:
                logger.error(f"Tool '{args.tool}' not available. Available tools: {available_tools}")
                server_process.terminate()
                sys.exit(1)
            
            # Prepare arguments based on tool
            tool_args = {}
            if args.tool == "run_uvm_simulation":
                tool_args = {
                    "test_name": args.test_name,
                    "mode": args.mode,
                    "verbosity": args.verbosity,
                    "waves": args.waves,
                    "coverage": args.coverage,
                    "timeout": args.timeout
                }
            elif args.tool == "check_dsim_environment":
                pass  # No arguments needed
            elif args.tool == "list_available_tests":
                pass  # No arguments needed
            
            # Call the tool
            result = await session.call_tool(args.tool, tool_args)
            
            # Display results
            print("\n" + "="*50)
            print(f"MCP Tool Result: {args.tool}")
            print("="*50)
            
            if result.content:
                for content in result.content:
                    if hasattr(content, 'text'):
                        print(content.text)
                    else:
                        print(str(content))
            else:
                print("No content returned")
                
        # Clean shutdown
        server_process.terminate()
        await asyncio.sleep(1)
        if server_process.poll() is None:
            server_process.kill()
        logger.info("MCP server stopped")
            
    except KeyboardInterrupt:
        logger.info("Interrupted by user")
        if 'server_process' in locals():
            server_process.terminate()
    except Exception as e:
        logger.error(f"Error: {e}")
        if 'server_process' in locals():
            server_process.terminate()
        sys.exit(1)

if __name__ == "__main__":
    asyncio.run(main())