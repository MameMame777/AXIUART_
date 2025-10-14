#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
DSIM MCP Server - VS Code Integration Fixed Version
VS Code MCP統合に完全対応したFallback実装

Created: October 14, 2025
Purpose: VS Code MCP統合問題を解決する簡潔な実装
"""

import asyncio
import json
import logging
import os
import sys
import subprocess
from pathlib import Path
from typing import Any, Dict, List, Optional
import argparse
from datetime import datetime

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[logging.StreamHandler(sys.stderr)]
)
logger = logging.getLogger("dsim-mcp-simplified")

class DSIMMCPServer:
    """Simplified MCP Server for VS Code integration"""
    
    def __init__(self, workspace_path: str):
        self.workspace_path = Path(workspace_path)
        
    async def run_stdio(self):
        """Run server with stdio transport"""
        logger.info("Starting DSIM MCP Server (stdio transport)")
        
        # Initialize request
        init_request = {
            "jsonrpc": "2.0",
            "id": 1,
            "method": "initialize",
            "params": {
                "protocolVersion": "2024-11-05",
                "capabilities": {
                    "tools": {}
                },
                "clientInfo": {
                    "name": "vscode-copilot",
                    "version": "1.0.0"
                }
            }
        }
        
        # Send initialize response
        init_response = {
            "jsonrpc": "2.0",
            "id": 1,
            "result": {
                "protocolVersion": "2024-11-05",
                "capabilities": {
                    "tools": {
                        "listChanged": True
                    }
                },
                "serverInfo": {
                    "name": "dsim-mcp-server",
                    "version": "1.0.0"
                }
            }
        }
        
        print(json.dumps(init_response))
        sys.stdout.flush()
        
        # Main message loop
        while True:
            try:
                line = sys.stdin.readline()
                if not line:
                    break
                    
                try:
                    request = json.loads(line.strip())
                    response = await self.handle_request(request)
                    if response:
                        print(json.dumps(response))
                        sys.stdout.flush()
                except json.JSONDecodeError:
                    logger.warning(f"Invalid JSON: {line.strip()}")
                    
            except KeyboardInterrupt:
                break
            except Exception as e:
                logger.error(f"Error in message loop: {e}")
                break
                
        logger.info("DSIM MCP Server stopped")
    
    async def handle_request(self, request: Dict[str, Any]) -> Optional[Dict[str, Any]]:
        """Handle MCP requests"""
        method = request.get("method")
        request_id = request.get("id")
        
        if method == "tools/list":
            return {
                "jsonrpc": "2.0",
                "id": request_id,
                "result": {
                    "tools": [
                        {
                            "name": "check_dsim_environment",
                            "description": "Check DSIM environment status",
                            "inputSchema": {
                                "type": "object",
                                "properties": {},
                                "required": []
                            }
                        },
                        {
                            "name": "list_available_tests", 
                            "description": "List available UVM tests",
                            "inputSchema": {
                                "type": "object",
                                "properties": {},
                                "required": []
                            }
                        },
                        {
                            "name": "compile_design",
                            "description": "Compile design for syntax checking",
                            "inputSchema": {
                                "type": "object", 
                                "properties": {
                                    "test_name": {
                                        "type": "string",
                                        "description": "Name of the test to compile"
                                    }
                                },
                                "required": ["test_name"]
                            }
                        }
                    ]
                }
            }
            
        elif method == "tools/call":
            params = request.get("params", {})
            tool_name = params.get("name")
            arguments = params.get("arguments", {})
            
            result = await self.execute_tool(tool_name, arguments)
            
            return {
                "jsonrpc": "2.0",
                "id": request_id,
                "result": {
                    "content": [
                        {
                            "type": "text",
                            "text": json.dumps(result, indent=2)
                        }
                    ]
                }
            }
            
        return None
    
    async def execute_tool(self, tool_name: str, arguments: Dict[str, Any]) -> Dict[str, Any]:
        """Execute tool commands"""
        logger.info(f"Executing tool: {tool_name} with args: {arguments}")
        
        try:
            if tool_name == "check_dsim_environment":
                return await self.check_dsim_environment()
            elif tool_name == "list_available_tests":
                return await self.list_available_tests()
            elif tool_name == "compile_design":
                test_name = arguments.get("test_name", "uart_axi4_basic_test")
                return await self.compile_design(test_name)
            else:
                return {
                    "status": "error",
                    "message": f"Unknown tool: {tool_name}"
                }
        except Exception as e:
            logger.error(f"Tool execution error: {e}")
            return {
                "status": "error",
                "message": str(e)
            }
    
    async def check_dsim_environment(self) -> Dict[str, Any]:
        """Check DSIM environment"""
        try:
            script_path = self.workspace_path / "mcp_server" / "check_dsim_env.py"
            result = subprocess.run(
                [sys.executable, str(script_path)],
                capture_output=True,
                text=True,
                timeout=30,
                cwd=str(self.workspace_path)
            )
            
            return {
                "status": "success" if result.returncode == 0 else "error",
                "exit_code": result.returncode,
                "output": result.stdout,
                "error": result.stderr,
                "dsim_home": os.environ.get("DSIM_HOME"),
                "dsim_license": os.environ.get("DSIM_LICENSE")
            }
        except Exception as e:
            return {
                "status": "error",
                "message": str(e)
            }
    
    async def list_available_tests(self) -> Dict[str, Any]:
        """List available UVM tests"""
        try:
            script_path = self.workspace_path / "mcp_server" / "list_available_tests.py"
            result = subprocess.run(
                [sys.executable, str(script_path)],
                capture_output=True,
                text=True,
                timeout=30,
                cwd=str(self.workspace_path)
            )
            
            return {
                "status": "success" if result.returncode == 0 else "error",
                "exit_code": result.returncode,
                "output": result.stdout,
                "error": result.stderr
            }
        except Exception as e:
            return {
                "status": "error",
                "message": str(e)
            }
    
    async def compile_design(self, test_name: str) -> Dict[str, Any]:
        """Compile design for syntax checking"""
        try:
            script_path = self.workspace_path / "mcp_server" / "run_uvm_simulation.py"
            result = subprocess.run(
                [sys.executable, str(script_path), 
                 "--test_name", test_name,
                 "--mode", "compile",
                 "--verbosity", "UVM_LOW",
                 "--timeout", "120"],
                capture_output=True,
                text=True,
                timeout=120,
                cwd=str(self.workspace_path)
            )
            
            return {
                "status": "success" if result.returncode == 0 else "error",
                "exit_code": result.returncode,
                "output": result.stdout,
                "error": result.stderr,
                "test_name": test_name,
                "mode": "compile"
            }
        except Exception as e:
            return {
                "status": "error",
                "message": str(e),
                "test_name": test_name
            }

def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(description="DSIM MCP Server - VS Code Integration")
    parser.add_argument("--workspace", required=True, help="Workspace directory path")
    parser.add_argument("--transport", choices=["stdio", "http"], default="stdio", 
                       help="Transport method")
    parser.add_argument("--debug", action="store_true", help="Enable debug logging")
    
    args = parser.parse_args()
    
    if args.debug:
        logging.getLogger().setLevel(logging.DEBUG)
    
    server = DSIMMCPServer(args.workspace)
    
    if args.transport == "stdio":
        asyncio.run(server.run_stdio())
    else:
        logger.error("HTTP transport not implemented")
        sys.exit(1)

if __name__ == "__main__":
    main()