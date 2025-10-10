#!/usr/bin/env python3
"""
AXIUART Verification MCP Server (Standalone Implementation)
Model Context Protocol server for SystemVerilog UVM verification automation
"""

import asyncio
import json
import logging
import sys
import os
from pathlib import Path
from typing import Any, Dict, List, Optional

# Setup logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("axiuart-verification-mcp")

# Add UVM checker modules to path
sys.path.insert(0, str(Path(__file__).parent.parent / "uvm_checker"))

try:
    from environment_checker import DSIMEnvironmentChecker
    from test_runner import UVMTestRunner
    from log_analyzer import DSIMLogAnalyzer
except ImportError as e:
    logger.warning(f"Failed to import verification modules: {e}")
    DSIMEnvironmentChecker = None
    UVMTestRunner = None
    DSIMLogAnalyzer = None

class MCPRequest:
    """MCP request wrapper"""
    def __init__(self, method: str, params: Dict[str, Any] = None, id: Any = None):
        self.method = method
        self.params = params or {}
        self.id = id

class MCPResponse:
    """MCP response wrapper"""
    def __init__(self, result: Any = None, error: Dict[str, Any] = None, id: Any = None):
        self.result = result
        self.error = error
        self.id = id
    
    def to_dict(self) -> Dict[str, Any]:
        response = {"jsonrpc": "2.0"}
        if self.id is not None:
            response["id"] = self.id
        if self.error:
            response["error"] = self.error
        else:
            response["result"] = self.result
        return response

class AXIUARTVerificationMCP:
    """MCP Server for AXIUART SystemVerilog UVM Verification"""
    
    def __init__(self):
        self.project_root = self._find_project_root()
        
        # Initialize verification components
        self.env_checker = None
        self.test_runner = None
        self.log_analyzer = None
        
        if DSIMEnvironmentChecker:
            try:
                self.env_checker = DSIMEnvironmentChecker()
                self.test_runner = UVMTestRunner()
                self.log_analyzer = DSIMLogAnalyzer()
                logger.info("Verification components initialized successfully")
            except Exception as e:
                logger.warning(f"Failed to initialize verification components: {e}")
    
    def _find_project_root(self) -> Path:
        """Find AXIUART project root directory"""
        current = Path(__file__).parent
        while current != current.parent:
            if (current / "rtl" / "AXIUART_Top.sv").exists():
                return current
            current = current.parent
        # Default to current working directory
        return Path.cwd()
    
    async def handle_request(self, request: MCPRequest) -> MCPResponse:
        """Handle MCP request"""
        try:
            if request.method == "initialize":
                return await self._handle_initialize(request)
            elif request.method == "tools/list":
                return await self._handle_list_tools(request)
            elif request.method == "tools/call":
                return await self._handle_call_tool(request)
            elif request.method == "resources/list":
                return await self._handle_list_resources(request)
            elif request.method == "resources/read":
                return await self._handle_read_resource(request)
            else:
                return MCPResponse(
                    error={"code": -32601, "message": f"Method not found: {request.method}"},
                    id=request.id
                )
        except Exception as e:
            logger.error(f"Request handling failed: {e}")
            return MCPResponse(
                error={"code": -32603, "message": f"Internal error: {str(e)}"},
                id=request.id
            )
    
    async def _handle_initialize(self, request: MCPRequest) -> MCPResponse:
        """Handle initialization request"""
        return MCPResponse(
            result={
                "protocolVersion": "2024-11-05",
                "capabilities": {
                    "tools": {},
                    "resources": {}
                },
                "serverInfo": {
                    "name": "axiuart-verification",
                    "version": "1.0.0"
                }
            },
            id=request.id
        )
    
    async def _handle_list_tools(self, request: MCPRequest) -> MCPResponse:
        """List available verification tools"""
        tools = [
            {
                "name": "check_environment",
                "description": "Validate DSIM environment and project setup",
                "inputSchema": {
                    "type": "object",
                    "properties": {
                        "verbose": {
                            "type": "boolean",
                            "description": "Enable verbose output",
                            "default": False
                        }
                    }
                }
            },
            {
                "name": "run_uvm_test", 
                "description": "Execute UVM test with specified parameters",
                "inputSchema": {
                    "type": "object",
                    "properties": {
                        "test_name": {
                            "type": "string",
                            "description": "UVM test name to execute",
                            "default": "uart_axi4_register_verification_test"
                        },
                        "seed": {
                            "type": "integer", 
                            "description": "Random seed for test execution",
                            "default": 12345
                        }
                    }
                }
            },
            {
                "name": "analyze_logs",
                "description": "Analyze UVM test logs for errors and issues",
                "inputSchema": {
                    "type": "object",
                    "properties": {
                        "log_path": {
                            "type": "string",
                            "description": "Path to log file (default: latest dsim.log)"
                        }
                    }
                }
            },
            {
                "name": "debug_phase_issues",
                "description": "Debug current Phase 1-3 issues (CRC, alignment, register access)",
                "inputSchema": {
                    "type": "object",
                    "properties": {
                        "phase": {
                            "type": "string",
                            "enum": ["auto", "phase1", "phase2", "phase3"],
                            "description": "Target phase for debugging",
                            "default": "auto"
                        }
                    }
                }
            },
            {
                "name": "get_phase_guidance",
                "description": "Get guidance for current verification phase",
                "inputSchema": {
                    "type": "object",
                    "properties": {}
                }
            }
        ]
        
        return MCPResponse(result={"tools": tools}, id=request.id)
    
    async def _handle_call_tool(self, request: MCPRequest) -> MCPResponse:
        """Execute verification tool"""
        tool_name = request.params.get("name")
        arguments = request.params.get("arguments", {})
        
        try:
            if tool_name == "check_environment":
                result = await self._tool_check_environment(arguments)
            elif tool_name == "run_uvm_test":
                result = await self._tool_run_uvm_test(arguments)
            elif tool_name == "analyze_logs":
                result = await self._tool_analyze_logs(arguments)
            elif tool_name == "debug_phase_issues":
                result = await self._tool_debug_phase_issues(arguments)
            elif tool_name == "get_phase_guidance":
                result = await self._tool_get_phase_guidance(arguments)
            else:
                return MCPResponse(
                    error={"code": -32601, "message": f"Unknown tool: {tool_name}"},
                    id=request.id
                )
            
            return MCPResponse(result={"content": result}, id=request.id)
            
        except Exception as e:
            logger.error(f"Tool {tool_name} failed: {e}")
            return MCPResponse(
                error={"code": -32603, "message": f"Tool execution failed: {str(e)}"},
                id=request.id
            )
    
    async def _handle_list_resources(self, request: MCPRequest) -> MCPResponse:
        """List available resources"""
        resources = [
            {
                "uri": "axiuart://environment/status",
                "name": "Environment Status",
                "description": "DSIM environment validation status",
                "mimeType": "application/json"
            },
            {
                "uri": "axiuart://logs/latest",
                "name": "Latest Test Logs",
                "description": "Most recent UVM test execution logs",
                "mimeType": "text/plain"
            },
            {
                "uri": "axiuart://phase/status",
                "name": "Phase Status", 
                "description": "Current verification phase status",
                "mimeType": "application/json"
            }
        ]
        
        return MCPResponse(result={"resources": resources}, id=request.id)
    
    async def _handle_read_resource(self, request: MCPRequest) -> MCPResponse:
        """Read resource content"""
        uri = request.params.get("uri")
        
        try:
            if uri == "axiuart://environment/status":
                content = await self._get_environment_status()
            elif uri == "axiuart://logs/latest":
                content = await self._get_latest_logs()
            elif uri == "axiuart://phase/status":
                content = await self._get_phase_status()
            else:
                return MCPResponse(
                    error={"code": -32601, "message": f"Unknown resource: {uri}"},
                    id=request.id
                )
            
            return MCPResponse(
                result={
                    "contents": [
                        {
                            "type": "text",
                            "text": content
                        }
                    ]
                },
                id=request.id
            )
            
        except Exception as e:
            return MCPResponse(
                error={"code": -32603, "message": f"Resource read failed: {str(e)}"},
                id=request.id
            )
    
    # Tool implementations
    async def _tool_check_environment(self, args: Dict[str, Any]) -> List[Dict[str, Any]]:
        """Check DSIM environment and project setup"""
        if not self.env_checker:
            return [{"type": "text", "text": "❌ Environment checker not available"}]
        
        verbose = args.get("verbose", False)
        
        try:
            report = self.env_checker.generate_environment_report()
            
            result = "🔍 AXIUART Environment Check Results\n"
            result += "=" * 50 + "\n"
            result += f"Project Root: {report.get('project_root', 'Unknown')}\n"
            result += f"Overall Status: {'✅ READY' if report.get('overall_status') else '❌ ISSUES FOUND'}\n\n"
            
            # Environment variables
            env_vars = report.get("environment_variables", {})
            result += "📋 Environment Variables:\n"
            for var, status in env_vars.items():
                if status is True:
                    result += f"  ✅ {var}\n"
                elif status is False:
                    result += f"  ❌ {var}\n"
                else:
                    result += f"  ⚠️  {var} (optional)\n"
            
            if verbose:
                result += f"\n📊 Full Report:\n{json.dumps(report, indent=2)}"
            
            return [{"type": "text", "text": result}]
            
        except Exception as e:
            return [{"type": "text", "text": f"❌ Environment check failed: {str(e)}"}]
    
    async def _tool_run_uvm_test(self, args: Dict[str, Any]) -> List[Dict[str, Any]]:
        """Run UVM test with specified parameters"""
        if not self.test_runner:
            return [{"type": "text", "text": "❌ Test runner not available"}]
        
        test_name = args.get("test_name", "uart_axi4_register_verification_test")
        seed = args.get("seed", 12345)
        
        try:
            result_text = f"🚀 Running UVM Test: {test_name}\n"
            result_text += f"Parameters: seed={seed}\n"
            result_text += "=" * 60 + "\n"
            
            # Execute test
            test_result = self.test_runner.run_test(
                test_name=test_name,
                seed=seed
            )
            
            # Format results
            status = "✅ PASSED" if test_result.success else "❌ FAILED"
            result_text += f"Status: {status}\n"
            result_text += f"Duration: {test_result.duration:.1f}s\n"
            result_text += f"Errors: {test_result.error_count}\n"
            result_text += f"Warnings: {test_result.warning_count}\n"
            
            return [{"type": "text", "text": result_text}]
            
        except Exception as e:
            return [{"type": "text", "text": f"❌ Test execution failed: {str(e)}"}]
    
    async def _tool_analyze_logs(self, args: Dict[str, Any]) -> List[Dict[str, Any]]:
        """Analyze UVM test logs for errors"""
        if not self.log_analyzer:
            return [{"type": "text", "text": "❌ Log analyzer not available"}]
        
        log_path = args.get("log_path")
        if not log_path:
            log_path = str(self.project_root / "sim" / "uvm" / "dsim.log")
        
        try:
            analysis = self.log_analyzer.analyze_log_file(log_path)
            
            result_text = f"📋 Log Analysis: {Path(log_path).name}\n"
            result_text += "=" * 50 + "\n"
            result_text += f"Total Lines: {analysis.total_lines}\n"
            result_text += f"Simulation Success: {'✅' if analysis.simulation_success else '❌'}\n\n"
            
            if analysis.crc_errors:
                result_text += f"🔴 CRC Errors ({len(analysis.crc_errors)}):\n"
                for i, error in enumerate(analysis.crc_errors[:3], 1):
                    result_text += f"  {i}. Line {error.line_number}: recv=0x{error.received_crc} exp=0x{error.expected_crc}\n"
            
            if analysis.alignment_errors:
                result_text += f"🔴 Alignment Errors ({len(analysis.alignment_errors)}):\n"
                for i, error in enumerate(analysis.alignment_errors[:3], 1):
                    result_text += f"  {i}. Line {error.line_number}: {error.error_type}\n"
            
            return [{"type": "text", "text": result_text}]
            
        except Exception as e:
            return [{"type": "text", "text": f"❌ Log analysis failed: {str(e)}"}]
    
    async def _tool_debug_phase_issues(self, args: Dict[str, Any]) -> List[Dict[str, Any]]:
        """Debug current Phase 1-3 issues"""
        phase = args.get("phase", "auto")
        
        result_text = "🔧 AXIUART Phase Debug Analysis\n"
        result_text += "=" * 40 + "\n"
        
        # Determine current phase based on log analysis
        if self.log_analyzer:
            log_path = self.project_root / "sim" / "uvm" / "dsim.log"
            if log_path.exists():
                try:
                    analysis = self.log_analyzer.analyze_log_file(str(log_path))
                    
                    if phase == "auto":
                        if analysis.crc_errors:
                            phase = "phase1"
                        elif analysis.alignment_errors:
                            phase = "phase2"
                        elif analysis.uvm_errors:
                            phase = "phase3"
                        else:
                            phase = "phase4"
                    
                    result_text += f"Detected Phase: {phase.upper()}\n\n"
                    
                    if phase == "phase1":
                        result_text += "🎯 Phase 1: CRC Error Resolution\n"
                        result_text += f"Found {len(analysis.crc_errors)} CRC errors\n\n"
                        result_text += "📋 Action Items:\n"
                        result_text += "1. Review Frame_Parser.sv CRC implementation\n"
                        result_text += "2. Verify CRC8 polynomial 0x07 usage\n" 
                        result_text += "3. Check byte ordering and timing\n"
                    
                    elif phase == "phase2":
                        result_text += "🎯 Phase 2: AXI Alignment Error Resolution\n"
                        result_text += f"Found {len(analysis.alignment_errors)} alignment errors\n\n"
                        result_text += "📋 Action Items:\n"
                        result_text += "1. Debug Address_Aligner.sv implementation\n"
                        result_text += "2. Verify 32-bit boundary checking\n"
                        result_text += "3. Check AXI Master state transitions\n"
                    
                    elif phase == "phase3":
                        result_text += "🎯 Phase 3: Register Access Verification\n"
                        result_text += f"Found {len(analysis.uvm_errors)} UVM errors\n\n"
                        result_text += "📋 Action Items:\n"
                        result_text += "1. Verify AXI transactions reach Register_Block\n"
                        result_text += "2. Test register read/write operations\n"
                        result_text += "3. Validate data persistence\n"
                    
                    else:
                        result_text += "🎯 Phase 4: Coverage Improvement Ready\n"
                        result_text += "No critical errors detected\n\n"
                        result_text += "📋 Next Steps:\n"
                        result_text += "1. Focus on coverage improvement\n"
                        result_text += "2. Achieve ≥60% toggle coverage\n"
                
                except Exception as e:
                    result_text += f"⚠️  Log analysis failed: {e}\n"
            else:
                result_text += "⚠️  No log file available for analysis\n"
        
        return [{"type": "text", "text": result_text}]
    
    async def _tool_get_phase_guidance(self, args: Dict[str, Any]) -> List[Dict[str, Any]]:
        """Get guidance for current verification phase"""
        guidance_text = "📚 AXIUART Verification Phase Guidance\n"
        guidance_text += "=" * 45 + "\n\n"
        
        guidance_text += "🎯 Phase 1: CRC Error Resolution\n"
        guidance_text += "Goal: Fix CRC calculation errors in Frame_Parser\n"
        guidance_text += "Key Files: rtl/Frame_Parser.sv\n\n"
        
        guidance_text += "🎯 Phase 2: AXI Alignment Error Resolution\n"
        guidance_text += "Goal: Fix address alignment checking\n"
        guidance_text += "Key Files: rtl/Address_Aligner.sv\n\n"
        
        guidance_text += "🎯 Phase 3: Register Access Verification\n"
        guidance_text += "Goal: Ensure register read/write operations work\n"
        guidance_text += "Key Files: rtl/Register_Block.sv\n\n"
        
        guidance_text += "🎯 Phase 4: Coverage Improvement\n"
        guidance_text += "Goal: Achieve ≥60% toggle coverage\n\n"
        
        guidance_text += "💡 Available MCP Tools:\n"
        guidance_text += "- check_environment: Validate DSIM setup\n"
        guidance_text += "- run_uvm_test: Execute single test\n"
        guidance_text += "- analyze_logs: Find specific errors\n"
        guidance_text += "- debug_phase_issues: Get targeted guidance\n"
        
        return [{"type": "text", "text": guidance_text}]
    
    # Resource implementations
    async def _get_environment_status(self) -> str:
        """Get environment status as JSON string"""
        if self.env_checker:
            try:
                report = self.env_checker.generate_environment_report()
                return json.dumps(report, indent=2)
            except Exception as e:
                return json.dumps({"error": f"Environment check failed: {str(e)}"})
        else:
            return json.dumps({"error": "Environment checker not available"})
    
    async def _get_latest_logs(self) -> str:
        """Get latest log file content"""
        log_path = self.project_root / "sim" / "uvm" / "dsim.log"
        if log_path.exists():
            try:
                return log_path.read_text(encoding='utf-8', errors='replace')
            except Exception as e:
                return f"Failed to read log file: {str(e)}"
        else:
            return f"No log file found at: {log_path}"
    
    async def _get_phase_status(self) -> str:
        """Get current phase status as JSON string"""
        phase_status = {
            "current_phase": "unknown",
            "phase_description": "Analysis required",
            "last_updated": None
        }
        
        if self.log_analyzer:
            log_path = self.project_root / "sim" / "uvm" / "dsim.log"
            if log_path.exists():
                try:
                    analysis = self.log_analyzer.analyze_log_file(str(log_path))
                    
                    if analysis.crc_errors:
                        phase_status.update({
                            "current_phase": "phase1",
                            "phase_description": "CRC Error Resolution Required",
                            "error_count": len(analysis.crc_errors)
                        })
                    elif analysis.alignment_errors:
                        phase_status.update({
                            "current_phase": "phase2",
                            "phase_description": "AXI Alignment Error Resolution Required",
                            "error_count": len(analysis.alignment_errors)
                        })
                    elif analysis.uvm_errors:
                        phase_status.update({
                            "current_phase": "phase3",
                            "phase_description": "Register Access Verification Required",
                            "error_count": len(analysis.uvm_errors)
                        })
                    else:
                        phase_status.update({
                            "current_phase": "phase4",
                            "phase_description": "Coverage Improvement Ready",
                            "error_count": 0
                        })
                    
                    phase_status["last_updated"] = log_path.stat().st_mtime
                    
                except Exception as e:
                    phase_status["error"] = f"Phase analysis failed: {str(e)}"
        
        return json.dumps(phase_status, indent=2)

async def main():
    """Main MCP server entry point"""
    server = AXIUARTVerificationMCP()
    
    # Simple stdio-based MCP server
    while True:
        try:
            # Read JSON-RPC request from stdin
            line = await asyncio.get_event_loop().run_in_executor(None, sys.stdin.readline)
            if not line:
                break
            
            # Parse request
            try:
                request_data = json.loads(line.strip())
                request = MCPRequest(
                    method=request_data.get("method"),
                    params=request_data.get("params", {}),
                    id=request_data.get("id")
                )
            except json.JSONDecodeError as e:
                response = MCPResponse(
                    error={"code": -32700, "message": f"Parse error: {str(e)}"}
                )
                print(json.dumps(response.to_dict()))
                continue
            
            # Handle request
            response = await server.handle_request(request)
            
            # Send response
            print(json.dumps(response.to_dict()))
            sys.stdout.flush()
            
        except Exception as e:
            logger.error(f"Server error: {e}")
            response = MCPResponse(
                error={"code": -32603, "message": f"Internal error: {str(e)}"}
            )
            print(json.dumps(response.to_dict()))
            break

if __name__ == "__main__":
    asyncio.run(main())