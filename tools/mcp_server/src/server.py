#!/usr/bin/env python3
"""
AXIUART Verification MCP Server
Model Context Protocol server for SystemVerilog UVM verification automation
"""

import asyncio
import json
import logging
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence

# MCP imports
from mcp.server import Server
from mcp.server.models import InitializationOptions
from mcp.server.stdio import stdio_server
from mcp.types import (
    Resource,
    Tool,
    TextContent,
    ImageContent,
    EmbeddedResource,
    LoggingLevel
)

# Import our verification modules
sys.path.append(str(Path(__file__).parent.parent / "uvm_checker"))
from environment_checker import DSIMEnvironmentChecker
from test_runner import UVMTestRunner
from log_analyzer import DSIMLogAnalyzer

# Setup logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("axiuart-verification-mcp")

class AXIUARTVerificationMCP:
    """MCP Server for AXIUART SystemVerilog UVM Verification"""
    
    def __init__(self):
        self.server = Server("axiuart-verification")
        self.project_root = self._find_project_root()
        
        # Initialize verification components
        try:
            self.env_checker = DSIMEnvironmentChecker()
            self.test_runner = UVMTestRunner()
            self.log_analyzer = DSIMLogAnalyzer()
        except Exception as e:
            logger.warning(f"Failed to initialize verification components: {e}")
            self.env_checker = None
            self.test_runner = None
            self.log_analyzer = None
        
        self._setup_resources()
        self._setup_tools()
    
    def _find_project_root(self) -> Path:
        """Find AXIUART project root directory"""
        current = Path(__file__).parent
        while current != current.parent:
            if (current / "rtl" / "AXIUART_Top.sv").exists():
                return current
            current = current.parent
        # Default to current directory if not found
        return Path.cwd()
    
    def _setup_resources(self):
        """Setup MCP resources for project information"""
        
        @self.server.list_resources()
        async def list_resources() -> List[Resource]:
            """List available verification resources"""
            resources = [
                Resource(
                    uri="axiuart://environment/status",
                    name="Environment Status",
                    description="DSIM environment validation status",
                    mimeType="application/json"
                ),
                Resource(
                    uri="axiuart://project/structure",
                    name="Project Structure",
                    description="AXIUART project directory structure",
                    mimeType="application/json"
                ),
                Resource(
                    uri="axiuart://logs/latest",
                    name="Latest Test Logs",
                    description="Most recent UVM test execution logs",
                    mimeType="text/plain"
                ),
                Resource(
                    uri="axiuart://coverage/report",
                    name="Coverage Report",
                    description="Latest coverage analysis report",
                    mimeType="application/json"
                ),
                Resource(
                    uri="axiuart://phase/status",
                    name="Phase Status",
                    description="Current verification phase status (Phase 1-4)",
                    mimeType="application/json"
                )
            ]
            return resources
        
        @self.server.read_resource()
        async def read_resource(uri: str) -> str:
            """Read verification resource content"""
            try:
                if uri == "axiuart://environment/status":
                    if self.env_checker:
                        report = self.env_checker.generate_environment_report()
                        return json.dumps(report, indent=2)
                    else:
                        return json.dumps({"error": "Environment checker not available"})
                
                elif uri == "axiuart://project/structure":
                    structure = self._get_project_structure()
                    return json.dumps(structure, indent=2)
                
                elif uri == "axiuart://logs/latest":
                    log_path = self.project_root / "sim" / "uvm" / "dsim.log"
                    if log_path.exists():
                        return log_path.read_text(encoding='utf-8', errors='replace')
                    else:
                        return "No log file found at: " + str(log_path)
                
                elif uri == "axiuart://coverage/report":
                    coverage_data = self._get_coverage_report()
                    return json.dumps(coverage_data, indent=2)
                
                elif uri == "axiuart://phase/status":
                    phase_status = await self._get_phase_status()
                    return json.dumps(phase_status, indent=2)
                
                else:
                    raise ValueError(f"Unknown resource URI: {uri}")
                    
            except Exception as e:
                logger.error(f"Failed to read resource {uri}: {e}")
                return json.dumps({"error": str(e)})
    
    def _setup_tools(self):
        """Setup MCP tools for verification automation"""
        
        @self.server.list_tools()
        async def list_tools() -> List[Tool]:
            """List available verification tools"""
            tools = [
                Tool(
                    name="check_environment",
                    description="Validate DSIM environment and project setup",
                    inputSchema={
                        "type": "object",
                        "properties": {
                            "verbose": {
                                "type": "boolean",
                                "description": "Enable verbose output",
                                "default": False
                            }
                        }
                    }
                ),
                Tool(
                    name="run_uvm_test",
                    description="Execute UVM test with specified parameters",
                    inputSchema={
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
                            },
                            "verbosity": {
                                "type": "string",
                                "enum": ["UVM_LOW", "UVM_MEDIUM", "UVM_HIGH", "UVM_FULL"],
                                "description": "UVM verbosity level",
                                "default": "UVM_MEDIUM"
                            },
                            "coverage": {
                                "type": "boolean",
                                "description": "Enable coverage collection",
                                "default": True
                            }
                        }
                    }
                ),
                Tool(
                    name="analyze_logs",
                    description="Analyze UVM test logs for errors and issues",
                    inputSchema={
                        "type": "object", 
                        "properties": {
                            "log_path": {
                                "type": "string",
                                "description": "Path to log file (default: latest dsim.log)"
                            },
                            "error_types": {
                                "type": "array",
                                "items": {"type": "string"},
                                "description": "Types of errors to analyze",
                                "default": ["crc", "alignment", "uvm"]
                            }
                        }
                    }
                ),
                Tool(
                    name="debug_phase_issues",
                    description="Debug current Phase 1-3 issues (CRC, alignment, register access)",
                    inputSchema={
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
                ),
                Tool(
                    name="run_regression",
                    description="Execute regression test suite with multiple seeds",
                    inputSchema={
                        "type": "object",
                        "properties": {
                            "test_list": {
                                "type": "array",
                                "items": {"type": "string"},
                                "description": "List of tests to run",
                                "default": ["uart_axi4_register_verification_test"]
                            },
                            "seed_count": {
                                "type": "integer",
                                "description": "Number of different seeds to test",
                                "default": 3,
                                "minimum": 1,
                                "maximum": 10
                            }
                        }
                    }
                ),
                Tool(
                    name="get_phase_guidance",
                    description="Get guidance for current verification phase",
                    inputSchema={
                        "type": "object",
                        "properties": {}
                    }
                )
            ]
            return tools
        
        @self.server.call_tool()
        async def call_tool(name: str, arguments: Dict[str, Any]) -> List[TextContent]:
            """Execute verification tool"""
            try:
                if name == "check_environment":
                    return await self._tool_check_environment(arguments)
                elif name == "run_uvm_test":
                    return await self._tool_run_uvm_test(arguments)
                elif name == "analyze_logs":
                    return await self._tool_analyze_logs(arguments)
                elif name == "debug_phase_issues":
                    return await self._tool_debug_phase_issues(arguments)
                elif name == "run_regression":
                    return await self._tool_run_regression(arguments)
                elif name == "get_phase_guidance":
                    return await self._tool_get_phase_guidance(arguments)
                else:
                    return [TextContent(
                        type="text",
                        text=f"Unknown tool: {name}"
                    )]
                    
            except Exception as e:
                logger.error(f"Tool {name} failed: {e}")
                return [TextContent(
                    type="text", 
                    text=f"Tool execution failed: {str(e)}"
                )]
    
    # Tool implementations
    async def _tool_check_environment(self, args: Dict[str, Any]) -> List[TextContent]:
        """Check DSIM environment and project setup"""
        if not self.env_checker:
            return [TextContent(type="text", text="Environment checker not available")]
        
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
            
            # Project structure
            project_struct = report.get("project_structure", {})
            result += "\n📁 Project Structure:\n"
            for dir_name, exists in project_struct.items():
                status = "✅" if exists else "❌"
                result += f"  {status} {dir_name}\n"
            
            # SystemVerilog compliance
            sv_compliance = report.get("systemverilog_compliance", {})
            violations = sv_compliance.get("timescale_violations", [])
            if violations:
                result += "\n⚠️  SystemVerilog Compliance Issues:\n"
                for violation in violations:
                    result += f"  - {violation}\n"
            else:
                result += "\n✅ SystemVerilog Compliance: OK\n"
            
            if verbose:
                result += f"\n📊 Full Report:\n{json.dumps(report, indent=2)}"
            
            return [TextContent(type="text", text=result)]
            
        except Exception as e:
            return [TextContent(type="text", text=f"Environment check failed: {str(e)}")]
    
    async def _tool_run_uvm_test(self, args: Dict[str, Any]) -> List[TextContent]:
        """Run UVM test with specified parameters"""
        if not self.test_runner:
            return [TextContent(type="text", text="Test runner not available")]
        
        test_name = args.get("test_name", "uart_axi4_register_verification_test")
        seed = args.get("seed", 12345)
        verbosity = args.get("verbosity", "UVM_MEDIUM")
        coverage = args.get("coverage", True)
        
        try:
            result_text = f"🚀 Running UVM Test: {test_name}\n"
            result_text += f"Parameters: seed={seed}, verbosity={verbosity}, coverage={coverage}\n"
            result_text += "=" * 60 + "\n"
            
            # Execute test
            test_result = self.test_runner.run_test(
                test_name=test_name,
                seed=seed,
                verbosity=verbosity,
                coverage=coverage
            )
            
            # Format results
            status = "✅ PASSED" if test_result.success else "❌ FAILED"
            result_text += f"Status: {status}\n"
            result_text += f"Duration: {test_result.duration:.1f}s\n"
            result_text += f"Errors: {test_result.error_count}\n"
            result_text += f"Warnings: {test_result.warning_count}\n"
            
            if test_result.log_path:
                result_text += f"Log: {test_result.log_path}\n"
            if test_result.waveform_path:
                result_text += f"Waveform: {test_result.waveform_path}\n"
            if test_result.coverage_path:
                result_text += f"Coverage: {test_result.coverage_path}\n"
            
            return [TextContent(type="text", text=result_text)]
            
        except Exception as e:
            return [TextContent(type="text", text=f"Test execution failed: {str(e)}")]
    
    async def _tool_analyze_logs(self, args: Dict[str, Any]) -> List[TextContent]:
        """Analyze UVM test logs for errors"""
        if not self.log_analyzer:
            return [TextContent(type="text", text="Log analyzer not available")]
        
        log_path = args.get("log_path")
        if not log_path:
            log_path = str(self.project_root / "sim" / "uvm" / "dsim.log")
        
        error_types = args.get("error_types", ["crc", "alignment", "uvm"])
        
        try:
            analysis = self.log_analyzer.analyze_log_file(log_path)
            
            result_text = f"📋 Log Analysis: {Path(log_path).name}\n"
            result_text += "=" * 50 + "\n"
            result_text += f"Total Lines: {analysis.total_lines}\n"
            result_text += f"Simulation Success: {'✅' if analysis.simulation_success else '❌'}\n\n"
            
            # CRC Errors
            if "crc" in error_types and analysis.crc_errors:
                result_text += f"🔴 CRC Errors ({len(analysis.crc_errors)}):\n"
                for i, error in enumerate(analysis.crc_errors[:3], 1):
                    result_text += f"  {i}. Line {error.line_number}: recv=0x{error.received_crc} exp=0x{error.expected_crc}\n"
                if len(analysis.crc_errors) > 3:
                    result_text += f"  ... and {len(analysis.crc_errors) - 3} more\n"
                result_text += "\n"
            
            # Alignment Errors
            if "alignment" in error_types and analysis.alignment_errors:
                result_text += f"🔴 Alignment Errors ({len(analysis.alignment_errors)}):\n"
                for i, error in enumerate(analysis.alignment_errors[:3], 1):
                    result_text += f"  {i}. Line {error.line_number}: {error.error_type} at {error.address}\n"
                if len(analysis.alignment_errors) > 3:
                    result_text += f"  ... and {len(analysis.alignment_errors) - 3} more\n"
                result_text += "\n"
            
            # UVM Errors
            if "uvm" in error_types and analysis.uvm_errors:
                result_text += f"🔴 UVM Errors ({len(analysis.uvm_errors)}):\n"
                for i, error in enumerate(analysis.uvm_errors[:3], 1):
                    result_text += f"  {i}. Line {error.line_number}: {error.severity} - {error.message[:60]}...\n"
                if len(analysis.uvm_errors) > 3:
                    result_text += f"  ... and {len(analysis.uvm_errors) - 3} more\n"
            
            return [TextContent(type="text", text=result_text)]
            
        except Exception as e:
            return [TextContent(type="text", text=f"Log analysis failed: {str(e)}")]
    
    async def _tool_debug_phase_issues(self, args: Dict[str, Any]) -> List[TextContent]:
        """Debug current Phase 1-3 issues"""
        phase = args.get("phase", "auto")
        
        result_text = "🔧 AXIUART Phase Debug Analysis\n"
        result_text += "=" * 40 + "\n"
        
        try:
            # Analyze current log if available
            log_path = self.project_root / "sim" / "uvm" / "dsim.log"
            if log_path.exists() and self.log_analyzer:
                analysis = self.log_analyzer.analyze_log_file(str(log_path))
                
                # Determine phase automatically if requested
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
                    result_text += "4. Create Python reference for comparison\n"
                
                elif phase == "phase2":
                    result_text += "🎯 Phase 2: AXI Alignment Error Resolution\n"
                    result_text += f"Found {len(analysis.alignment_errors)} alignment errors\n\n"
                    result_text += "📋 Action Items:\n"
                    result_text += "1. Debug Address_Aligner.sv implementation\n"
                    result_text += "2. Verify 32-bit boundary checking (0x1000-0x100C)\n"
                    result_text += "3. Check AXI Master state transitions\n"
                    result_text += "4. Validate addr_ok signal generation\n"
                
                elif phase == "phase3":
                    result_text += "🎯 Phase 3: Register Access Verification\n"
                    result_text += f"Found {len(analysis.uvm_errors)} UVM errors\n\n"
                    result_text += "📋 Action Items:\n"
                    result_text += "1. Verify AXI write transactions reach Register_Block\n"
                    result_text += "2. Test register read/write data persistence\n"
                    result_text += "3. Validate 0x44444444 test pattern\n"
                    result_text += "4. Check register address mapping\n"
                
                else:
                    result_text += "🎯 Phase 4: Coverage Improvement Ready\n"
                    result_text += "No critical errors detected\n\n"
                    result_text += "📋 Next Steps:\n"
                    result_text += "1. Focus on coverage improvement\n"
                    result_text += "2. Achieve ≥60% toggle coverage\n"
                    result_text += "3. Expand functional verification\n"
            
            else:
                result_text += "⚠️  No log file available for analysis\n"
                result_text += "Run UVM test first to generate debug information\n"
            
            return [TextContent(type="text", text=result_text)]
            
        except Exception as e:
            return [TextContent(type="text", text=f"Phase debug failed: {str(e)}")]
    
    async def _tool_run_regression(self, args: Dict[str, Any]) -> List[TextContent]:
        """Run regression test suite"""
        if not self.test_runner:
            return [TextContent(type="text", text="Test runner not available")]
        
        test_list = args.get("test_list", ["uart_axi4_register_verification_test"])
        seed_count = args.get("seed_count", 3)
        
        try:
            result_text = f"🏃 Running Regression: {len(test_list)} tests × {seed_count} seeds\n"
            result_text += "=" * 60 + "\n"
            
            # Generate seed range
            base_seed = 12345
            seed_range = range(base_seed, base_seed + seed_count)
            
            # Execute regression
            results = self.test_runner.run_regression(test_list, seed_range)
            
            # Analyze results
            total_tests = len(results)
            passed_tests = sum(1 for r in results if r.success)
            failed_tests = total_tests - passed_tests
            
            result_text += f"📊 Regression Results:\n"
            result_text += f"Total Tests: {total_tests}\n"
            result_text += f"Passed: {passed_tests} ({passed_tests/total_tests*100:.1f}%)\n"
            result_text += f"Failed: {failed_tests} ({failed_tests/total_tests*100:.1f}%)\n\n"
            
            if failed_tests > 0:
                result_text += "❌ Failed Tests:\n"
                for result in results:
                    if not result.success:
                        result_text += f"  - {result.test_name} (seed={result.seed})\n"
            
            return [TextContent(type="text", text=result_text)]
            
        except Exception as e:
            return [TextContent(type="text", text=f"Regression execution failed: {str(e)}")]
    
    async def _tool_get_phase_guidance(self, args: Dict[str, Any]) -> List[TextContent]:
        """Get guidance for current verification phase"""
        guidance_text = "📚 AXIUART Verification Phase Guidance\n"
        guidance_text += "=" * 45 + "\n\n"
        
        guidance_text += "🎯 Phase 1: CRC Error Resolution\n"
        guidance_text += "Goal: Fix CRC calculation errors in Frame_Parser\n"
        guidance_text += "Key Files: rtl/Frame_Parser.sv\n"
        guidance_text += "Debug: Compare with Python CRC8 reference\n\n"
        
        guidance_text += "🎯 Phase 2: AXI Alignment Error Resolution\n"
        guidance_text += "Goal: Fix address alignment checking\n"
        guidance_text += "Key Files: rtl/Address_Aligner.sv\n"
        guidance_text += "Debug: Verify 32-bit boundary logic\n\n"
        
        guidance_text += "🎯 Phase 3: Register Access Verification\n"
        guidance_text += "Goal: Ensure register read/write operations work\n"
        guidance_text += "Key Files: rtl/Register_Block.sv\n"
        guidance_text += "Debug: Test data persistence\n\n"
        
        guidance_text += "🎯 Phase 4: Coverage Improvement\n"
        guidance_text += "Goal: Achieve ≥60% toggle coverage\n"
        guidance_text += "Focus: Expand test scenarios\n\n"
        
        guidance_text += "💡 Current Tools Available:\n"
        guidance_text += "- check_environment: Validate setup\n"
        guidance_text += "- run_uvm_test: Execute single test\n"
        guidance_text += "- analyze_logs: Find specific errors\n"
        guidance_text += "- debug_phase_issues: Get targeted guidance\n"
        guidance_text += "- run_regression: Multi-test validation\n"
        
        return [TextContent(type="text", text=guidance_text)]
    
    # Helper methods
    def _get_project_structure(self) -> Dict[str, Any]:
        """Get current project structure"""
        structure = {
            "project_root": str(self.project_root),
            "directories": {},
            "key_files": {}
        }
        
        # Check key directories
        key_dirs = ["rtl", "sim", "docs", "tools", "scripts"]
        for dir_name in key_dirs:
            dir_path = self.project_root / dir_name
            structure["directories"][dir_name] = {
                "exists": dir_path.exists(),
                "path": str(dir_path)
            }
        
        # Check key files
        key_files = [
            "rtl/AXIUART_Top.sv",
            "rtl/Frame_Parser.sv", 
            "rtl/Address_Aligner.sv",
            "rtl/Register_Block.sv",
            "sim/uvm/run_uvm.ps1"
        ]
        for file_path in key_files:
            full_path = self.project_root / file_path
            structure["key_files"][file_path] = {
                "exists": full_path.exists(),
                "path": str(full_path)
            }
        
        return structure
    
    def _get_coverage_report(self) -> Dict[str, Any]:
        """Get coverage analysis report"""
        coverage_data = {
            "timestamp": None,
            "toggle_coverage": 0.0,
            "expression_coverage": 0.0,
            "functional_coverage": 0.0,
            "metrics_db_path": None
        }
        
        # Check for metrics database
        metrics_path = self.project_root / "sim" / "uvm" / "metrics.db"
        if metrics_path.exists():
            coverage_data["metrics_db_path"] = str(metrics_path)
            coverage_data["timestamp"] = metrics_path.stat().st_mtime
            # TODO: Parse actual coverage from metrics.db
        
        return coverage_data
    
    async def _get_phase_status(self) -> Dict[str, Any]:
        """Get current verification phase status"""
        phase_status = {
            "current_phase": "unknown",
            "phase_description": "Analysis required",
            "next_actions": [],
            "completion_criteria": [],
            "estimated_completion": "unknown"
        }
        
        # Analyze latest log to determine phase
        log_path = self.project_root / "sim" / "uvm" / "dsim.log"
        if log_path.exists() and self.log_analyzer:
            try:
                analysis = self.log_analyzer.analyze_log_file(str(log_path))
                
                if analysis.crc_errors:
                    phase_status.update({
                        "current_phase": "phase1",
                        "phase_description": "CRC Error Resolution Required",
                        "next_actions": [
                            "Review Frame_Parser.sv CRC implementation",
                            "Create Python CRC8 reference",
                            "Fix byte ordering issues"
                        ],
                        "completion_criteria": ["Zero CRC mismatch errors"],
                        "estimated_completion": "1-2 days"
                    })
                elif analysis.alignment_errors:
                    phase_status.update({
                        "current_phase": "phase2", 
                        "phase_description": "AXI Alignment Error Resolution Required",
                        "next_actions": [
                            "Debug Address_Aligner.sv logic",
                            "Fix 32-bit boundary checking",
                            "Validate register address range"
                        ],
                        "completion_criteria": ["Zero alignment errors"],
                        "estimated_completion": "1-2 days"
                    })
                elif analysis.uvm_errors:
                    phase_status.update({
                        "current_phase": "phase3",
                        "phase_description": "Register Access Verification Required", 
                        "next_actions": [
                            "Verify AXI transaction completion",
                            "Test register data persistence",
                            "Validate read/write operations"
                        ],
                        "completion_criteria": ["Zero UVM errors", "Successful register access"],
                        "estimated_completion": "1-2 days"
                    })
                else:
                    phase_status.update({
                        "current_phase": "phase4",
                        "phase_description": "Coverage Improvement Ready",
                        "next_actions": [
                            "Focus on toggle coverage improvement",
                            "Expand test scenarios",
                            "Target ≥60% coverage"
                        ],
                        "completion_criteria": ["≥60% toggle coverage"],
                        "estimated_completion": "1-2 weeks"
                    })
                    
            except Exception as e:
                logger.error(f"Phase analysis failed: {e}")
        
        return phase_status

async def main():
    """Main MCP server entry point"""
    server_instance = AXIUARTVerificationMCP()
    
    # Configure server options
    options = InitializationOptions(
        server_name="axiuart-verification",
        server_version="1.0.0",
        capabilities={
            "resources": True,
            "tools": True,
            "logging": True
        }
    )
    
    async with stdio_server() as (read_stream, write_stream):
        await server_instance.server.run(
            read_stream,
            write_stream,
            options
        )

if __name__ == "__main__":
    asyncio.run(main())