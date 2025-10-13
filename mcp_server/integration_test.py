#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
MCP Integration Test Suite
Comprehensive testing for Agent AI + MCP Server integration

Created: October 13, 2025
Purpose: Validate MCP best practices implementation and Agent AI optimization
"""

import asyncio
import json
import logging
import sys
import time
from pathlib import Path
from typing import Dict, List, Any
import subprocess

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
logger = logging.getLogger("mcp-integration-test")

class MCPIntegrationTestSuite:
    """Test suite for MCP Server + Agent AI integration"""
    
    def __init__(self, workspace_path: Path):
        self.workspace_path = workspace_path
        self.mcp_client_path = workspace_path / "mcp_server" / "mcp_client.py"
        self.test_results = []
        
    async def run_all_tests(self):
        """Execute comprehensive MCP integration tests"""
        
        logger.info("🚀 Starting MCP Integration Test Suite")
        logger.info("="*70)
        
        tests = [
            ("Environment Check", self.test_environment_check),
            ("Tool Discovery", self.test_tool_discovery), 
            ("Atomic Tool: Compile Design", self.test_compile_design),
            ("Atomic Tool: Run Simulation", self.test_run_simulation),
            ("Atomic Tool: Generate Waveforms", self.test_generate_waveforms),
            ("Atomic Tool: Collect Coverage", self.test_collect_coverage),
            ("Legacy Tool: Monolithic Simulation", self.test_legacy_simulation),
            ("Tool Chain Integration", self.test_tool_chain),
            ("Error Handling", self.test_error_handling),
            ("Performance Baseline", self.test_performance)
        ]
        
        for test_name, test_func in tests:
            logger.info(f"\n📋 Running Test: {test_name}")
            logger.info("-" * 50)
            
            start_time = time.time()
            try:
                result = await test_func()
                duration = time.time() - start_time
                
                self.test_results.append({
                    "test": test_name,
                    "status": "PASS" if result else "FAIL",
                    "duration": f"{duration:.2f}s",
                    "details": result if isinstance(result, dict) else {"success": result}
                })
                
                status = "✅ PASS" if result else "❌ FAIL"
                logger.info(f"{status} - {test_name} ({duration:.2f}s)")
                
            except Exception as e:
                duration = time.time() - start_time
                self.test_results.append({
                    "test": test_name,
                    "status": "ERROR",
                    "duration": f"{duration:.2f}s",
                    "error": str(e)
                })
                logger.error(f"❌ ERROR - {test_name}: {e}")
        
        await self.generate_test_report()
    
    async def run_mcp_client(self, tool: str, **kwargs) -> Dict[str, Any]:
        """Helper to run MCP client tool"""
        
        cmd = [
            sys.executable,
            str(self.mcp_client_path),
            "--workspace", str(self.workspace_path),
            "--tool", tool
        ]
        
        # Add tool-specific arguments
        for key, value in kwargs.items():
            cmd.extend([f"--{key.replace('_', '-')}", str(value)])
        
        try:
            logger.debug(f"Executing: {' '.join(cmd)}")
            
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=120,  # 2 minute timeout for tests
                cwd=self.workspace_path
            )
            
            return {
                "exit_code": result.returncode,
                "stdout": result.stdout,
                "stderr": result.stderr,
                "success": result.returncode == 0
            }
            
        except subprocess.TimeoutExpired:
            return {
                "exit_code": -1,
                "stdout": "",
                "stderr": "Timeout expired",
                "success": False
            }
        except Exception as e:
            return {
                "exit_code": -1,
                "stdout": "",
                "stderr": str(e),
                "success": False
            }
    
    async def test_environment_check(self) -> bool:
        """Test DSIM environment verification"""
        result = await self.run_mcp_client("check_dsim_environment")
        return result["success"] and "DSIM_HOME" in result["stdout"]
    
    async def test_tool_discovery(self) -> bool:
        """Test MCP tool discovery"""
        result = await self.run_mcp_client("list_available_tests")
        return result["success"] and "uart_axi4_basic_test" in result["stdout"]
    
    async def test_compile_design(self) -> bool:
        """Test atomic compile_design tool"""
        result = await self.run_mcp_client(
            "compile_design",
            test_name="uart_axi4_basic_test",
            verbosity="UVM_LOW",
            timeout=120
        )
        return result["success"] and "SUCCESS" in result["stdout"]
    
    async def test_run_simulation(self) -> bool:
        """Test atomic run_simulation tool"""
        result = await self.run_mcp_client(
            "run_simulation",
            test_name="uart_axi4_basic_test",
            verbosity="UVM_MEDIUM",
            timeout=300
        )
        return result["success"] and ("SUCCESS" in result["stdout"] or "TEST PASSED" in result["stdout"])
    
    async def test_generate_waveforms(self) -> bool:
        """Test atomic generate_waveforms tool"""
        result = await self.run_mcp_client(
            "generate_waveforms",
            test_name="uart_axi4_basic_test",
            format="mxd",
            depth="all"
        )
        return result["success"] and "Waveform Generation Settings" in result["stdout"]
    
    async def test_collect_coverage(self) -> bool:
        """Test atomic collect_coverage tool"""
        result = await self.run_mcp_client(
            "collect_coverage",
            test_name="uart_axi4_basic_test",
            coverage_types="line,branch,toggle"
        )
        return result["success"] and "Coverage Collection Settings" in result["stdout"]
    
    async def test_legacy_simulation(self) -> bool:
        """Test legacy monolithic run_uvm_simulation tool"""
        result = await self.run_mcp_client(
            "run_uvm_simulation",
            test_name="uart_axi4_basic_test",
            mode="compile",
            verbosity="UVM_LOW"
        )
        return result["success"]
    
    async def test_tool_chain(self) -> Dict[str, Any]:
        """Test tool chaining (compile → run → analyze)"""
        
        # Step 1: Compile
        compile_result = await self.run_mcp_client(
            "compile_design",
            test_name="uart_axi4_basic_test"
        )
        
        if not compile_result["success"]:
            return {"success": False, "step": "compile", "details": compile_result}
        
        # Step 2: Run
        run_result = await self.run_mcp_client(
            "run_simulation", 
            test_name="uart_axi4_basic_test"
        )
        
        if not run_result["success"]:
            return {"success": False, "step": "run", "details": run_result}
        
        # Step 3: Collect Coverage
        coverage_result = await self.run_mcp_client(
            "collect_coverage",
            test_name="uart_axi4_basic_test"
        )
        
        return {
            "success": coverage_result["success"],
            "steps_completed": 3,
            "chain_success": all([
                compile_result["success"],
                run_result["success"], 
                coverage_result["success"]
            ])
        }
    
    async def test_error_handling(self) -> bool:
        """Test error handling with invalid inputs"""
        result = await self.run_mcp_client(
            "run_simulation",
            test_name="invalid_test_name"
        )
        # Should fail gracefully, not crash
        return result["exit_code"] != 0 and "error" in result["stderr"].lower()
    
    async def test_performance(self) -> Dict[str, Any]:
        """Test performance baseline"""
        
        start_time = time.time()
        
        result = await self.run_mcp_client(
            "compile_design",
            test_name="uart_axi4_basic_test"
        )
        
        duration = time.time() - start_time
        
        return {
            "success": result["success"],
            "compile_time": f"{duration:.2f}s",
            "performance_acceptable": duration < 60.0  # Under 1 minute
        }
    
    async def generate_test_report(self):
        """Generate comprehensive test report"""
        
        logger.info("\n" + "="*70)
        logger.info("📊 MCP Integration Test Report")
        logger.info("="*70)
        
        passed = sum(1 for result in self.test_results if result["status"] == "PASS")
        failed = sum(1 for result in self.test_results if result["status"] == "FAIL")
        errors = sum(1 for result in self.test_results if result["status"] == "ERROR")
        total = len(self.test_results)
        
        logger.info(f"Total Tests: {total}")
        logger.info(f"✅ Passed: {passed}")
        logger.info(f"❌ Failed: {failed}")
        logger.info(f"🔥 Errors: {errors}")
        logger.info(f"📈 Success Rate: {(passed/total)*100:.1f}%")
        
        # Generate detailed report file
        report_file = self.workspace_path / "mcp_integration_test_report.json"
        with open(report_file, "w") as f:
            json.dump({
                "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
                "summary": {
                    "total": total,
                    "passed": passed,
                    "failed": failed,
                    "errors": errors,
                    "success_rate": (passed/total)*100
                },
                "results": self.test_results
            }, f, indent=2)
        
        logger.info(f"\n📄 Detailed report saved: {report_file}")
        
        # MCP Best Practices Compliance Assessment
        compliance_score = self.assess_mcp_compliance()
        logger.info(f"\n🎯 MCP Best Practices Compliance: {compliance_score:.1f}%")
        
        return passed == total
    
    def assess_mcp_compliance(self) -> float:
        """Assess MCP best practices compliance based on test results"""
        
        compliance_checks = {
            "Environment Check": 10,      # Basic MCP functionality
            "Tool Discovery": 10,         # Standard MCP protocol
            "Atomic Tool: Compile Design": 20,  # Atomic tool design
            "Atomic Tool: Run Simulation": 20,  # Atomic tool design
            "Tool Chain Integration": 25,      # Agent AI optimization
            "Error Handling": 15              # Robustness
        }
        
        total_score = 0
        max_score = sum(compliance_checks.values())
        
        for result in self.test_results:
            test_name = result["test"]
            if test_name in compliance_checks and result["status"] == "PASS":
                total_score += compliance_checks[test_name]
        
        return (total_score / max_score) * 100

async def main():
    """Main entry point for integration tests"""
    workspace_path = Path(".").resolve()
    
    test_suite = MCPIntegrationTestSuite(workspace_path)
    success = await test_suite.run_all_tests()
    
    if success:
        logger.info("\n🎉 All tests passed! MCP integration is ready for Agent AI.")
        sys.exit(0)
    else:
        logger.error("\n💥 Some tests failed. Please review and fix issues.")
        sys.exit(1)

if __name__ == "__main__":
    asyncio.run(main())