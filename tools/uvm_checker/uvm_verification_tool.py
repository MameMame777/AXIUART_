#!/usr/bin/env python3
"""
Integrated UVM Checker Tool for AXIUART SystemVerilog Verification
Main interface combining environment checking, test execution, and log analysis
"""

import sys
import argparse
from pathlib import Path
from typing import List, Optional
from datetime import datetime

# Import our modules
from environment_checker import DSIMEnvironmentChecker
from test_runner import UVMTestRunner
from log_analyzer import DSIMLogAnalyzer

class AXIUARTVerificationTool:
    """Integrated verification tool for AXIUART project"""
    
    def __init__(self, config_path: Optional[str] = None):
        """Initialize verification tool"""
        self.config_path = config_path
        self.env_checker = DSIMEnvironmentChecker(config_path)
        self.test_runner = UVMTestRunner(config_path)
        self.log_analyzer = DSIMLogAnalyzer(config_path)
    
    def check_environment(self) -> bool:
        """Run complete environment validation"""
        print("🔍 AXIUART Verification Environment Check")
        print("=" * 50)
        
        try:
            report = self.env_checker.generate_environment_report()
            return report["overall_status"]
        except Exception as e:
            print(f"❌ Environment check failed: {e}")
            return False
    
    def run_single_test(self, 
                       test_name: str = "uart_axi4_register_verification_test",
                       seed: Optional[int] = None,
                       analyze_logs: bool = True) -> bool:
        """Run single test with optional log analysis"""
        print(f"🚀 Running single UVM test: {test_name}")
        
        # Run test
        result = self.test_runner.run_test(
            test_name=test_name,
            seed=seed,
            verbosity="UVM_MEDIUM",
            coverage=True
        )
        
        # Analyze logs if requested
        if analyze_logs and Path(result.log_path).exists():
            print("\n📋 Analyzing test logs...")
            analysis = self.log_analyzer.analyze_log_file(result.log_path)
            
            # Save combined results
            self._save_combined_results(result, analysis)
        
        return result.success
    
    def run_regression(self, 
                      test_list: Optional[List[str]] = None,
                      seed_count: int = 3) -> bool:
        """Run regression with multiple tests and seeds"""
        if test_list is None:
            test_list = [
                "uart_axi4_register_verification_test",
                "uart_axi4_register_simple_sequence"
            ]
        
        print(f"🏃 Running regression with {len(test_list)} tests, {seed_count} seeds each")
        
        # Generate seed range
        base_seed = 12345
        seed_range = range(base_seed, base_seed + seed_count)
        
        # Run regression
        results = self.test_runner.run_regression(test_list, seed_range)
        
        # Analyze all log files
        log_paths = [r.log_path for r in results if Path(r.log_path).exists()]
        if log_paths:
            print("\n📋 Analyzing regression logs...")
            analyses = self.log_analyzer.analyze_multiple_logs(log_paths)
            
            # Save combined results
            self._save_regression_results(results, analyses)
        
        # Return success if all tests passed
        return all(r.success for r in results)
    
    def debug_current_issues(self) -> None:
        """Debug current Phase 1-3 issues (CRC and alignment errors)"""
        print("🔧 AXIUART Phase 1-3 Debug Mode")
        print("Analyzing current issues: CRC errors and AXI alignment")
        print("=" * 60)
        
        # Check environment first
        if not self.check_environment():
            print("❌ Environment issues detected. Fix before debugging.")
            return
        
        # Run targeted test for debugging
        print("\n🎯 Running targeted debug test...")
        result = self.run_single_test(
            test_name="uart_axi4_register_verification_test",
            seed=12345,
            analyze_logs=True
        )
        
        if not result:
            print("\n🔍 Debug Analysis:")
            print("   - Check CRC calculation in Frame_Parser.sv")
            print("   - Verify AXI alignment logic in Address_Aligner.sv")
            print("   - Review register access path in Register_Block.sv")
            print("   - Compare with Python reference implementations")
    
    def _save_combined_results(self, test_result, log_analysis) -> str:
        """Save combined test and analysis results"""
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        output_path = f"verification_results_{timestamp}.json"
        
        combined_data = {
            "timestamp": datetime.now().isoformat(),
            "test_result": {
                "test_name": test_result.test_name,
                "seed": test_result.seed,
                "success": test_result.success,
                "duration": test_result.duration,
                "error_count": test_result.error_count,
                "warning_count": test_result.warning_count
            },
            "log_analysis": {
                "crc_error_count": len(log_analysis.crc_errors),
                "alignment_error_count": len(log_analysis.alignment_errors),
                "uvm_error_count": len(log_analysis.uvm_errors),
                "simulation_success": log_analysis.simulation_success
            },
            "phase_status": self._assess_phase_status(log_analysis)
        }
        
        import json
        with open(output_path, 'w') as f:
            json.dump(combined_data, f, indent=2)
        
        print(f"📁 Combined results saved to: {output_path}")
        return output_path
    
    def _save_regression_results(self, test_results, log_analyses) -> str:
        """Save regression results"""
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        output_path = f"regression_results_{timestamp}.json"
        
        # Combine data
        regression_data = {
            "timestamp": datetime.now().isoformat(),
            "total_tests": len(test_results),
            "passed_tests": sum(1 for r in test_results if r.success),
            "failed_tests": sum(1 for r in test_results if not r.success),
            "total_crc_errors": sum(len(a.crc_errors) for a in log_analyses),
            "total_alignment_errors": sum(len(a.alignment_errors) for a in log_analyses),
            "total_uvm_errors": sum(len(a.uvm_errors) for a in log_analyses),
            "phase_assessment": self._assess_regression_phase_status(log_analyses)
        }
        
        import json
        with open(output_path, 'w') as f:
            json.dump(regression_data, f, indent=2)
        
        print(f"📁 Regression results saved to: {output_path}")
        return output_path
    
    def _assess_phase_status(self, analysis) -> str:
        """Assess current phase status based on analysis"""
        if len(analysis.crc_errors) > 0:
            return "Phase 1: CRC Error Resolution Required"
        elif len(analysis.alignment_errors) > 0:
            return "Phase 2: AXI Alignment Error Resolution Required"
        elif len(analysis.uvm_errors) > 0:
            return "Phase 3: Register Access Verification Required"
        elif analysis.simulation_success:
            return "Phase 4: Coverage Improvement Ready"
        else:
            return "Phase Unknown: Investigation Required"
    
    def _assess_regression_phase_status(self, analyses) -> str:
        """Assess phase status from regression results"""
        total_crc = sum(len(a.crc_errors) for a in analyses)
        total_alignment = sum(len(a.alignment_errors) for a in analyses)
        total_uvm = sum(len(a.uvm_errors) for a in analyses)
        
        if total_crc > 0:
            return f"Phase 1: {total_crc} CRC errors across regression"
        elif total_alignment > 0:
            return f"Phase 2: {total_alignment} alignment errors across regression"
        elif total_uvm > 0:
            return f"Phase 3: {total_uvm} UVM errors across regression"
        else:
            return "Phase 4: Ready for coverage improvement"

def main():
    """Main CLI interface"""
    parser = argparse.ArgumentParser(
        description="AXIUART SystemVerilog UVM Verification Tool",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python uvm_verification_tool.py check              # Environment check only
  python uvm_verification_tool.py test               # Run single test
  python uvm_verification_tool.py test --seed 54321  # Run with specific seed
  python uvm_verification_tool.py regression         # Run full regression
  python uvm_verification_tool.py debug              # Debug current issues
        """
    )
    
    parser.add_argument(
        "command",
        choices=["check", "test", "regression", "debug"],
        help="Command to execute"
    )
    
    parser.add_argument(
        "--test-name",
        default="uart_axi4_register_verification_test",
        help="Test name to run (default: uart_axi4_register_verification_test)"
    )
    
    parser.add_argument(
        "--seed",
        type=int,
        help="Seed for test execution (default: from config)"
    )
    
    parser.add_argument(
        "--seed-count",
        type=int,
        default=3,
        help="Number of seeds for regression (default: 3)"
    )
    
    parser.add_argument(
        "--config",
        help="Configuration file path (default: config/dsim_config.json)"
    )
    
    args = parser.parse_args()
    
    try:
        # Initialize verification tool
        tool = AXIUARTVerificationTool(args.config)
        
        # Execute command
        if args.command == "check":
            success = tool.check_environment()
            
        elif args.command == "test":
            success = tool.run_single_test(
                test_name=args.test_name,
                seed=args.seed
            )
            
        elif args.command == "regression":
            success = tool.run_regression(
                seed_count=args.seed_count
            )
            
        elif args.command == "debug":
            tool.debug_current_issues()
            success = True  # Debug mode doesn't fail
        
        else:
            print(f"❌ Unknown command: {args.command}")
            success = False
        
        # Exit with appropriate code
        sys.exit(0 if success else 1)
        
    except Exception as e:
        print(f"❌ Verification tool failed: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()