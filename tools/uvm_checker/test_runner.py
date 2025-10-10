#!/usr/bin/env python3
"""
UVM Test Execution Wrapper for AXIUART SystemVerilog Verification
Automates PowerShell run_uvm.ps1 execution with error handling and monitoring
"""

import os
import json
import subprocess
import time
from pathlib import Path
from typing import List, Optional, NamedTuple
from datetime import datetime

class TestResult(NamedTuple):
    """Test execution result structure"""
    test_name: str
    seed: int
    success: bool
    duration: float
    log_path: str
    waveform_path: str
    error_count: int
    warning_count: int
    coverage_path: Optional[str]

class UVMTestRunner:
    """Wrapper for DSIM UVM test execution via PowerShell"""
    
    def __init__(self, config_path: Optional[str] = None):
        """Initialize test runner with configuration"""
        if config_path is None:
            config_file = Path(__file__).parent / "config" / "dsim_config.json"
        else:
            config_file = Path(config_path)
            
        with open(str(config_file), 'r') as f:
            self.config = json.load(f)
        
        self.project_root = self._find_project_root()
        self.sim_dir = self.project_root / self.config["project_structure"]["sim_dir"]
        self.waveform_dir = self.project_root / self.config["project_structure"]["waveform_dir"]
        self.results_history: List[TestResult] = []
    
    def _find_project_root(self) -> Path:
        """Find AXIUART project root directory"""
        current = Path(__file__).parent
        while current != current.parent:
            if (current / "rtl" / "AXIUART_Top.sv").exists():
                return current
            current = current.parent
        raise FileNotFoundError("AXIUART project root not found")
    
    def _validate_environment(self) -> bool:
        """Quick environment validation before test execution"""
        required_vars = self.config["dsim_environment"]["required_vars"]
        for var in required_vars:
            if not os.environ.get(var):
                print(f"❌ Environment variable {var} not set")
                return False
        
        script_path = self.sim_dir / self.config["test_execution"]["powershell_script"]
        if not script_path.exists():
            print(f"❌ PowerShell script not found: {script_path}")
            return False
        
        return True
    
    def run_test(self, 
                 test_name: str = "uart_axi4_register_verification_test",
                 seed: Optional[int] = None,
                 verbosity: str = "UVM_MEDIUM",
                 mode: str = "run",
                 coverage: bool = True,
                 timeout: Optional[int] = None) -> TestResult:
        """Execute single UVM test with specified parameters"""
        
        if not self._validate_environment():
            raise RuntimeError("Environment validation failed")
        
        # Use default seed if not provided
        if seed is None:
            seed = self.config["test_execution"]["default_seed"]
        
        # Ensure seed is an integer
        actual_seed = int(seed)
        
        if timeout is None:
            timeout = self.config["test_execution"]["timeout_seconds"]
        
        # Prepare PowerShell command
        script_path = self.sim_dir / self.config["test_execution"]["powershell_script"]
        cmd_args = [
            "powershell.exe", 
            "-ExecutionPolicy", "Bypass",
            "-File", str(script_path),
            "-TestName", test_name,
            "-Mode", mode,
            "-Seed", str(actual_seed),
            "-Verbose", verbosity
        ]
        
        if coverage:
            cmd_args.extend(["-Coverage", "on"])
        
        # Always enable waveforms for debugging
        cmd_args.extend(["-Waves", "on"])
        
        print(f"🚀 Starting UVM test: {test_name}")
        print(f"   Seed: {actual_seed}, Verbosity: {verbosity}, Mode: {mode}")
        print(f"   Command: {' '.join(cmd_args)}")
        
        start_time = time.time()
        
        try:
            # Execute PowerShell script
            result = subprocess.run(
                cmd_args,
                cwd=str(self.sim_dir),
                capture_output=True,
                text=True,
                timeout=timeout,
                encoding='utf-8',
                errors='replace'
            )
            
            duration = time.time() - start_time
            
            # Analyze execution results
            success = result.returncode == 0
            log_path = str(self.sim_dir / "dsim.log")
            waveform_path = str(self.waveform_dir / f"{test_name}.mxd")
            coverage_path = str(self.sim_dir / "metrics.db") if coverage else None
            
            # Count errors and warnings from output
            error_count = self._count_pattern(result.stdout + result.stderr, "UVM_ERROR")
            warning_count = self._count_pattern(result.stdout + result.stderr, "UVM_WARNING")
            
            # Create test result
            test_result = TestResult(
                test_name=test_name,
                seed=actual_seed,
                success=success,
                duration=duration,
                log_path=log_path,
                waveform_path=waveform_path,
                error_count=error_count,
                warning_count=warning_count,
                coverage_path=coverage_path
            )
            
            self.results_history.append(test_result)
            
            # Print result summary
            status = "✅ PASSED" if success else "❌ FAILED"
            print(f"{status} {test_name} in {duration:.1f}s")
            print(f"   Errors: {error_count}, Warnings: {warning_count}")
            
            if not success:
                print(f"   Return code: {result.returncode}")
                if result.stderr:
                    print(f"   Error output: {result.stderr[:500]}")
            
            return test_result
            
        except subprocess.TimeoutExpired:
            duration = time.time() - start_time
            print(f"❌ Test {test_name} timed out after {timeout}s")
            
            return TestResult(
                test_name=test_name,
                seed=actual_seed,
                success=False,
                duration=duration,
                log_path="",
                waveform_path="",
                error_count=-1,
                warning_count=0,
                coverage_path=None
            )
            
        except Exception as e:
            duration = time.time() - start_time
            print(f"❌ Test {test_name} failed with exception: {e}")
            
            return TestResult(
                test_name=test_name,
                seed=actual_seed,
                success=False,
                duration=duration,
                log_path="",
                waveform_path="",
                error_count=-1,
                warning_count=0,
                coverage_path=None
            )
    
    def _count_pattern(self, text: str, pattern: str) -> int:
        """Count occurrences of pattern in text"""
        return text.upper().count(pattern.upper())
    
    def run_regression(self, 
                      test_list: List[str],
                      seed_range: Optional[range] = None,
                      parallel: bool = False) -> List[TestResult]:
        """Run multiple tests with optional seed sweeping"""
        
        if seed_range is None:
            seed_range = range(self.config["test_execution"]["default_seed"], 
                             self.config["test_execution"]["default_seed"] + 1)
        
        all_results = []
        total_tests = len(test_list) * len(seed_range)
        
        print(f"🏃 Starting regression with {total_tests} tests")
        
        for i, test_name in enumerate(test_list):
            for j, seed in enumerate(seed_range):
                print(f"\n[{i * len(seed_range) + j + 1}/{total_tests}]", end=" ")
                
                result = self.run_test(test_name=test_name, seed=seed)
                all_results.append(result)
                
                # Early exit on critical failures
                if result.error_count > 0:
                    print(f"⚠️  Critical errors detected in {test_name}, continuing...")
        
        self._print_regression_summary(all_results)
        return all_results
    
    def _print_regression_summary(self, results: List[TestResult]) -> None:
        """Print comprehensive regression summary"""
        total = len(results)
        passed = sum(1 for r in results if r.success)
        failed = total - passed
        total_errors = sum(r.error_count for r in results if r.error_count >= 0)
        total_warnings = sum(r.warning_count for r in results)
        avg_duration = sum(r.duration for r in results) / total if total > 0 else 0
        
        print("\n" + "=" * 60)
        print("📊 REGRESSION SUMMARY")
        print("=" * 60)
        print(f"Total Tests: {total}")
        print(f"Passed: {passed} ({passed/total*100:.1f}%)")
        print(f"Failed: {failed} ({failed/total*100:.1f}%)")
        print(f"Total Errors: {total_errors}")
        print(f"Total Warnings: {total_warnings}")
        print(f"Average Duration: {avg_duration:.1f}s")
        
        if failed > 0:
            print("\n❌ Failed Tests:")
            for result in results:
                if not result.success:
                    print(f"   {result.test_name} (seed={result.seed})")
        
        print("=" * 60)
    
    def compile_only(self) -> bool:
        """Run compilation check without execution"""
        print("🔧 Running compilation check...")
        
        result = self.run_test(
            test_name="compile_check",
            mode="compile",
            coverage=False
        )
        
        return result.success
    
    def get_latest_result(self) -> Optional[TestResult]:
        """Get most recent test result"""
        return self.results_history[-1] if self.results_history else None
    
    def save_results(self, output_path: Optional[str] = None) -> str:
        """Save test results to JSON file"""
        if output_path is None:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            output_path = str(self.project_root / "tools" / "uvm_checker" / f"test_results_{timestamp}.json")
        
        # Convert results to serializable format
        results_data = {
            "timestamp": datetime.now().isoformat(),
            "project_root": str(self.project_root),
            "total_tests": len(self.results_history),
            "results": [
                {
                    "test_name": r.test_name,
                    "seed": r.seed,
                    "success": r.success,
                    "duration": r.duration,
                    "log_path": r.log_path,
                    "waveform_path": r.waveform_path,
                    "error_count": r.error_count,
                    "warning_count": r.warning_count,
                    "coverage_path": r.coverage_path
                }
                for r in self.results_history
            ]
        }
        
        Path(output_path).parent.mkdir(parents=True, exist_ok=True)
        with open(output_path, 'w') as f:
            json.dump(results_data, f, indent=2)
        
        print(f"📁 Results saved to: {output_path}")
        return output_path

def main():
    """Main execution function for standalone testing"""
    try:
        runner = UVMTestRunner()
        
        # Run environment check first
        if not runner._validate_environment():
            print("❌ Environment validation failed")
            return 1
        
        # Run single test
        result = runner.run_test(
            test_name="uart_axi4_register_verification_test",
            seed=12345,
            verbosity="UVM_MEDIUM"
        )
        
        # Save results
        runner.save_results()
        
        return 0 if result.success else 1
        
    except Exception as e:
        print(f"❌ Test runner failed: {e}")
        return 1

if __name__ == "__main__":
    exit(main())