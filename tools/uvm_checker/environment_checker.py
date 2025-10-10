#!/usr/bin/env python3
"""
UVM Environment Checker for AXIUART SystemVerilog Verification
Validates DSIM environment, project structure, and execution readiness
"""

import os
import json
import sys
import subprocess
import re
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Any
from datetime import datetime

class DSIMEnvironmentChecker:
    """Validates DSIM UVM execution environment"""
    
    def __init__(self, config_path: Optional[str] = None):
        """Initialize with configuration file"""
        if config_path is None:
            config_file = Path(__file__).parent / "config" / "dsim_config.json"
        else:
            config_file = Path(config_path)
        
        with open(str(config_file), 'r') as f:
            self.config = json.load(f)
        
        self.project_root = self._find_project_root()
        self.validation_results = {}
    
    def _find_project_root(self) -> Path:
        """Find AXIUART project root directory"""
        current = Path(__file__).parent
        while current != current.parent:
            if (current / "rtl" / "AXIUART_Top.sv").exists():
                return current
            current = current.parent
        raise FileNotFoundError("AXIUART project root not found")
    
    def check_environment_variables(self) -> Dict[str, Optional[bool]]:
        """Validate required DSIM environment variables"""
        results: Dict[str, Optional[bool]] = {}
        
        # Check required variables
        for var in self.config["dsim_environment"]["required_vars"]:
            value = os.environ.get(var)
            if value and Path(value).exists():
                results[var] = True
            else:
                results[var] = False
                print(f"❌ {var}: {'Not set' if not value else 'Path does not exist'}")
        
        # Check optional variables
        for var in self.config["dsim_environment"]["optional_vars"]:
            value = os.environ.get(var)
            if value:
                results[var] = Path(value).exists() if Path(value).is_file() else True
            else:
                results[var] = None  # Optional, not set
        
        return results
    
    def check_executable_paths(self) -> Dict[str, bool]:
        """Verify DSIM executables are accessible"""
        results: Dict[str, bool] = {}
        dsim_home = os.environ.get("DSIM_HOME", "")
        
        for exe_name, exe_path_template in self.config["dsim_environment"]["executable_paths"].items():
            exe_path = exe_path_template.format(DSIM_HOME=dsim_home)
            results[exe_name] = Path(exe_path).exists()
            
            if not results[exe_name]:
                print(f"❌ {exe_name}: Executable not found at {exe_path}")
        
        return results
    
    def check_project_structure(self) -> Dict[str, bool]:
        """Validate AXIUART project directory structure"""
        results: Dict[str, bool] = {}
        
        for dir_name, relative_path in self.config["project_structure"].items():
            full_path = self.project_root / relative_path
            results[dir_name] = full_path.exists()
            
            if not results[dir_name]:
                print(f"❌ {dir_name}: Directory not found at {full_path}")
        
        return results
    
    def check_systemverilog_files(self) -> Dict[str, List[str]]:
        """Validate SystemVerilog file compliance"""
        results: Dict[str, List[str]] = {"timescale_violations": [], "naming_violations": []}
        
        rtl_dir = self.project_root / self.config["project_structure"]["rtl_dir"]
        sim_dir = self.project_root / self.config["project_structure"]["sim_dir"]
        
        # Check timescale in RTL files
        for sv_file in rtl_dir.glob("*.sv"):
            if not self._check_timescale(sv_file):
                results["timescale_violations"].append(str(sv_file))
        
        # Check timescale in UVM files
        for sv_file in sim_dir.rglob("*.sv"):
            if not self._check_timescale(sv_file):
                results["timescale_violations"].append(str(sv_file))
        
        return results
    
    def _check_timescale(self, file_path: Path) -> bool:
        """Check if file contains required timescale"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read(500)  # Check first 500 characters
                return self.config["validation_rules"]["timescale_required"] in content
        except UnicodeDecodeError:
            return True  # Skip binary files
        except Exception:
            return False
    
    def check_powershell_script(self) -> bool:
        """Verify PowerShell test runner exists and is executable"""
        script_path = (self.project_root / 
                      self.config["project_structure"]["scripts_dir"] / 
                      self.config["test_execution"]["powershell_script"])
        
        exists = script_path.exists()
        if not exists:
            print(f"❌ PowerShell script not found: {script_path}")
        
        return exists
    
    def run_environment_test(self) -> bool:
        """Execute a minimal DSIM test to verify environment"""
        try:
            dsim_exe = Path(os.environ.get("DSIM_HOME", "")) / "bin" / "dsim.exe"
            result = subprocess.run(
                [str(dsim_exe), "--version"],
                capture_output=True,
                text=True,
                timeout=10
            )
            
            if result.returncode == 0:
                print(f"✅ DSIM version check passed: {result.stdout.strip()}")
                return True
            else:
                print(f"❌ DSIM version check failed: {result.stderr}")
                return False
                
        except Exception as e:
            print(f"❌ DSIM execution test failed: {e}")
            return False
    
    def generate_environment_report(self) -> Dict[str, Any]:
        """Generate comprehensive environment validation report"""
        print("🔍 AXIUART UVM Environment Validation Report")
        print("=" * 50)
        print(f"Timestamp: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        print(f"Project Root: {self.project_root}")
        print()
        
        report: Dict[str, Any] = {
            "timestamp": datetime.now().isoformat(),
            "project_root": str(self.project_root),
            "environment_variables": self.check_environment_variables(),
            "executable_paths": self.check_executable_paths(),
            "project_structure": self.check_project_structure(),
            "systemverilog_compliance": self.check_systemverilog_files(),
            "powershell_script": self.check_powershell_script(),
            "dsim_execution": self.run_environment_test()
        }
        
        # Calculate overall status
        env_ok = all(report["environment_variables"].values())
        exe_ok = all(report["executable_paths"].values())
        struct_ok = all(report["project_structure"].values())
        sv_ok = len(report["systemverilog_compliance"]["timescale_violations"]) == 0
        
        report["overall_status"] = env_ok and exe_ok and struct_ok and sv_ok and report["powershell_script"] and report["dsim_execution"]
        
        print("\n📊 Summary:")
        print(f"Environment Variables: {'✅' if env_ok else '❌'}")
        print(f"Executable Paths: {'✅' if exe_ok else '❌'}")
        print(f"Project Structure: {'✅' if struct_ok else '❌'}")
        print(f"SystemVerilog Compliance: {'✅' if sv_ok else '❌'}")
        print(f"PowerShell Script: {'✅' if report['powershell_script'] else '❌'}")
        print(f"DSIM Execution: {'✅' if report['dsim_execution'] else '❌'}")
        print(f"\nOverall Status: {'✅ READY' if report['overall_status'] else '❌ ISSUES FOUND'}")
        
        return report

def main():
    """Main execution function"""
    try:
        checker = DSIMEnvironmentChecker()
        report = checker.generate_environment_report()
        
        # Save report to file
        report_path = checker.project_root / "tools" / "uvm_checker" / "environment_report.json"
        report_path.parent.mkdir(parents=True, exist_ok=True)
        
        with open(report_path, 'w') as f:
            json.dump(report, f, indent=2)
        
        print(f"\n📁 Report saved to: {report_path}")
        
        # Exit with appropriate code
        sys.exit(0 if report["overall_status"] else 1)
        
    except Exception as e:
        print(f"❌ Environment check failed: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()