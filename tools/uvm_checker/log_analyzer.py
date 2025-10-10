#!/usr/bin/env python3
"""
Log Analysis Module for AXIUART UVM Verification
Analyzes DSIM log files for CRC errors, alignment errors, and UVM status
"""

import re
import json
from pathlib import Path
from typing import List, Dict, Optional
from datetime import datetime
from dataclasses import dataclass

@dataclass
class CRCError:
    """CRC error details"""
    line_number: int
    received_crc: str
    expected_crc: str
    context: str
    timestamp: Optional[str] = None

@dataclass
class AlignmentError:
    """AXI alignment error details"""
    line_number: int
    address: str
    error_type: str
    context: str
    timestamp: Optional[str] = None

@dataclass
class UVMError:
    """UVM error details"""
    line_number: int
    severity: str  # UVM_ERROR, UVM_FATAL, UVM_WARNING
    message: str
    component: str
    timestamp: Optional[str] = None

@dataclass
class LogAnalysisResult:
    """Complete log analysis result"""
    log_file: str
    analysis_timestamp: str
    total_lines: int
    crc_errors: List[CRCError]
    alignment_errors: List[AlignmentError]
    uvm_errors: List[UVMError]
    uvm_warnings: List[UVMError]
    compilation_errors: List[str]
    simulation_success: bool
    test_duration: Optional[float]

class DSIMLogAnalyzer:
    """Analyzes DSIM UVM log files for verification errors"""
    
    def __init__(self, config_path: Optional[str] = None):
        """Initialize with configuration file"""
        if config_path is None:
            config_file = Path(__file__).parent / "config" / "dsim_config.json"
        else:
            config_file = Path(config_path)
            
        with open(str(config_file), 'r') as f:
            self.config = json.load(f)
        
        # Compile regex patterns for efficiency
        self.patterns = self._compile_patterns()
    
    def _compile_patterns(self) -> Dict[str, any]:
        """Compile regex patterns from configuration"""
        patterns = {}
        
        error_patterns = self.config["error_patterns"]
        
        # CRC error patterns
        patterns["crc_errors"] = [
            re.compile(pattern, re.IGNORECASE) 
            for pattern in error_patterns["crc_errors"]
        ]
        
        # Alignment error patterns
        patterns["alignment_errors"] = [
            re.compile(pattern, re.IGNORECASE)
            for pattern in error_patterns["alignment_errors"]
        ]
        
        # UVM error patterns
        patterns["uvm_errors"] = [
            re.compile(pattern, re.IGNORECASE)
            for pattern in error_patterns["uvm_errors"]
        ]
        
        # Compilation error patterns
        patterns["compilation_errors"] = [
            re.compile(pattern, re.IGNORECASE)
            for pattern in error_patterns["compilation_errors"]
        ]
        
        # Additional specific patterns
        patterns["crc_mismatch"] = re.compile(
            r"CRC mismatch.*recv=0x([0-9a-fA-F]+).*exp=0x([0-9a-fA-F]+)",
            re.IGNORECASE
        )
        
        patterns["timestamp"] = re.compile(
            r"@\s*(\d+)\s*([numpf]?s)",
            re.IGNORECASE
        )
        
        patterns["uvm_severity"] = re.compile(
            r"(UVM_ERROR|UVM_FATAL|UVM_WARNING|UVM_INFO)",
            re.IGNORECASE
        )
        
        patterns["test_finished"] = re.compile(
            r"Test\s+(PASSED|FAILED|passed|failed)",
            re.IGNORECASE
        )
        
        return patterns
    
    def analyze_log_file(self, log_path: str) -> LogAnalysisResult:
        """Analyze a single DSIM log file"""
        log_file = Path(log_path)
        
        if not log_file.exists():
            raise FileNotFoundError(f"Log file not found: {log_path}")
        
        print(f"📋 Analyzing log file: {log_file.name}")
        
        # Initialize result containers
        crc_errors: List[CRCError] = []
        alignment_errors: List[AlignmentError] = []
        uvm_errors: List[UVMError] = []
        uvm_warnings: List[UVMError] = []
        compilation_errors: List[str] = []
        
        simulation_success = False
        test_duration = None
        line_count = 0
        
        try:
            with open(log_file, 'r', encoding='utf-8', errors='replace') as f:
                for line_num, line in enumerate(f, 1):
                    line_count = line_num
                    line_stripped = line.strip()
                    
                    if not line_stripped:
                        continue
                    
                    # Check for CRC errors
                    crc_error = self._check_crc_errors(line_stripped, line_num)
                    if crc_error:
                        crc_errors.append(crc_error)
                    
                    # Check for alignment errors
                    alignment_error = self._check_alignment_errors(line_stripped, line_num)
                    if alignment_error:
                        alignment_errors.append(alignment_error)
                    
                    # Check for UVM errors/warnings
                    uvm_error = self._check_uvm_errors(line_stripped, line_num)
                    if uvm_error:
                        if uvm_error.severity in ["UVM_ERROR", "UVM_FATAL"]:
                            uvm_errors.append(uvm_error)
                        elif uvm_error.severity == "UVM_WARNING":
                            uvm_warnings.append(uvm_error)
                    
                    # Check for compilation errors
                    comp_error = self._check_compilation_errors(line_stripped)
                    if comp_error:
                        compilation_errors.append(line_stripped)
                    
                    # Check for test completion
                    if self.patterns["test_finished"].search(line_stripped):
                        match = self.patterns["test_finished"].search(line_stripped)
                        if match and match.group(1).upper() == "PASSED":
                            simulation_success = True
        
        except Exception as e:
            print(f"⚠️  Error reading log file: {e}")
        
        # Create analysis result
        result = LogAnalysisResult(
            log_file=str(log_file),
            analysis_timestamp=datetime.now().isoformat(),
            total_lines=line_count,
            crc_errors=crc_errors,
            alignment_errors=alignment_errors,
            uvm_errors=uvm_errors,
            uvm_warnings=uvm_warnings,
            compilation_errors=compilation_errors,
            simulation_success=simulation_success,
            test_duration=test_duration
        )
        
        self._print_analysis_summary(result)
        return result
    
    def _check_crc_errors(self, line: str, line_num: int) -> Optional[CRCError]:
        """Check line for CRC errors"""
        # Check for specific CRC mismatch pattern
        match = self.patterns["crc_mismatch"].search(line)
        if match:
            return CRCError(
                line_number=line_num,
                received_crc=match.group(1),
                expected_crc=match.group(2),
                context=line[:100],  # First 100 chars for context
                timestamp=self._extract_timestamp(line)
            )
        
        # Check for general CRC error patterns
        for pattern in self.patterns["crc_errors"]:
            if pattern.search(line):
                return CRCError(
                    line_number=line_num,
                    received_crc="unknown",
                    expected_crc="unknown",
                    context=line[:100],
                    timestamp=self._extract_timestamp(line)
                )
        
        return None
    
    def _check_alignment_errors(self, line: str, line_num: int) -> Optional[AlignmentError]:
        """Check line for AXI alignment errors"""
        for pattern in self.patterns["alignment_errors"]:
            if pattern.search(line):
                # Try to extract address information
                address_match = re.search(r"0x([0-9a-fA-F]+)", line)
                address = address_match.group(0) if address_match else "unknown"
                
                return AlignmentError(
                    line_number=line_num,
                    address=address,
                    error_type="CHECK_ALIGNMENT",
                    context=line[:100],
                    timestamp=self._extract_timestamp(line)
                )
        
        return None
    
    def _check_uvm_errors(self, line: str, line_num: int) -> Optional[UVMError]:
        """Check line for UVM errors/warnings"""
        severity_match = self.patterns["uvm_severity"].search(line)
        if severity_match:
            severity = severity_match.group(1).upper()
            
            # Extract component name (usually after @)
            component_match = re.search(r"@\s*\w+", line)
            component = component_match.group(0) if component_match else "unknown"
            
            return UVMError(
                line_number=line_num,
                severity=severity,
                message=line[:200],  # First 200 chars
                component=component,
                timestamp=self._extract_timestamp(line)
            )
        
        return None
    
    def _check_compilation_errors(self, line: str) -> bool:
        """Check line for compilation errors"""
        for pattern in self.patterns["compilation_errors"]:
            if pattern.search(line):
                return True
        return False
    
    def _extract_timestamp(self, line: str) -> Optional[str]:
        """Extract timestamp from log line"""
        match = self.patterns["timestamp"].search(line)
        return match.group(0) if match else None
    
    def _print_analysis_summary(self, result: LogAnalysisResult) -> None:
        """Print comprehensive analysis summary"""
        print("\n" + "=" * 60)
        print("📊 LOG ANALYSIS SUMMARY")
        print("=" * 60)
        print(f"File: {Path(result.log_file).name}")
        print(f"Lines: {result.total_lines}")
        print(f"Analysis Time: {result.analysis_timestamp}")
        print()
        
        # Error counts
        print("🔍 Error Analysis:")
        print(f"   CRC Errors: {len(result.crc_errors)}")
        print(f"   Alignment Errors: {len(result.alignment_errors)}")
        print(f"   UVM Errors: {len(result.uvm_errors)}")
        print(f"   UVM Warnings: {len(result.uvm_warnings)}")
        print(f"   Compilation Errors: {len(result.compilation_errors)}")
        print()
        
        # Simulation status
        status = "✅ PASSED" if result.simulation_success else "❌ FAILED"
        print(f"📈 Simulation Status: {status}")
        
        # Detailed error information
        if result.crc_errors:
            print("\n🔴 CRC Errors:")
            for i, error in enumerate(result.crc_errors[:5], 1):  # Show first 5
                print(f"   {i}. Line {error.line_number}: recv=0x{error.received_crc} exp=0x{error.expected_crc}")
            if len(result.crc_errors) > 5:
                print(f"   ... and {len(result.crc_errors) - 5} more")
        
        if result.alignment_errors:
            print("\n🔴 Alignment Errors:")
            for i, error in enumerate(result.alignment_errors[:3], 1):  # Show first 3
                print(f"   {i}. Line {error.line_number}: {error.error_type} at {error.address}")
            if len(result.alignment_errors) > 3:
                print(f"   ... and {len(result.alignment_errors) - 3} more")
        
        if result.uvm_errors:
            print("\n🔴 UVM Errors:")
            for i, error in enumerate(result.uvm_errors[:3], 1):  # Show first 3
                print(f"   {i}. Line {error.line_number}: {error.severity} - {error.message[:50]}...")
            if len(result.uvm_errors) > 3:
                print(f"   ... and {len(result.uvm_errors) - 3} more")
        
        print("=" * 60)
    
    def analyze_multiple_logs(self, log_paths: List[str]) -> List[LogAnalysisResult]:
        """Analyze multiple log files"""
        results = []
        
        print(f"📋 Analyzing {len(log_paths)} log files...")
        
        for i, log_path in enumerate(log_paths, 1):
            print(f"\n[{i}/{len(log_paths)}]", end=" ")
            try:
                result = self.analyze_log_file(log_path)
                results.append(result)
            except Exception as e:
                print(f"❌ Failed to analyze {log_path}: {e}")
        
        self._print_batch_summary(results)
        return results
    
    def _print_batch_summary(self, results: List[LogAnalysisResult]) -> None:
        """Print summary for multiple log analyses"""
        if not results:
            return
        
        total_crc = sum(len(r.crc_errors) for r in results)
        total_alignment = sum(len(r.alignment_errors) for r in results)
        total_uvm_errors = sum(len(r.uvm_errors) for r in results)
        total_passed = sum(1 for r in results if r.simulation_success)
        
        print("\n" + "=" * 60)
        print("📊 BATCH ANALYSIS SUMMARY")
        print("=" * 60)
        print(f"Total Files: {len(results)}")
        print(f"Passed: {total_passed} ({total_passed/len(results)*100:.1f}%)")
        print(f"Failed: {len(results) - total_passed}")
        print()
        print(f"Total CRC Errors: {total_crc}")
        print(f"Total Alignment Errors: {total_alignment}")
        print(f"Total UVM Errors: {total_uvm_errors}")
        print("=" * 60)
    
    def save_analysis_results(self, results: List[LogAnalysisResult], output_path: Optional[str] = None) -> str:
        """Save analysis results to JSON file"""
        if output_path is None:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            output_path = f"log_analysis_{timestamp}.json"
        
        # Convert dataclasses to dictionaries for JSON serialization
        serializable_results = []
        for result in results:
            result_dict = {
                "log_file": result.log_file,
                "analysis_timestamp": result.analysis_timestamp,
                "total_lines": result.total_lines,
                "simulation_success": result.simulation_success,
                "test_duration": result.test_duration,
                "crc_errors": [
                    {
                        "line_number": err.line_number,
                        "received_crc": err.received_crc,
                        "expected_crc": err.expected_crc,
                        "context": err.context,
                        "timestamp": err.timestamp
                    }
                    for err in result.crc_errors
                ],
                "alignment_errors": [
                    {
                        "line_number": err.line_number,
                        "address": err.address,
                        "error_type": err.error_type,
                        "context": err.context,
                        "timestamp": err.timestamp
                    }
                    for err in result.alignment_errors
                ],
                "uvm_errors": [
                    {
                        "line_number": err.line_number,
                        "severity": err.severity,
                        "message": err.message,
                        "component": err.component,
                        "timestamp": err.timestamp
                    }
                    for err in result.uvm_errors
                ],
                "uvm_warnings": [
                    {
                        "line_number": err.line_number,
                        "severity": err.severity,
                        "message": err.message,
                        "component": err.component,
                        "timestamp": err.timestamp
                    }
                    for err in result.uvm_warnings
                ],
                "compilation_errors": result.compilation_errors
            }
            serializable_results.append(result_dict)
        
        analysis_data = {
            "analysis_timestamp": datetime.now().isoformat(),
            "total_files": len(results),
            "results": serializable_results
        }
        
        with open(output_path, 'w') as f:
            json.dump(analysis_data, f, indent=2)
        
        print(f"📁 Analysis results saved to: {output_path}")
        return output_path

def main():
    """Main execution function for standalone testing"""
    try:
        analyzer = DSIMLogAnalyzer()
        
        # Analyze current log file
        current_log = Path.cwd() / "dsim.log"
        if current_log.exists():
            result = analyzer.analyze_log_file(str(current_log))
            analyzer.save_analysis_results([result])
            return 0 if result.simulation_success else 1
        else:
            print("❌ No dsim.log file found in current directory")
            return 1
            
    except Exception as e:
        print(f"❌ Log analysis failed: {e}")
        return 1

if __name__ == "__main__":
    exit(main())