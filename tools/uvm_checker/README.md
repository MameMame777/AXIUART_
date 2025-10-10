# AXIUART UVM Verification Tool

Python-based automation tool for AXIUART SystemVerilog UVM verification workflow. This tool integrates environment checking, test execution, and log analysis to streamline the Phase 1-3 debugging process.

## 🎯 Purpose

Automate the manual verification tasks outlined in `comprehensive_work_instructions_updated_20251007.md`:
- **Environment Validation**: Automatically check DSIM setup and project structure
- **Test Execution**: Streamline UVM test runs with PowerShell integration  
- **Log Analysis**: Automatically detect CRC errors, alignment errors, and UVM issues
- **Phase Tracking**: Assess current debug phase status and next steps

## 📁 Project Structure

```
tools/uvm_checker/
├── config/
│   └── dsim_config.json          # Configuration for DSIM paths and validation rules
├── environment_checker.py        # DSIM environment validation
├── test_runner.py                # UVM test execution wrapper
├── log_analyzer.py               # Log file analysis for errors
├── uvm_verification_tool.py      # Main integrated interface
└── README.md                     # This file
```

## 🚀 Quick Start

### 1. Environment Setup
Ensure DSIM environment variables are set:
```powershell
$env:DSIM_HOME = "C:\Users\Nautilus\AppData\Local\metrics-ca\dsim\20240422.0.0"
$env:DSIM_ROOT = $env:DSIM_HOME
$env:DSIM_LIB_PATH = "$env:DSIM_HOME\lib"
```

### 2. Environment Check
```bash
cd E:\Nautilus\workspace\fpgawork\AXIUART_\tools\uvm_checker
python uvm_verification_tool.py check
```

### 3. Run Single Test
```bash
# Run with default parameters
python uvm_verification_tool.py test

# Run with specific seed
python uvm_verification_tool.py test --seed 54321

# Run specific test
python uvm_verification_tool.py test --test-name uart_axi4_register_simple_sequence
```

### 4. Debug Current Issues (Phase 1-3)
```bash
python uvm_verification_tool.py debug
```

### 5. Run Regression
```bash
# Run with 3 seeds (default)
python uvm_verification_tool.py regression

# Run with 5 seeds
python uvm_verification_tool.py regression --seed-count 5
```

## 🔧 Individual Module Usage

### Environment Checker
```python
from environment_checker import DSIMEnvironmentChecker

checker = DSIMEnvironmentChecker()
report = checker.generate_environment_report()
print(f"Environment OK: {report['overall_status']}")
```

### Test Runner
```python
from test_runner import UVMTestRunner

runner = UVMTestRunner()
result = runner.run_test(
    test_name="uart_axi4_register_verification_test",
    seed=12345,
    verbosity="UVM_MEDIUM"
)
print(f"Test passed: {result.success}")
```

### Log Analyzer
```python
from log_analyzer import DSIMLogAnalyzer

analyzer = DSIMLogAnalyzer()
analysis = analyzer.analyze_log_file("sim/uvm/dsim.log")
print(f"CRC errors: {len(analysis.crc_errors)}")
print(f"Alignment errors: {len(analysis.alignment_errors)}")
```

## 📊 Phase Status Assessment

The tool automatically assesses current verification phase based on log analysis:

- **Phase 1**: CRC Error Resolution Required
- **Phase 2**: AXI Alignment Error Resolution Required  
- **Phase 3**: Register Access Verification Required
- **Phase 4**: Coverage Improvement Ready

## 🎛️ Configuration

Edit `config/dsim_config.json` to customize:

```json
{
  "dsim_environment": {
    "required_vars": ["DSIM_HOME", "DSIM_ROOT", "DSIM_LIB_PATH"],
    "optional_vars": ["DSIM_LICENSE"]
  },
  "test_execution": {
    "default_seed": 12345,
    "default_verbosity": "UVM_MEDIUM",
    "timeout_seconds": 300
  },
  "error_patterns": {
    "crc_errors": ["CRC mismatch.*recv=0x([0-9a-fA-F]+).*exp=0x([0-9a-fA-F]+)"],
    "alignment_errors": ["CHECK_ALIGNMENT -> ERROR"]
  }
}
```

## 📈 Output Files

The tool generates several output files:

- `environment_report.json` - Environment validation results
- `test_results_YYYYMMDD_HHMMSS.json` - Test execution results
- `log_analysis_YYYYMMDD_HHMMSS.json` - Log analysis results  
- `verification_results_YYYYMMDD_HHMMSS.json` - Combined results
- `regression_results_YYYYMMDD_HHMMSS.json` - Regression summary

## 🛠️ Troubleshooting

### Common Issues

1. **Environment Variables Not Set**
   ```
   ❌ DSIM_HOME: Not set
   ```
   **Solution**: Set required DSIM environment variables

2. **PowerShell Script Not Found**
   ```  
   ❌ PowerShell script not found: sim\uvm\run_uvm.ps1
   ```
   **Solution**: Ensure you're running from project root or script exists

3. **Log File Not Found**
   ```
   ❌ No dsim.log file found
   ```
   **Solution**: Run UVM test first to generate log file

4. **Timeout During Test Execution**
   ```
   ❌ Test timed out after 300s
   ```
   **Solution**: Increase timeout in configuration or check test issues

### Debug Mode

Use debug mode for systematic Phase 1-3 issue analysis:
```bash
python uvm_verification_tool.py debug
```

This mode:
- Validates environment setup
- Runs targeted test for current issues
- Provides specific guidance for CRC and alignment errors
- Suggests next debugging steps

## 🎯 Integration with Current Workflow

This tool integrates with the existing AXIUART verification workflow:

1. **Pre-flight Checks**: Replaces manual environment validation from Section 5.1
2. **Test Execution**: Automates Section 5.2 PowerShell runs with error handling
3. **Post-run Verification**: Automates Section 5.3 log analysis
4. **Phase Assessment**: Automatically determines current phase status per Section 4

## 🔄 Next Steps

After Phase 1-3 completion with this tool:
1. Use for Phase 4 coverage improvement automation
2. Extend for Phase 5 functional verification patterns
3. Add continuous integration support
4. Implement automated regression reporting

## 📝 Command Reference

```bash
# Full command syntax
python uvm_verification_tool.py <command> [options]

Commands:
  check                    Validate DSIM environment
  test                     Run single UVM test
  regression              Run multiple tests with seed sweep
  debug                   Debug current Phase 1-3 issues

Options:
  --test-name TEXT        Test name (default: uart_axi4_register_verification_test)
  --seed INTEGER          Seed for test execution
  --seed-count INTEGER    Number of seeds for regression (default: 3)
  --config PATH           Configuration file path
```

## 🎉 Success Criteria

Tool execution success is defined as:
- ✅ Environment validation passes
- ✅ UVM tests execute with `UVM_ERROR = 0`
- ✅ Log analysis correctly identifies error types
- ✅ Phase status accurately reflects current debugging needs
- ✅ Output files generated with complete information

---

**Last Updated**: October 9, 2025  
**Compatible with**: DSIM v20240422.0.0, SystemVerilog UVM 1.2, Windows PowerShell  
**Project**: AXIUART SystemVerilog UVM Verification