# UART-AXI4 Bridge - Quick Start Guide

## Overview

This guide provides step-by-step instructions to quickly set up and run the UART-AXI4 Bridge verification environment. Follow these instructions to get your test environment operational within 30 minutes.

## Prerequisites

### Required Software
- **DSIM Simulator** (version 20240422.0.0 or later)
- **PowerShell** (version 5.1 or later)
- **Windows 10/11** or compatible OS
- **Git** for source code management (optional)

### Hardware Requirements
- **RAM**: 8GB minimum, 16GB recommended
- **CPU**: Multi-core processor (4+ cores recommended)
- **Storage**: 2GB free space for simulation files
- **Network**: Access for license server (if required)

## Quick Setup (5 Minutes)

### Step 1: Environment Variables

Set the required DSIM environment variables. Open PowerShell as Administrator and run:

```powershell
# Set DSIM environment variables (adjust path as needed)
[Environment]::SetEnvironmentVariable("DSIM_HOME", "C:\Users\Nautilus\AppData\Local\metrics-ca\dsim\20240422.0.0", "Machine")
[Environment]::SetEnvironmentVariable("DSIM_ROOT", $env:DSIM_HOME, "Machine")

# Verify settings
Write-Host "DSIM_HOME = $env:DSIM_HOME"
Write-Host "DSIM_ROOT = $env:DSIM_ROOT"
```

### Step 2: Navigate to Project Directory

```powershell
cd "E:\Nautilus\workspace\fpgawork\AXIUART_"
```

### Step 3: Quick Environment Test

```powershell
# Test DSIM installation
& "$env:DSIM_HOME\bin\dsim.exe" -version
```

If this returns version information, your DSIM environment is ready!

## Running Your First Test (2 Minutes)

### Basic Functional Test

Navigate to the simulation directory and run the basic test:

```powershell
cd sim\uvm
.\run_uvm.ps1 -TestName uart_axi4_basic_test -Waves
```

This command will:
- Compile all RTL and verification code
- Run the basic functional test
- Generate waveforms for debugging
- Display results summary

### Expected Output

You should see output similar to:

```text
[09:15:23.456][INFO] === UART-AXI4 Bridge UVM Test Runner ===
[09:15:23.457][INFO] Test: uart_axi4_basic_test
[09:15:23.458][INFO] Seed: 1
[09:15:23.459][INFO] Verbosity: UVM_MEDIUM
[09:15:23.460][SUCCESS] DSIM environment check passed
[09:15:23.461][INFO] Starting DSIM simulation...
...
[09:15:45.123][SUCCESS] *** TEST PASSED ***
```

## Available Test Options

### Test Selection

Run different test types using the `-TestName` parameter:

```powershell
# Basic functionality test
.\run_uvm.ps1 -TestName uart_axi4_basic_test

# Error handling test  
.\run_uvm.ps1 -TestName uart_axi4_error_paths_test

# Performance and stress test
.\run_uvm.ps1 -TestName uart_axi4_burst_perf_test
```

### Common Command-Line Options

| Option | Description | Example |
|--------|-------------|---------|
| `-TestName` | Specify which test to run | `-TestName uart_axi4_basic_test` |
| `-Seed` | Set random seed for reproducibility | `-Seed 42` |
| `-Verbosity` | Control message verbosity | `-Verbosity UVM_HIGH` |
| `-Waves` | Enable waveform generation | `-Waves` |
| `-Coverage` | Enable coverage collection | `-Coverage` |
| `-CleanFirst` | Clean previous artifacts | `-CleanFirst` |

### Example Commands

```powershell
# Run with custom seed and high verbosity
.\run_uvm.ps1 -TestName uart_axi4_basic_test -Seed 123 -Verbosity UVM_HIGH

# Run with coverage and waves enabled
.\run_uvm.ps1 -TestName uart_axi4_basic_test -Coverage -Waves

# Run error test with cleanup
.\run_uvm.ps1 -TestName uart_axi4_error_paths_test -CleanFirst
```

## Understanding Results

### Test Pass Indicators

✅ **Success Indicators:**
- `*** TEST PASSED ***` message
- `UVM_ERROR: 0` count
- `UVM_FATAL: 0` count
- Successful waveform generation (if enabled)

### Test Failure Indicators  

❌ **Failure Indicators:**
- `*** TEST FAILED ***` message
- `UVM_ERROR: >0` count
- `UVM_FATAL: >0` count  
- Compilation errors

### Output Files

After running tests, you'll find these files:

| File | Purpose |
|------|---------|
| `*.log` | Detailed simulation logs |
| `*.mxd` | Waveform files (if `-Waves` used) |
| `coverage.db` | Coverage database (if `-Coverage` used) |
| `dsim.log` | DSIM simulator log |

## Viewing Waveforms

If you ran with `-Waves`, open the generated waveform file:

```powershell
# Open waveform viewer (adjust path as needed)
& "$env:DSIM_HOME\bin\viewwave.exe" uart_axi4_basic_test_*.mxd
```

### Key Signals to Observe

**UART Interface:**
- `tb.dut.uart_rx` - UART receive signal
- `tb.dut.uart_tx` - UART transmit signal

**AXI4-Lite Interface:**
- `tb.dut.m_axi_awaddr` - Write address
- `tb.dut.m_axi_wdata` - Write data
- `tb.dut.m_axi_araddr` - Read address  
- `tb.dut.m_axi_rdata` - Read data

**Internal Signals:**
- `tb.dut.frame_parser_inst` - Frame parsing logic
- `tb.dut.axi_master_inst` - AXI master controller

## Troubleshooting

### Common Issues and Solutions

#### Issue: "DSIM executable not found"

**Solution:**
```powershell
# Verify DSIM_HOME is set correctly
echo $env:DSIM_HOME

# Check if dsim.exe exists
Test-Path "$env:DSIM_HOME\bin\dsim.exe"

# If false, update DSIM_HOME to correct path
```

#### Issue: "Configuration file not found"

**Solution:**
```powershell
# Ensure you're in the correct directory
cd "E:\Nautilus\workspace\fpgawork\AXIUART_\sim\uvm"

# Verify dsim_config.f exists
Test-Path "dsim_config.f"
```

#### Issue: "Compilation errors"

**Solution:**
1. Check that all RTL files exist in `../../rtl/`
2. Verify all UVM files are present
3. Review error messages in `dsim.log`
4. Try cleaning first: `.\run_uvm.ps1 -CleanFirst`

#### Issue: "Test timeout"

**Solution:**
```powershell
# Increase timeout or check for deadlock
# Review waveforms to identify the issue
.\run_uvm.ps1 -TestName uart_axi4_basic_test -Waves -Verbosity UVM_HIGH
```

### Getting Help

**Log Files to Check:**
1. `dsim.log` - DSIM simulator messages
2. `[testname]_[timestamp].log` - Test-specific log
3. UVM messages in console output

**Debug Commands:**
```powershell
# Run with maximum verbosity
.\run_uvm.ps1 -TestName uart_axi4_basic_test -Verbosity UVM_FULL

# Generate detailed waveforms
.\run_uvm.ps1 -TestName uart_axi4_basic_test -Waves -Verbosity UVM_HIGH
```

## Advanced Usage

### Running Custom Test Sequences

You can create custom test sequences by modifying the sequence files in `sequences/` directory. After modification, rerun the test:

```powershell
.\run_uvm.ps1 -TestName uart_axi4_basic_test -CleanFirst
```

### Batch Testing

Run multiple tests in sequence:

```powershell
# Create batch script
$tests = @("uart_axi4_basic_test", "uart_axi4_error_paths_test", "uart_axi4_burst_perf_test")

foreach ($test in $tests) {
    Write-Host "Running $test..."
    .\run_uvm.ps1 -TestName $test -CleanFirst
    if ($LASTEXITCODE -ne 0) {
        Write-Error "Test $test failed!"
        break
    }
}
```

### Coverage Analysis

To run with coverage and analyze results:

```powershell
# Run test with coverage
.\run_uvm.ps1 -TestName uart_axi4_basic_test -Coverage

# Generate coverage report (if dcreport is available)
if (Test-Path "$env:DSIM_HOME\bin\dcreport.exe") {
    & "$env:DSIM_HOME\bin\dcreport.exe" coverage.db -out_dir coverage_report
}
```

## Performance Benchmarking

### Quick Performance Test

```powershell
# Run performance-focused test
.\run_uvm.ps1 -TestName uart_axi4_burst_perf_test -Verbosity UVM_LOW

# Look for performance metrics in output:
# - Throughput (Mbps)
# - Average latency (ns)
# - Transaction count
```

### Performance Optimization Tips

1. **Reduce Verbosity**: Use `UVM_LOW` for performance runs
2. **Disable Waves**: Don't use `-Waves` for performance testing  
3. **Clean Environment**: Use `-CleanFirst` to ensure clean state
4. **Multiple Seeds**: Run with different seeds to get average performance

## Next Steps

### After Successful Basic Test

1. **Run All Tests**: Execute the complete test suite
2. **Review Coverage**: Generate and analyze coverage reports
3. **Examine Waveforms**: Understand signal behavior
4. **Modify Tests**: Customize tests for specific scenarios

### Recommended Learning Path

1. **Start with**: `uart_axi4_basic_test`
2. **Progress to**: `uart_axi4_error_paths_test`  
3. **Advanced testing**: `uart_axi4_burst_perf_test`
4. **Custom sequences**: Modify existing sequences
5. **New tests**: Create application-specific tests

## Support Resources

### Documentation
- `docs/design_overview.md` - Complete design documentation
- `docs/uvm_testplan.md` - Detailed verification plan
- `docs/uart_axi4_protocol.md` - Protocol specification

### Code Examples
- `sequences/` - Example test sequences
- `tests/` - Test class implementations
- `env/` - Environment configuration examples

### Community Support
- Check project documentation for updates
- Review example implementations in reference projects
- Contact verification team for complex issues

---

## Summary

You should now be able to:
- ✅ Set up the DSIM environment
- ✅ Run basic verification tests  
- ✅ Generate and view waveforms
- ✅ Understand test results
- ✅ Troubleshoot common issues
- ✅ Run advanced test scenarios

**Time to first successful test**: ~10 minutes  
**Time to understand basics**: ~30 minutes

Happy testing! 🚀