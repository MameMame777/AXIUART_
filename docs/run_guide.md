# UART-AXI4 Bridge - Run Guide

## Overview

This comprehensive guide provides detailed instructions for operating the UART-AXI4 Bridge verification environment. It covers everything from initial setup through advanced debugging and performance analysis.

## Table of Contents

1. [Environment Setup](#environment-setup)
2. [Test Execution](#test-execution)
3. [Result Analysis](#result-analysis)
4. [Debugging Guide](#debugging-guide)
5. [Performance Analysis](#performance-analysis)
6. [Coverage Analysis](#coverage-analysis)
7. [Advanced Usage](#advanced-usage)
8. [Best Practices](#best-practices)

## Environment Setup

### System Requirements

**Minimum Requirements:**
- **Operating System**: Windows 10/11, Linux (Ubuntu 18.04+)
- **RAM**: 8GB (16GB recommended for coverage runs)
- **CPU**: 4+ cores (8+ cores recommended)
- **Storage**: 5GB free space
- **Network**: License server access (if applicable)

**Software Dependencies:**
- **DSIM Simulator**: Version 20240422.0.0 or later
- **PowerShell**: Version 5.1+ (Windows) or PowerShell Core 7.0+ (Linux)
- **Text Editor**: VS Code, Vim, or preferred editor
- **Git**: Version control (recommended)

### Installation Steps

#### Step 1: DSIM Installation Verification

```powershell
# Check DSIM installation
$dsim_path = "$env:DSIM_HOME\bin\dsim.exe"
if (Test-Path $dsim_path) {
    Write-Host "DSIM found at: $dsim_path" -ForegroundColor Green
    & $dsim_path -version
} else {
    Write-Host "DSIM not found. Please verify installation." -ForegroundColor Red
}
```

#### Step 2: Environment Variables Configuration

```powershell
# Set persistent environment variables (run as Administrator)
[Environment]::SetEnvironmentVariable("DSIM_HOME", "C:\path\to\dsim", "Machine")
[Environment]::SetEnvironmentVariable("DSIM_ROOT", $env:DSIM_HOME, "Machine")

# For current session only
$env:DSIM_HOME = "C:\path\to\dsim"
$env:DSIM_ROOT = $env:DSIM_HOME

# Verify settings
Write-Host "Environment Variables:" -ForegroundColor Yellow
Write-Host "DSIM_HOME = $env:DSIM_HOME"
Write-Host "DSIM_ROOT = $env:DSIM_ROOT"
```

#### Step 3: Project Directory Setup

```powershell
# Navigate to project root
cd "E:\Nautilus\workspace\fpgawork\AXIUART_"

# Verify directory structure
$required_dirs = @("rtl", "sim\uvm", "docs")
foreach ($dir in $required_dirs) {
    if (Test-Path $dir) {
        Write-Host "✓ Found: $dir" -ForegroundColor Green
    } else {
        Write-Host "✗ Missing: $dir" -ForegroundColor Red
    }
}
```

#### Step 4: Verification Environment Test

```powershell
# Test compilation only
cd sim\uvm
.\run_uvm.ps1 -TestName uart_axi4_basic_test -CompileOnly

# If compilation succeeds, run quick test
if ($LASTEXITCODE -eq 0) {
    Write-Host "Compilation successful. Running quick test..." -ForegroundColor Green
    .\run_uvm.ps1 -TestName uart_axi4_basic_test -Verbosity UVM_LOW
}
```

## Test Execution

### Basic Test Execution

#### Single Test Run

```powershell
# Basic functional test
.\run_uvm.ps1 -TestName uart_axi4_basic_test

# With waveforms
.\run_uvm.ps1 -TestName uart_axi4_basic_test -Waves

# With coverage
.\run_uvm.ps1 -TestName uart_axi4_basic_test -Coverage

# Combined options
.\run_uvm.ps1 -TestName uart_axi4_basic_test -Waves -Coverage -Verbosity UVM_HIGH
```

#### Available Test Classes

| Test Name | Purpose | Duration | Description |
|-----------|---------|----------|-------------|
| `uart_axi4_basic_test` | Functional verification | ~5 min | Basic read/write operations |
| `uart_axi4_error_paths_test` | Error handling | ~10 min | CRC errors, timeouts, protocol violations |
| `uart_axi4_burst_perf_test` | Performance testing | ~15 min | Throughput, latency, stress testing |

#### Command Line Options Reference

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `-TestName` | String | `uart_axi4_basic_test` | Test class to execute |
| `-Seed` | Integer | `1` | Random seed for reproducibility |
| `-Verbosity` | String | `UVM_MEDIUM` | UVM message verbosity level |
| `-Waves` | Switch | `false` | Enable waveform generation |
| `-Coverage` | Switch | `false` | Enable coverage collection |
| `-CleanFirst` | Switch | `false` | Clean previous artifacts |
| `-LogFile` | String | Auto-generated | Custom log file name |

#### Verbosity Levels

| Level | Usage | Output Volume |
|-------|-------|---------------|
| `UVM_NONE` | Silent operation | Minimal output |
| `UVM_LOW` | Production runs | Errors and key info |
| `UVM_MEDIUM` | Standard testing | Moderate detail |
| `UVM_HIGH` | Debugging | Detailed information |
| `UVM_FULL` | Deep debugging | Maximum detail |

### Batch Test Execution

#### Sequential Test Execution

```powershell
# Define test suite
$test_suite = @(
    "uart_axi4_basic_test",
    "uart_axi4_error_paths_test",
    "uart_axi4_burst_perf_test"
)

# Run all tests
$results = @{}
foreach ($test in $test_suite) {
    Write-Host "`n=== Running $test ===" -ForegroundColor Cyan
    .\run_uvm.ps1 -TestName $test -CleanFirst
    $results[$test] = $LASTEXITCODE -eq 0
}

# Report results
Write-Host "`n=== Test Results ===" -ForegroundColor Yellow
foreach ($test in $results.Keys) {
    $status = if ($results[$test]) { "PASS" } else { "FAIL" }
    $color = if ($results[$test]) { "Green" } else { "Red" }
    Write-Host "$test : $status" -ForegroundColor $color
}
```

#### Parallel Test Execution

```powershell
# Run tests in parallel (requires multiple licenses)
$jobs = @()
$test_suite = @("uart_axi4_basic_test", "uart_axi4_error_paths_test")

foreach ($test in $test_suite) {
    $jobs += Start-Job -ScriptBlock {
        param($TestName, $WorkingDir)
        Set-Location $WorkingDir
        .\run_uvm.ps1 -TestName $TestName -CleanFirst
    } -ArgumentList $test, (Get-Location)
}

# Wait for completion and collect results
$jobs | Wait-Job | Receive-Job
$jobs | Remove-Job
```

### Regression Testing

#### Nightly Regression

```powershell
# Create regression script
$regression_tests = @{
    "smoke" = @("uart_axi4_basic_test")
    "functional" = @("uart_axi4_basic_test", "uart_axi4_error_paths_test")
    "full" = @("uart_axi4_basic_test", "uart_axi4_error_paths_test", "uart_axi4_burst_perf_test")
}

function Run-Regression {
    param([string]$Suite = "functional")
    
    $tests = $regression_tests[$Suite]
    $passed = 0
    $failed = 0
    
    foreach ($test in $tests) {
        Write-Host "Running $test..." -ForegroundColor Cyan
        .\run_uvm.ps1 -TestName $test -Seed (Get-Random) -CleanFirst
        if ($LASTEXITCODE -eq 0) {
            $passed++
        } else {
            $failed++
        }
    }
    
    Write-Host "`nRegression Results:" -ForegroundColor Yellow
    Write-Host "Passed: $passed" -ForegroundColor Green  
    Write-Host "Failed: $failed" -ForegroundColor Red
    
    return $failed -eq 0
}

# Run regression
Run-Regression -Suite "functional"
```

## Result Analysis

### Understanding Test Output

#### Success Indicators

```text
[INFO] === UART-AXI4 Bridge UVM Test Runner ===
[SUCCESS] DSIM environment check passed
[INFO] Starting DSIM simulation...
[SUCCESS] UVM_WARNING: 0
[SUCCESS] UVM_ERROR: 0  
[SUCCESS] UVM_FATAL: 0
[SUCCESS] *** TEST PASSED ***
```

#### Failure Indicators

```text
[ERROR] UVM_ERROR: 5
[ERROR] UVM_FATAL: 1
[ERROR] Compilation failed
[ERROR] *** TEST FAILED ***
```

### Log File Analysis

#### Primary Log Files

| File | Content | Usage |
|------|---------|-------|
| `dsim.log` | DSIM simulator output | Compilation and runtime errors |
| `[test]_[timestamp].log` | Test-specific messages | UVM messages and test flow |
| Console output | Real-time progress | Immediate feedback |

#### Log Analysis Commands

```powershell
# Search for errors in logs
Select-String -Path "*.log" -Pattern "ERROR|FATAL" -Context 2

# Count message types
$log_content = Get-Content "dsim.log" -Raw
$errors = ($log_content | Select-String "UVM_ERROR" -AllMatches).Matches.Count
$warnings = ($log_content | Select-String "UVM_WARNING" -AllMatches).Matches.Count
Write-Host "Errors: $errors, Warnings: $warnings"

# Find specific patterns
Select-String -Path "*.log" -Pattern "Transaction.*failed|Timeout|CRC.*error"
```

### Performance Metrics Analysis

#### Extracting Performance Data

```powershell
# Parse performance metrics from logs
function Get-PerformanceMetrics {
    param([string]$LogFile)
    
    $content = Get-Content $LogFile -Raw
    $metrics = @{}
    
    # Extract throughput
    if ($content -match "Throughput:\s*([\d.]+)\s*Mbps") {
        $metrics["Throughput_Mbps"] = [float]$Matches[1]
    }
    
    # Extract latency
    if ($content -match "Average latency:\s*([\d.]+)\s*ns") {
        $metrics["Avg_Latency_ns"] = [float]$Matches[1]
    }
    
    # Extract transaction count
    if ($content -match "Total Transactions:\s*(\d+)") {
        $metrics["Transaction_Count"] = [int]$Matches[1]
    }
    
    return $metrics
}

# Analyze recent test
$latest_log = Get-ChildItem "*.log" | Sort-Object LastWriteTime -Descending | Select-Object -First 1
$metrics = Get-PerformanceMetrics $latest_log.Name
$metrics
```

## Debugging Guide

### Common Issues and Solutions

#### Issue 1: Compilation Errors

**Symptoms:**
- Error messages during compilation phase
- "File not found" errors
- SystemVerilog syntax errors

**Debug Steps:**

```powershell
# Check file paths in config
Get-Content "dsim_config.f" | Where-Object { $_ -notmatch "^#" -and $_ -notmatch "^\+" -and $_ -ne "" } | ForEach-Object {
    if (-not (Test-Path $_)) {
        Write-Host "Missing: $_" -ForegroundColor Red
    }
}

# Verbose compilation
.\run_uvm.ps1 -TestName uart_axi4_basic_test -Verbosity UVM_HIGH -CompileOnly
```

#### Issue 2: Test Hangs/Timeouts

**Symptoms:**
- Test runs indefinitely
- No progress messages
- Timeout errors

**Debug Steps:**

```powershell
# Run with maximum verbosity and waves
.\run_uvm.ps1 -TestName uart_axi4_basic_test -Verbosity UVM_FULL -Waves

# Check for infinite loops in waveform
# Look for signals that stop toggling
```

#### Issue 3: UVM Errors

**Symptoms:**
- UVM_ERROR or UVM_FATAL messages
- Transaction mismatches
- Protocol violations

**Debug Steps:**

```powershell
# Enable UVM debugging
.\run_uvm.ps1 -TestName uart_axi4_basic_test -ExtraArgs "+UVM_CONFIG_DB_TRACE +UVM_OBJECTION_TRACE"

# Check scoreboard messages
Select-String -Path "*.log" -Pattern "SCOREBOARD|MISMATCH|COMPARE"
```

### Waveform Analysis

#### Launching Waveform Viewer

```powershell
# Generate waveforms
.\run_uvm.ps1 -TestName uart_axi4_basic_test -Waves

# Open in viewer (adjust path as needed)
& "$env:DSIM_HOME\bin\viewwave.exe" *.mxd
```

#### Key Signal Groups

**UART Protocol Signals:**
- `tb.uart_if_inst.uart_rx` - Receive data
- `tb.uart_if_inst.uart_tx` - Transmit data  
- `tb.dut.frame_parser_inst.state` - Parser state machine
- `tb.dut.frame_parser_inst.frame_complete` - Frame completion

**AXI4-Lite Signals:**
- `tb.axi_if_inst.awaddr` / `tb.axi_if_inst.awvalid` - Write address
- `tb.axi_if_inst.wdata` / `tb.axi_if_inst.wvalid` - Write data
- `tb.axi_if_inst.araddr` / `tb.axi_if_inst.arvalid` - Read address
- `tb.axi_if_inst.rdata` / `tb.axi_if_inst.rvalid` - Read data

**Internal State Machines:**
- `tb.dut.bridge_state` - Main bridge state
- `tb.dut.axi_master_inst.state` - AXI master state
- FIFO levels and status flags

### Advanced Debugging Techniques

#### Custom Assertions

Add temporary assertions for debugging:

```systemverilog
// In testbench
always @(posedge clk) begin
    if (rst_n) begin
        // Check for unexpected conditions
        assert (!(uart_tx_busy && fifo_empty)) 
        else $error("UART transmitting with empty FIFO");
        
        assert (!(axi_transaction_active && invalid_address))
        else $error("AXI transaction with invalid address");
    end
end
```

#### Runtime Diagnostics

```powershell
# Enable runtime diagnostics
.\run_uvm.ps1 -TestName uart_axi4_basic_test -ExtraDefines "DEBUG_ENABLED,VERBOSE_CHECKING"

# Monitor system resources during run
while (Get-Process dsim -ErrorAction SilentlyContinue) {
    $proc = Get-Process dsim
    Write-Host "Memory: $($proc.WorkingSet64/1MB) MB, CPU: $($proc.CPU)s"
    Start-Sleep 5
}
```

## Performance Analysis

### Throughput Measurement

#### Built-in Performance Tests

```powershell
# Run performance test with detailed metrics
.\run_uvm.ps1 -TestName uart_axi4_burst_perf_test -Verbosity UVM_LOW

# Extract key metrics
Select-String -Path "*.log" -Pattern "Throughput|Latency|Transaction.*complete"
```

#### Custom Performance Analysis

```powershell
# Performance test script
function Measure-TestPerformance {
    param([string]$TestName, [int]$Iterations = 5)
    
    $results = @()
    
    for ($i = 1; $i -le $Iterations; $i++) {
        Write-Host "Performance run $i/$Iterations"
        $start = Get-Date
        .\run_uvm.ps1 -TestName $TestName -Seed $i -Verbosity UVM_LOW
        $end = Get-Date
        
        $results += @{
            Run = $i
            Duration = ($end - $start).TotalSeconds
            Success = $LASTEXITCODE -eq 0
        }
    }
    
    # Calculate statistics
    $successful = $results | Where-Object { $_.Success }
    $avg_time = ($successful | Measure-Object Duration -Average).Average
    $min_time = ($successful | Measure-Object Duration -Minimum).Minimum  
    $max_time = ($successful | Measure-Object Duration -Maximum).Maximum
    
    Write-Host "`nPerformance Summary:" -ForegroundColor Yellow
    Write-Host "Average: $([math]::Round($avg_time, 2))s"
    Write-Host "Range: $([math]::Round($min_time, 2))s - $([math]::Round($max_time, 2))s"
    Write-Host "Success Rate: $($successful.Count)/$Iterations"
}

# Run performance analysis
Measure-TestPerformance -TestName "uart_axi4_basic_test" -Iterations 10
```

### Latency Analysis

#### Transaction Timing

Monitor individual transaction timing:

```powershell
# Enable detailed timing
.\run_uvm.ps1 -TestName uart_axi4_basic_test -ExtraDefines "TIMING_DEBUG" -Waves

# Analyze timing in waveform viewer
# Measure from UART frame start to AXI transaction completion
```

## Coverage Analysis

### Running with Coverage

```powershell
# Basic coverage run
.\run_uvm.ps1 -TestName uart_axi4_basic_test -Coverage

# Coverage with all test types
$tests = @("uart_axi4_basic_test", "uart_axi4_error_paths_test", "uart_axi4_burst_perf_test")
foreach ($test in $tests) {
    .\run_uvm.ps1 -TestName $test -Coverage
}
```

### Coverage Report Generation

```powershell
# Generate coverage report (if dcreport is available)
if (Test-Path "$env:DSIM_HOME\bin\dcreport.exe") {
    & "$env:DSIM_HOME\bin\dcreport.exe" coverage.db -out_dir coverage_report
    
    # Open coverage report
    if (Test-Path "coverage_report\index.html") {
        Start-Process "coverage_report\index.html"
    }
} else {
    Write-Host "dcreport not found - manual coverage analysis required"
}
```

### Coverage Analysis Scripts

```powershell
# Parse coverage from logs
function Get-CoverageMetrics {
    param([string]$LogFile)
    
    $content = Get-Content $LogFile -Raw
    $coverage = @{}
    
    # Extract functional coverage
    if ($content -match "Functional Coverage:\s*([\d.]+)%") {
        $coverage["Functional"] = [float]$Matches[1]
    }
    
    # Extract code coverage
    if ($content -match "Line Coverage:\s*([\d.]+)%") {
        $coverage["Line"] = [float]$Matches[1]
    }
    
    if ($content -match "Branch Coverage:\s*([\d.]+)%") {
        $coverage["Branch"] = [float]$Matches[1]
    }
    
    return $coverage
}

# Analyze coverage trends
$coverage_history = @()
Get-ChildItem "*coverage*.log" | ForEach-Object {
    $metrics = Get-CoverageMetrics $_.Name
    $metrics["Date"] = $_.LastWriteTime
    $coverage_history += $metrics
}

$coverage_history | Format-Table -AutoSize
```

## Advanced Usage

### Custom Test Development

#### Creating New Test Classes

1. **Copy base test template:**
```powershell
Copy-Item "tests\uart_axi4_base_test.sv" "tests\my_custom_test.sv"
```

2. **Modify test class:**
```systemverilog
class my_custom_test extends uart_axi4_base_test;
    `uvm_component_utils(my_custom_test)
    
    function new(string name = "my_custom_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        // Custom test implementation
    endtask
endclass
```

3. **Register in package:**
```systemverilog
// In uart_axi4_test_pkg.sv
`include "my_custom_test.sv"
```

#### Creating Custom Sequences

```systemverilog
class my_custom_sequence extends uvm_sequence #(uart_frame_transaction);
    `uvm_object_utils(my_custom_sequence)
    
    function new(string name = "my_custom_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction req;
        
        // Custom sequence logic
        `uvm_do_with(req, {
            // Custom constraints
        })
    endtask
endclass
```

### Environment Customization

#### Modifying Configuration

```powershell
# Create custom configuration
$custom_config = @"
# Custom DSIM configuration
-define+CUSTOM_FEATURE
-define+DEBUG_LEVEL=2
+define+EXTENDED_TIMEOUT
"@

$custom_config | Out-File "custom_config.f"

# Run with custom configuration
.\universal_uvm_runner.ps1 -ConfigFile "custom_config.f" -TestName "uart_axi4_basic_test"
```

#### Environment Variables

```powershell
# Set custom environment variables for test
$env:UART_BAUD_RATE = "921600"  # Higher baud rate
$env:AXI_TIMEOUT = "2000"       # Extended timeout
$env:DEBUG_LEVEL = "HIGH"       # Debug mode

# Run test with custom environment
.\run_uvm.ps1 -TestName uart_axi4_basic_test
```

### Automation and CI/CD Integration

#### Jenkins Integration

```groovy
pipeline {
    agent any
    stages {
        stage('Environment Setup') {
            steps {
                // Set up DSIM environment
                bat '''
                    set DSIM_HOME=C:\\tools\\dsim
                    set DSIM_ROOT=%DSIM_HOME%
                '''
            }
        }
        stage('Verification') {
            steps {
                dir('sim/uvm') {
                    bat '''
                        powershell -Command "& .\\run_uvm.ps1 -TestName uart_axi4_basic_test -Coverage"
                    '''
                }
            }
            post {
                always {
                    archiveArtifacts artifacts: '**/*.log, **/*.mxd, **/coverage_report/**'
                    publishHTML([
                        allowMissing: false,
                        alwaysLinkToLastBuild: true,
                        keepAll: true,
                        reportDir: 'coverage_report',
                        reportFiles: 'index.html',
                        reportName: 'Coverage Report'
                    ])
                }
            }
        }
    }
}
```

#### GitHub Actions Integration

```yaml
name: UART-AXI4 Verification
on: [push, pull_request]

jobs:
  verification:
    runs-on: windows-latest
    steps:
    - uses: actions/checkout@v2
    
    - name: Setup DSIM Environment
      run: |
        echo "DSIM_HOME=C:\tools\dsim" >> $GITHUB_ENV
        echo "DSIM_ROOT=C:\tools\dsim" >> $GITHUB_ENV
    
    - name: Run Verification
      run: |
        cd sim\uvm
        .\run_uvm.ps1 -TestName uart_axi4_basic_test -Coverage
      shell: pwsh
    
    - name: Upload Results
      uses: actions/upload-artifact@v2
      with:
        name: verification-results
        path: |
          **/*.log
          **/*.mxd
          coverage_report/
```

## Best Practices

### Development Workflow

1. **Start Small**: Begin with basic functional tests
2. **Incremental Development**: Add features gradually
3. **Version Control**: Commit changes frequently
4. **Documentation**: Update documentation with changes
5. **Review**: Peer review for complex modifications

### Test Organization

```text
Test Development Lifecycle:
1. Plan test scenario
2. Develop sequence
3. Create test class
4. Integrate with environment
5. Debug and validate
6. Document and review
```

### Performance Optimization

#### Simulation Performance

```powershell
# Optimize for speed
.\run_uvm.ps1 -TestName uart_axi4_basic_test `
    -Verbosity UVM_LOW `
    -ExtraArgs "-O2" `
    -ExtraDefines "FAST_SIM"

# Optimize for coverage
.\run_uvm.ps1 -TestName uart_axi4_basic_test `
    -Coverage `
    -ExtraArgs "-O1" `
    -Verbosity UVM_MEDIUM
```

#### Resource Management

```powershell
# Monitor resource usage
function Monitor-Simulation {
    $start_time = Get-Date
    $max_memory = 0
    
    while (Get-Process dsim -ErrorAction SilentlyContinue) {
        $proc = Get-Process dsim -ErrorAction SilentlyContinue
        if ($proc) {
            $memory_mb = $proc.WorkingSet64 / 1MB
            if ($memory_mb -gt $max_memory) { $max_memory = $memory_mb }
        }
        Start-Sleep 1
    }
    
    $duration = (Get-Date) - $start_time
    Write-Host "Peak Memory: $([math]::Round($max_memory, 1)) MB"
    Write-Host "Duration: $($duration.TotalSeconds) seconds"
}

# Run with monitoring
Start-Job -ScriptBlock { Monitor-Simulation }
.\run_uvm.ps1 -TestName uart_axi4_basic_test
```

### Quality Assurance

#### Regression Guidelines

- **Daily**: Smoke tests (basic functionality)
- **Weekly**: Full functional regression
- **Release**: Complete test suite with stress testing

#### Code Quality Checks

```powershell
# Check for common issues
function Check-CodeQuality {
    # Check for hardcoded values
    Select-String -Path "*.sv" -Pattern "\d+'" | Where-Object { $_ -notmatch "parameter|localparam" }
    
    # Check for TODO/FIXME comments
    Select-String -Path "*.sv" -Pattern "TODO|FIXME|XXX"
    
    # Check for proper headers
    Get-ChildItem "*.sv" | ForEach-Object {
        $content = Get-Content $_ -Head 5
        if ($content[0] -notmatch "timescale") {
            Write-Host "Missing timescale: $_" -ForegroundColor Yellow
        }
    }
}

Check-CodeQuality
```

### Maintenance and Updates

#### Regular Maintenance Tasks

1. **Clean Old Artifacts**: Remove old log files and waveforms
2. **Update Documentation**: Keep documentation current
3. **Review Performance**: Monitor performance trends
4. **Coverage Analysis**: Identify coverage gaps
5. **Tool Updates**: Update DSIM and scripts as needed

#### Troubleshooting Checklist

- [ ] Environment variables set correctly
- [ ] All required files present
- [ ] DSIM license valid
- [ ] Sufficient disk space
- [ ] No conflicting processes
- [ ] Latest tool versions
- [ ] Clean working directory

---

This comprehensive run guide should enable efficient operation of the UART-AXI4 Bridge verification environment. For additional support, refer to the other documentation files in the `docs/` directory.

**Document Version**: 1.0  
**Last Updated**: January 27, 2025  
**Maintained By**: Verification Team