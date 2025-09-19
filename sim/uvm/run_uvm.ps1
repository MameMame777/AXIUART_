# Enhanced UVM Test Execution Script for AXIUART
# Provides comprehensive test execution with error handling and reporting

param(
    [string]$TestName = "uart_axi4_basic_test",
    [bool]$Coverage = $true,  # Coverage enabled by default
    [string]$Verbosity = "UVM_MEDIUM",
    [bool]$Waves = $true,
    [int]$Seed = 1,
    [bool]$CleanBuild = $false,
    [bool]$DetailedLog = $false
)

# Enhanced Environment Validation
function Validate-DSIMEnvironment {
    $errors = @()
    
    if (-not $env:DSIM_HOME) {
        $errors += "DSIM_HOME environment variable not set"
    } elseif (-not (Test-Path "$env:DSIM_HOME\bin\dsim.exe")) {
        $errors += "DSIM executable not found at: $env:DSIM_HOME\bin\dsim.exe"
    }
    
    if (-not (Test-Path "dsim_config.f")) {
        $errors += "dsim_config.f file not found in current directory"
    }
    
    if (-not (Test-Path "$env:DSIM_HOME\uvm\1.2\src\dpi\libuvm_dpi.so")) {
        $errors += "UVM DPI library not found"
    }
    
    if ($errors.Count -gt 0) {
        Write-Host "Environment validation failed:" -ForegroundColor Red
        $errors | ForEach-Object { Write-Host "  - $_" -ForegroundColor Red }
        exit 1
    }
    
    Write-Host "✓ DSIM environment validated successfully" -ForegroundColor Green
}

# DSIM Environment Setup with validation
try {
    Validate-DSIMEnvironment
    
    $env:DSIM_LICENSE = "$env:USERPROFILE\AppData\Local\metrics-ca\dsim-license.json"
    & "$env:USERPROFILE\AppData\Local\metrics-ca\dsim\20240422.0.0\shell_activate.bat"
    
    Write-Host "=== Enhanced UVM Test Execution ===" -ForegroundColor Cyan
    Write-Host "Test: $TestName" -ForegroundColor Green
    Write-Host "Seed: $Seed" -ForegroundColor Yellow
    Write-Host "Coverage: $(if($Coverage){'Enabled'}else{'Disabled'})" -ForegroundColor $(if($Coverage){'Green'}else{'Yellow'})
    Write-Host "Waveforms: $(if($Waves){'Enabled'}else{'Disabled'})" -ForegroundColor $(if($Waves){'Green'}else{'Yellow'})
} catch {
    Write-Host "Failed to setup DSIM environment: $($_.Exception.Message)" -ForegroundColor Red
    exit 1
}

# Clean build option
if ($CleanBuild) {
    Write-Host "Performing clean build..." -ForegroundColor Yellow
    if (Test-Path "dsim_work") { Remove-Item -Recurse -Force "dsim_work" }
    if (Test-Path "work") { Remove-Item -Recurse -Force "work" }
    if (Test-Path "metrics.db") { Remove-Item -Force "metrics.db" }
    Write-Host "✓ Clean build prepared" -ForegroundColor Green
}

# Build enhanced DSIM command
$dsim_cmd = @(
    "$env:DSIM_HOME\bin\dsim.exe"
    "-f", "dsim_config.f"
    "-sv_lib", "$env:DSIM_HOME\uvm\1.2\src\dpi\libuvm_dpi"
    "+UVM_TESTNAME=$TestName"
    "+UVM_VERBOSITY=$Verbosity"
    "-sv_seed", $Seed
    "+define+ENABLE_ASSERTIONS=1"  # Enable protocol assertions
)

# Add detailed logging if requested
if ($DetailedLog) {
    $logFile = "${TestName}_$(Get-Date -Format 'yyyyMMdd_HHmmss').log"
    $dsim_cmd += @("-l", $logFile)
    Write-Host "Detailed logging to: $logFile" -ForegroundColor Yellow
}

# Add coverage (RTL code coverage only to prevent crashes)
if ($Coverage) {
    $dsim_cmd += @(
        "-code-cov", "all"
        "-code-cov-scope-specs", "coverage_scope.specs"
        "-cov-db", "metrics.db"
        "+define+ENABLE_COVERAGE=1"
    )
    Write-Host "✓ RTL Code Coverage collection enabled" -ForegroundColor Green
} else {
    Write-Host "Coverage collection disabled" -ForegroundColor Yellow
}

# Add waves if enabled (with access control for proper signal visibility)
if ($Waves) {
    $dsim_cmd += @(
        "+acc+rwb",
        "-waves", "$TestName.mxd"
    )
    Write-Host "✓ Wave dump enabled: $TestName.mxd" -ForegroundColor Green
}

Write-Host "`n=== Starting DSIM Compilation and Simulation ===" -ForegroundColor Cyan
$startTime = Get-Date

# Execute DSIM with error handling
try {
    Write-Host "Command: $($dsim_cmd -join ' ')" -ForegroundColor Gray
    $process = Start-Process -FilePath $dsim_cmd[0] -ArgumentList $dsim_cmd[1..($dsim_cmd.Length-1)] -Wait -PassThru -NoNewWindow
    $exitCode = $process.ExitCode
} catch {
    Write-Host "Failed to execute DSIM: $($_.Exception.Message)" -ForegroundColor Red
    exit 1
}

$endTime = Get-Date
$duration = $endTime - $startTime

# Analyze results
Write-Host "`n=== Test Results Analysis ===" -ForegroundColor Cyan
Write-Host "Execution time: $($duration.ToString('mm\:ss\.ff'))" -ForegroundColor Yellow

if ($exitCode -eq 0) {
    Write-Host "✓ DSIM execution completed successfully" -ForegroundColor Green
    
    # Parse log for UVM results
    if (Test-Path "dsim.log") {
        $logContent = Get-Content "dsim.log" -Raw
        
        # Check for UVM test results
        if ($logContent -match "UVM_ERROR\s*:\s*(\d+)") {
            $uvm_errors = [int]$matches[1]
            if ($uvm_errors -eq 0) {
                Write-Host "✓ UVM test passed (UVM_ERROR: $uvm_errors)" -ForegroundColor Green
            } else {
                Write-Host "✗ UVM test failed (UVM_ERROR: $uvm_errors)" -ForegroundColor Red
            }
        }
        
        if ($logContent -match "UVM_WARNING\s*:\s*(\d+)") {
            $uvm_warnings = [int]$matches[1]
            if ($uvm_warnings -gt 0) {
                Write-Host "⚠ UVM warnings detected: $uvm_warnings" -ForegroundColor Yellow
            }
        }
        
        # Check for protocol assertion violations
        if ($logContent -match "AXI_ASSERT") {
            Write-Host "⚠ AXI protocol assertion violations detected" -ForegroundColor Yellow
        }
    }
    
} else {
    Write-Host "✗ DSIM execution failed with exit code: $exitCode" -ForegroundColor Red
    
    # Analyze common failure causes
    if (Test-Path "dsim.log") {
        $logContent = Get-Content "dsim.log" -Raw
        
        if ($logContent -match "Error-\[ICXH\]") {
            Write-Host "Possible cause: Interface connection issues" -ForegroundColor Red
        }
        if ($logContent -match "Error-\[TFNF\]") {
            Write-Host "Possible cause: Task or function not found" -ForegroundColor Red
        }
        if ($logContent -match "Error-\[IPDW\]") {
            Write-Host "Possible cause: Incompatible port data widths" -ForegroundColor Red
        }
    }
}

# Generate coverage report if coverage was enabled and test passed
if ($Coverage -and $exitCode -eq 0) {
    Write-Host "`n=== Generating Coverage Report ===" -ForegroundColor Cyan
    try {
        $coverageProcess = Start-Process -FilePath "$env:DSIM_HOME\bin\dcreport.exe" -ArgumentList @("metrics.db", "-out_dir", "coverage_report") -Wait -PassThru -NoNewWindow
        if ($coverageProcess.ExitCode -eq 0) {
            Write-Host "✓ Coverage report generated in: coverage_report/" -ForegroundColor Green
            Write-Host "  View summary: coverage_report/index.html" -ForegroundColor Green
        } else {
            Write-Host "✗ Coverage report generation failed" -ForegroundColor Red
        }
    } catch {
        Write-Host "✗ Coverage report error: $($_.Exception.Message)" -ForegroundColor Red
    }
}

# Final status
Write-Host "`n=== Execution Summary ===" -ForegroundColor Cyan
Write-Host "Test: $TestName" -ForegroundColor Gray
Write-Host "Duration: $($duration.ToString('mm\:ss\.ff'))" -ForegroundColor Gray
Write-Host "Exit Code: $exitCode" -ForegroundColor $(if($exitCode -eq 0){'Green'}else{'Red'})

if ($Waves -and $exitCode -eq 0 -and (Test-Path "$TestName.mxd")) {
    Write-Host "✓ Waveform file generated: $TestName.mxd" -ForegroundColor Green
}

exit $exitCode