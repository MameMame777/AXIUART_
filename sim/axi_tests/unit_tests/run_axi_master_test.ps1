# AXI Master Unit Test Execution Script  
# Based on existing run_uvm.ps1 pattern for DSIM execution
param(
    [string]$TestName = "axi_master_unit_test",
    [int]$Seed = 1,
    [bool]$Waves = $true,
    [bool]$Coverage = $true,
    [bool]$DetailedLog = $true
)

Write-Host "🚀 AXI Master Unit Test - Phase 2" -ForegroundColor Cyan
Write-Host "====================================" -ForegroundColor Cyan

# Enhanced Environment Validation (based on run_uvm.ps1)
function Validate-DSIMEnvironment {
    $errors = @()
    
    if (-not $env:DSIM_HOME) {
        $errors += "DSIM_HOME environment variable not set"
    } elseif (-not (Test-Path "$env:DSIM_HOME\bin\dsim.exe")) {
        $errors += "DSIM executable not found at: $env:DSIM_HOME\bin\dsim.exe"
    }
    
    $config_file = "dsim_config_axi_master.f"
    if (-not (Test-Path $config_file)) {
        $errors += "Configuration file not found: $config_file"
    }
    
    if ($errors.Count -gt 0) {
        Write-Host "Environment validation failed:" -ForegroundColor Red
        $errors | ForEach-Object { Write-Host "  - $_" -ForegroundColor Red }
        exit 1
    }
    
    Write-Host "✓ DSIM environment validated successfully" -ForegroundColor Green
}

# DSIM Environment Setup
try {
    Validate-DSIMEnvironment
    
    # Set DSIM license (following run_uvm.ps1 pattern)
    $env:DSIM_LICENSE = "$env:USERPROFILE\AppData\Local\metrics-ca\dsim-license.json"
    & "$env:USERPROFILE\AppData\Local\metrics-ca\dsim\20240422.0.0\shell_activate.bat"
    
    Write-Host "Test: $TestName" -ForegroundColor Green
    Write-Host "Seed: $Seed" -ForegroundColor Yellow
    
    # Setup paths
    $test_dir = "."
    $timestamp = Get-Date -Format "yyyyMMdd_HHmmss"
    
    # Create directories
    @("logs", "waveforms") | ForEach-Object {
        if (-not (Test-Path $_)) {
            New-Item -ItemType Directory -Path $_ -Force | Out-Null
        }
    }
    
    # Build DSIM command (following run_uvm.ps1 pattern)
    $dsim_cmd = @(
        "$env:DSIM_HOME\bin\dsim.exe",
        "-f", "dsim_config_axi_master.f",
        "-sv_seed", $Seed
    )
    
    # Add detailed logging
    if ($DetailedLog) {
        $logFile = "logs\${TestName}_${timestamp}.log"
        $dsim_cmd += @("-l", $logFile)
        Write-Host "✓ Detailed logging to: $logFile" -ForegroundColor Green
    }
    
    # Add coverage
    if ($Coverage) {
        $dsim_cmd += @(
            "-code-cov", "all",
            "-cov-db", "metrics_${timestamp}.db"
        )
        Write-Host "✓ Code Coverage collection enabled" -ForegroundColor Green
    }
    
    # Add waves
    if ($Waves) {
        $wave_file = "waveforms\${TestName}_${timestamp}.mxd"
        $dsim_cmd += @(
            "+acc+rwb",
            "-waves", $wave_file
        )
        Write-Host "✓ Wave dump enabled: $wave_file" -ForegroundColor Green
    }
    
    Write-Host "`n=== Starting DSIM Compilation and Simulation ===" -ForegroundColor Cyan
    $startTime = Get-Date
    
    # Execute DSIM (following run_uvm.ps1 pattern)
    Write-Host "Command: $($dsim_cmd -join ' ')" -ForegroundColor Gray
    $process = Start-Process -FilePath $dsim_cmd[0] -ArgumentList $dsim_cmd[1..($dsim_cmd.Length-1)] -Wait -PassThru -NoNewWindow
    $exitCode = $process.ExitCode
    
    $endTime = Get-Date
    $duration = $endTime - $startTime
    
    # Results evaluation
    if ($exitCode -eq 0) {
        Write-Host "`n✅ AXI Master Unit Test PASSED" -ForegroundColor Green
        Write-Host "Duration: $($duration.TotalSeconds.ToString('F2')) seconds" -ForegroundColor Cyan
        if ($DetailedLog) { Write-Host "📄 Log: $logFile" -ForegroundColor Cyan }
        if ($Waves) { Write-Host "🌊 Waveform: $wave_file" -ForegroundColor Cyan }
    } else {
        Write-Host "`n❌ AXI Master Unit Test FAILED (Exit Code: $exitCode)" -ForegroundColor Red
        if ($DetailedLog) { Write-Host "📄 Check log: $logFile" -ForegroundColor Yellow }
        exit $exitCode
    }
    
} catch {
    Write-Host "❌ Execution failed: $($_.Exception.Message)" -ForegroundColor Red
    exit 1
}