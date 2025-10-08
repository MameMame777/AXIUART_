# AXI Integration Test Runner
# Tests real AXI Master + Register_Block modules together

param(
    [string]$TestName = "axi_integration_test",
    [int]$Seed = 1,
    [switch]$Gui = $false
)

# Verify DSIM environment
if (-not $env:DSIM_HOME) {
    Write-Host "❌ Error: DSIM_HOME environment variable not set" -ForegroundColor Red
    exit 1
}

$dsimPath = Join-Path $env:DSIM_HOME "bin" "dsim.exe"
if (-not (Test-Path $dsimPath)) {
    Write-Host "❌ Error: DSIM executable not found at: $dsimPath" -ForegroundColor Red
    exit 1
}

Write-Host "🎯 AXI Integration Test - Real RTL Modules" -ForegroundColor Cyan
Write-Host "==========================================" -ForegroundColor Cyan
Write-Host "✅ DSIM environment validated successfully" -ForegroundColor Green

# Setup directories
$logDir = "logs"
$waveDir = "waveforms"
if (-not (Test-Path $logDir)) { New-Item -ItemType Directory -Path $logDir -Force | Out-Null }
if (-not (Test-Path $waveDir)) { New-Item -ItemType Directory -Path $waveDir -Force | Out-Null }

# Generate timestamp
$timestamp = Get-Date -Format "yyyyMMdd_HHmmss"
$logFile = Join-Path $logDir "${TestName}_${timestamp}.log"
$waveFile = Join-Path $waveDir "${TestName}_${timestamp}.mxd"
$covDb = "metrics_${timestamp}.db"

Write-Host "Test: $TestName" -ForegroundColor Yellow
Write-Host "Seed: $Seed" -ForegroundColor Yellow
Write-Host "✅ Detailed logging to: $logFile" -ForegroundColor Green
Write-Host "✅ Code Coverage collection enabled" -ForegroundColor Green
Write-Host "✅ Wave dump enabled: $waveFile" -ForegroundColor Green

Write-Host "`n=== Starting DSIM Compilation and Simulation ===" -ForegroundColor Cyan

# Build DSIM command
$dsimCmd = @(
    $dsimPath,
    "-f", "dsim_config_integration.f",
    "-sv_seed", $Seed,
    "-l", $logFile,
    "-code-cov", "all",
    "-cov-db", $covDb,
    "+acc+rwb",
    "-waves", $waveFile
)

if ($Gui) {
    $dsimCmd += "-gui"
}

$cmdString = $dsimCmd -join " "
Write-Host "Command: $cmdString" -ForegroundColor White

# Execute DSIM
$stopwatch = [System.Diagnostics.Stopwatch]::StartNew()
$process = Start-Process -FilePath $dsimCmd[0] -ArgumentList $dsimCmd[1..($dsimCmd.Length-1)] -Wait -PassThru -NoNewWindow

$stopwatch.Stop()
$duration = $stopwatch.Elapsed.TotalSeconds

# Check results
if ($process.ExitCode -eq 0) {
    Write-Host "✅ AXI Integration Test PASSED" -ForegroundColor Green
    Write-Host "Duration: $([math]::Round($duration, 2)) seconds" -ForegroundColor Green
    Write-Host "📊 Log: $logFile" -ForegroundColor Blue
    Write-Host "🌊 Waveform: $waveFile" -ForegroundColor Blue
    
    # Check for specific success patterns in log
    if (Test-Path $logFile) {
        $logContent = Get-Content $logFile -Raw
        if ($logContent -match "ALL TESTS PASSED") {
            Write-Host "🎉 Integration test verification: ALL TESTS PASSED" -ForegroundColor Green
        } elseif ($logContent -match "SOME TESTS FAILED") {
            Write-Host "⚠️  Integration test verification: SOME TESTS FAILED" -ForegroundColor Yellow
        }
    }
} else {
    Write-Host "❌ AXI Integration Test FAILED" -ForegroundColor Red
    Write-Host "Exit Code: $($process.ExitCode)" -ForegroundColor Red
    Write-Host "Duration: $([math]::Round($duration, 2)) seconds" -ForegroundColor Red
    Write-Host "📊 Log: $logFile" -ForegroundColor Blue
    
    # Show last few lines of log for quick debugging
    if (Test-Path $logFile) {
        Write-Host "`n--- Last 10 lines of log ---" -ForegroundColor Yellow
        Get-Content $logFile | Select-Object -Last 10 | ForEach-Object { Write-Host $_ }
    }
    
    exit $process.ExitCode
}

# Offer to open waveform
if (-not $Gui -and (Test-Path $waveFile)) {
    $response = Read-Host "`nOpen waveform in viewer? (y/N)"
    if ($response -eq 'y' -or $response -eq 'Y') {
        Start-Process $waveFile
    }
}