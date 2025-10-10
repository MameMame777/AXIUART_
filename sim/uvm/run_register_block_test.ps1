# Register Block Detailed Test Runner
# Purpose: Execute comprehensive Register_Block.sv verification
# This fills the gap in current UVM testing

param(
    [string]$TestName = "register_block_detailed_test",
    [string]$Verbosity = "UVM_MEDIUM",
    [int]$Seed = 12345,
    [switch]$Waves = $true
)

# Set environment variables
$env:DSIM_HOME = "C:\Users\Nautilus\AppData\Local\metrics-ca\dsim\20240422.0.0"
$env:DSIM_LICENSE = "C:\Users\Nautilus\AppData\Local\metrics-ca\dsim-license.json"
$env:DSIM_LIB_PATH = "C:\Users\Nautilus\AppData\Local\metrics-ca\dsim\20240422.0.0\lib"
$env:DSIM_ROOT = "C:\Users\Nautilus\AppData\Local\metrics-ca\dsim\20240422.0.0"

if (-not $env:DSIM_HOME) {
    Write-Error "DSIM_HOME environment variable not set"
    exit 1
}

# Verify DSIM installation
if (-not (Test-Path "$env:DSIM_HOME\bin\dsim.exe")) {
    Write-Error "DSIM not found at $env:DSIM_HOME\bin\dsim.exe"
    exit 1
}

# Change to the correct working directory
Set-Location "E:\Nautilus\workspace\fpgawork\AXIUART_\sim\uvm"
Write-Host "Working directory: $(Get-Location)" -ForegroundColor Cyan

$timestamp = Get-Date -Format "yyyyMMdd_HHmmss"
$logFile = "..\exec\logs\${TestName}_${timestamp}.log"
$waveFile = "..\..\archive\waveforms\${TestName}_${timestamp}.mxd"

Write-Host "=== Register Block Detailed Verification Test ===" -ForegroundColor Green
Write-Host "Test: $TestName" -ForegroundColor Yellow
Write-Host "Purpose: Comprehensive Register_Block.sv testing" -ForegroundColor Yellow
Write-Host "Gap Filled: Individual register function verification" -ForegroundColor Yellow
Write-Host "Log: $logFile" -ForegroundColor Cyan
if ($Waves) {
    Write-Host "Waveform: $waveFile" -ForegroundColor Cyan
}

# Build DSIM command with proper UVM library path
$dsimArgs = @(
    "-f", "E:\Nautilus\workspace\fpgawork\AXIUART_\sim\uvm\dsim_config.f"
    "-sv_lib", "$env:DSIM_HOME\uvm\1.2\src\dpi\libuvm_dpi"
    "+UVM_TESTNAME=$TestName"
    "+UVM_VERBOSITY=$Verbosity"
    "-sv_seed", $Seed
    "-l", $logFile
    "+define+ENABLE_ASSERTIONS=1"
    "+acc+rwb"
)

if ($Waves) {
    $dsimArgs += "-waves", $waveFile
    $dsimArgs += "+define+WAVES"
}

# Coverage options (matching existing successful tests)
$dsimArgs += @(
    "-code-cov", "all"
    "-code-cov-scope-specs", "E:\Nautilus\workspace\fpgawork\AXIUART_\sim\uvm\coverage_scope.specs"
    "-cov-db", "E:\Nautilus\workspace\fpgawork\AXIUART_\sim\uvm\metrics.db"
    "+define+ENABLE_COVERAGE=1"
)

Write-Host "Executing DSIM..." -ForegroundColor Yellow
Write-Host "Command: dsim.exe $($dsimArgs -join ' ')" -ForegroundColor Gray

try {
    & "$env:DSIM_HOME\bin\dsim.exe" @dsimArgs
    $exitCode = $LASTEXITCODE
    
    if ($exitCode -eq 0) {
        Write-Host "=== Register Block Test COMPLETED ===" -ForegroundColor Green
        Write-Host "Check log file for detailed results: $logFile" -ForegroundColor Cyan
        if ($Waves) {
            Write-Host "Waveform saved: $waveFile" -ForegroundColor Cyan
        }
    } else {
        Write-Host "=== Register Block Test FAILED ===" -ForegroundColor Red
        Write-Host "Exit code: $exitCode" -ForegroundColor Red
        Write-Host "Check log: $logFile" -ForegroundColor Red
    }
    
    return $exitCode
} catch {
    Write-Error "Failed to execute DSIM: $_"
    return 1
}