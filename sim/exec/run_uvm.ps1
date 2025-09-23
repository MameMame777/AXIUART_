param(
    [string]$TestName = "uart_axi4_basic_test",
    [string]$Verbosity = "UVM_MEDIUM"
)

# Check DSIM environment variables
if (-not $env:DSIM_HOME) {
    Write-Error "DSIM_HOME environment variable is not set"
    exit 1
}

# Build paths
$dsim_exe = "$env:DSIM_HOME\bin\dsim.exe"
$config_file = "..\dsim_config.f"

# Create log directory if not exists
if (-not (Test-Path "logs")) {
    New-Item -ItemType Directory -Name "logs"
}

$log_file = "logs\dsim_$TestName.log"
$wave_file = "$TestName.mxd"

Write-Host "Starting UVM test execution with DSIM..." -ForegroundColor Green
Write-Host "Test: $TestName" -ForegroundColor Cyan
Write-Host "Verbosity: $Verbosity" -ForegroundColor Cyan
Write-Host "Log: $log_file" -ForegroundColor Cyan
Write-Host "Waveform: $wave_file" -ForegroundColor Cyan

# Execute DSIM
$dsim_args = @(
    "-f", $config_file,
    "+UVM_TESTNAME=$TestName",
    "+UVM_VERBOSITY=$Verbosity",
    "-waves", $wave_file,
    "-l", $log_file
)

& $dsim_exe @dsim_args

if ($LASTEXITCODE -eq 0) {
    Write-Host "Test completed successfully!" -ForegroundColor Green
    
    # Check for UVM errors in log
    $log_content = Get-Content $log_file -Raw
    if ($log_content -match "UVM_ERROR\s*:\s*(\d+)") {
        $error_count = $matches[1]
        if ($error_count -eq "0") {
            Write-Host "UVM_ERROR: 0 - No errors detected" -ForegroundColor Green
        } else {
            Write-Host "UVM_ERROR: $error_count - Errors found in test" -ForegroundColor Red
        }
    }
} else {
    Write-Host "Test execution failed with exit code: $LASTEXITCODE" -ForegroundColor Red
    exit $LASTEXITCODE
}