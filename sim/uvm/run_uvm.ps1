# Simple UVM Test Execution Script
# Restored to working version before my changes

param(
    [string]$TestName = "uart_axi4_basic_test",
    [bool]$Coverage = $true,  # Coverage enabled by default
    [string]$Verbosity = "UVM_MEDIUM",
    [bool]$Waves = $true,
    [int]$Seed = 1
)

# DSIM Environment Setup (exactly following reference)
$env:DSIM_LICENSE = "$env:USERPROFILE\AppData\Local\metrics-ca\dsim-license.json"
& "$env:USERPROFILE\AppData\Local\metrics-ca\dsim\20240422.0.0\shell_activate.bat"

Write-Host "=== UVM Test Execution ===" -ForegroundColor Cyan
Write-Host "Test: $TestName" -ForegroundColor Green

# Build DSIM command with coverage enabled by default
$dsim_cmd = @(
    "$env:DSIM_HOME\bin\dsim.exe"
    "-f", "dsim_config.f"  # Use clean config with coverage support
    "-sv_lib", "$env:DSIM_HOME\uvm\1.2\lib\uvm_dpi"
    "+UVM_TESTNAME=$TestName"
    "+UVM_VERBOSITY=$Verbosity"
    "-sv_seed", $Seed
)

# Add coverage (RTL code coverage only to prevent crashes)
if ($Coverage) {
    $dsim_cmd += @(
        "-code-cov", "all"          # Enable all code coverage features
        "-code-cov-scope-specs", "coverage_scope.specs"  # Limit to RTL only
        "-cov-db", "metrics.db"     # Coverage database file
        "+define+ENABLE_COVERAGE=1"
    )
    Write-Host "RTL Code Coverage collection enabled" -ForegroundColor Green
} else {
    Write-Host "Coverage collection disabled" -ForegroundColor Yellow
}

# Add waves if enabled (with access control for proper signal visibility)
if ($Waves) {
    $dsim_cmd += @(
        "+acc+rwb",                # Add read/write/bit access for wave dump
        "-waves", "$TestName.mxd"  # Enable MXD wave dump
    )
    Write-Host "Wave dump enabled with signal access: $TestName.mxd" -ForegroundColor Green
}

Write-Host "Executing UVM Test..." -ForegroundColor Cyan

# Execute DSIM
$exitCode = & $dsim_cmd[0] $dsim_cmd[1..($dsim_cmd.Length-1)]

# Generate coverage report if coverage was enabled
if ($Coverage -and $LASTEXITCODE -eq 0) {
    Write-Host "Generating coverage report..." -ForegroundColor Cyan
    & "$env:DSIM_HOME\bin\dcreport.exe" "metrics.db" "-out_dir" "coverage_report"
    if ($LASTEXITCODE -eq 0) {
        Write-Host "Coverage report generated in: coverage_report/" -ForegroundColor Green
        Write-Host "View coverage summary: coverage_report/index.html" -ForegroundColor Green
    } else {
        Write-Host "Coverage report generation failed" -ForegroundColor Red
    }
}

$LASTEXITCODE