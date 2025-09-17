# UVM Original Reference Test Execution Script
# Purpose: Execute complete UVM verification environment
# Date: August 12, 2025
# Note: Uses UVM configuration for full verification testing

param(
    [string]$TestName = "uart_axi4_basic_test"
)

Write-Host "=== UVM Verification Environment ===" -ForegroundColor Cyan
Write-Host "Purpose: Complete UVM-based verification with agents and scoreboards" -ForegroundColor Yellow
Write-Host "Test: $TestName" -ForegroundColor Green

# DSIM Environment Setup (following reference implementation pattern)
$env:DSIM_LICENSE = "$env:USERPROFILE\AppData\Local\metrics-ca\dsim-license.json"
& "$env:USERPROFILE\AppData\Local\metrics-ca\dsim\20240422.0.0\shell_activate.bat"

# Use UVM configuration for complete verification
Write-Host "Using UVM configuration for complete verification environment"
& dsim -f dsim_config_working.f +acc -waves "uvm_verification_$TestName.mxd" +UVM_TESTNAME=$TestName +UVM_VERBOSITY=UVM_MEDIUM

if ($LASTEXITCODE -eq 0) {
    Write-Host "✅ UVM verification completed successfully" -ForegroundColor Green
    Write-Host "📄 Waveform: uvm_verification_$TestName.mxd" -ForegroundColor Cyan
    Write-Host "📝 Purpose: This UVM verification validates design with agents and scoreboards" -ForegroundColor Yellow
} else {
    Write-Host "❌ UVM verification failed with error code: $LASTEXITCODE" -ForegroundColor Red
    Write-Host "💡 Check UVM agent packages and testbench configuration" -ForegroundColor Yellow
    exit $LASTEXITCODE
}
