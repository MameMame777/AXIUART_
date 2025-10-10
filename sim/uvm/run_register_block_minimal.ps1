# Register Block Minimal Test Runner
# Purpose: Execute minimal test without complexity

param(
    [switch]$Compile = $false,
    [string]$Seed = "12345"
)

# Check DSIM environment
if (-not $env:DSIM_HOME) {
    Write-Error "DSIM_HOME environment variable not set"
    exit 1
}

# Set DSIM license (following working pattern from run_uvm.ps1)
$env:DSIM_LICENSE = "$env:USERPROFILE\AppData\Local\metrics-ca\dsim-license.json"

$dsim_exe = "$env:DSIM_HOME\bin\dsim.exe"
if (-not (Test-Path $dsim_exe)) {
    Write-Error "DSIM executable not found: $dsim_exe"
    exit 1
}

if (-not (Test-Path $env:DSIM_LICENSE)) {
    Write-Error "DSIM license file not found: $env:DSIM_LICENSE"
    exit 1
}

Write-Host "=== Register Block Minimal Test ===" -ForegroundColor Green
Write-Host "DSIM_HOME: $env:DSIM_HOME" -ForegroundColor Cyan
Write-Host "Working Directory: $(Get-Location)" -ForegroundColor Cyan

# Clean previous run
if (Test-Path "dsim_work") {
    Remove-Item -Recurse -Force "dsim_work"
}

# Execute simulation directly (single command approach like run_uvm.ps1)
$sim_args = @(
    "-f", "register_block_minimal.f",
    "-sv_lib", "$env:DSIM_HOME\uvm\1.2\src\dpi\libuvm_dpi.so",
    "-sv_seed", $Seed,
    "+UVM_TESTNAME=register_block_minimal_test",
    "+UVM_VERBOSITY=UVM_LOW"
)

Write-Host "Running simulation..." -ForegroundColor Yellow
Write-Host "Command: $dsim_exe $($sim_args -join ' ')" -ForegroundColor Gray

$sim_result = Start-Process -FilePath $dsim_exe -ArgumentList $sim_args -Wait -PassThru -NoNewWindow

# Check results
if ($sim_result.ExitCode -eq 0) {
    Write-Host "=== SIMULATION PASSED ===" -ForegroundColor Green
} else {
    Write-Host "=== SIMULATION FAILED ===" -ForegroundColor Red
    exit 1
}

# Display summary
if (Test-Path "dsim.log") {
    $logContent = Get-Content "dsim.log" -Raw
    
    # Extract UVM error count from final report
    if ($logContent -match "UVM_ERROR\s*:\s*(\d+)") {
        $uvm_errors = [int]$matches[1]
    } else {
        $uvm_errors = 0
    }
    
    # Extract UVM warning count from final report
    if ($logContent -match "UVM_WARNING\s*:\s*(\d+)") {
        $uvm_warnings = [int]$matches[1]  
    } else {
        $uvm_warnings = 0
    }
    
    Write-Host "UVM Errors: $uvm_errors" -ForegroundColor $(if($uvm_errors -eq 0) {"Green"} else {"Red"})
    Write-Host "UVM Warnings: $uvm_warnings" -ForegroundColor $(if($uvm_warnings -eq 0) {"Green"} else {"Yellow"})
    
    if ($uvm_errors -eq 0) {
        Write-Host "✓ TRUE SUCCESS: No UVM errors detected" -ForegroundColor Green
    } else {
        Write-Host "✗ Test failed with $uvm_errors UVM errors" -ForegroundColor Red
    }
}

Write-Host "=== Test Complete ===" -ForegroundColor Green