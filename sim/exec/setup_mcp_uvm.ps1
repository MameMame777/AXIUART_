# MCP-UVM Setup and Quick Start Script
# Initialize MCP server environment for UVM simulation

Write-Host @"
🔬 MCP-UVM Environment Setup
==========================
Initializing MCP server optimized UVM environment...
"@ -ForegroundColor Cyan

# Import MCP-UVM functions
$scriptDir = Split-Path -Parent $PSCommandPath
$moduleFile = Join-Path $scriptDir "MCPUVMFunctions.psm1"

if (Test-Path $moduleFile) {
    Import-Module $moduleFile -Force
    Write-Host "✅ MCP-UVM functions imported successfully" -ForegroundColor Green
} else {
    Write-Host "❌ MCP-UVM functions module not found: $moduleFile" -ForegroundColor Red
    exit 1
}

# Verify DSIM environment
Write-Host "`n🔍 Verifying DSIM environment..." -ForegroundColor Yellow
$dsimVars = @("DSIM_HOME", "DSIM_ROOT", "DSIM_LIB_PATH")
$allValid = $true

foreach ($var in $dsimVars) {
    $value = [Environment]::GetEnvironmentVariable($var)
    if ($value -and (Test-Path $value)) {
        Write-Host "  ✅ $var = $value" -ForegroundColor Green
    } else {
        Write-Host "  ❌ $var not set or invalid" -ForegroundColor Red
        $allValid = $false
    }
}

if (-not $allValid) {
    Write-Host "`n❌ DSIM environment validation failed" -ForegroundColor Red
    exit 1
}

# Check dsim executable
$dsimExe = Join-Path $env:DSIM_HOME "bin\dsim.exe"
if (Test-Path $dsimExe) {
    Write-Host "  ✅ DSIM executable found: $dsimExe" -ForegroundColor Green
} else {
    Write-Host "  ❌ DSIM executable not found: $dsimExe" -ForegroundColor Red
    exit 1
}

# Verify UVM configuration files
Write-Host "`n📁 Verifying UVM configuration..." -ForegroundColor Yellow
$scriptDir = Split-Path -Parent $PSCommandPath
$configFile = Join-Path (Split-Path $scriptDir -Parent) "uvm\dsim_config.f"
if (Test-Path $configFile) {
    Write-Host "  ✅ UVM config file found: $configFile" -ForegroundColor Green
} else {
    Write-Host "  ❌ UVM config file not found: $configFile" -ForegroundColor Red
    exit 1
}

# Create necessary directories
Write-Host "`n📂 Creating output directories..." -ForegroundColor Yellow
$projectRoot = Split-Path (Split-Path $scriptDir -Parent) -Parent
$dirs = @(
    (Join-Path $scriptDir "logs"),
    (Join-Path $projectRoot "archive\waveforms"),
    (Join-Path $scriptDir "coverage_report")
)

foreach ($dir in $dirs) {
    if (-not (Test-Path $dir)) {
        New-Item -ItemType Directory -Path $dir -Force | Out-Null
        Write-Host "  📁 Created: $dir" -ForegroundColor Yellow
    } else {
        Write-Host "  ✅ Exists: $dir" -ForegroundColor Green
    }
}

Write-Host @"

✅ MCP-UVM Environment Ready!
============================

Quick Start Commands:
--------------------
# Basic test execution
Invoke-MCPUVMTest

# Quick test (fast iteration)
Invoke-MCPUVMQuickTest

# Compile check only
Invoke-MCPUVMCompileOnly

# Debug with waveforms
Invoke-MCPUVMWithWaves

# Check recent results
Get-MCPUVMStatus

# Show all available commands
Show-MCPUVMHelp

# Example: Run scoreboard test with waveforms
Invoke-MCPUVMTest -TestName "uart_axi4_scoreboard_test" -Waves on -Verbosity UVM_HIGH

Ready for MCP server UVM simulation!
"@ -ForegroundColor Green