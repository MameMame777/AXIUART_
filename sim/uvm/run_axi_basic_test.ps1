# AXI Basic Operation Test Runner
# Purpose: Run isolated AXI Master + Register_Block test WITHOUT UART complexity

param(
    [string]$TestMode = "direct",
    [string]$Verbosity = "LOW",
    [int]$Seed = 1
)

# Set error handling
$ErrorActionPreference = "Stop"

# Function to check DSIM environment
function Test-DSIMEnvironment {
    if (-not $env:DSIM_HOME) {
        Write-Error "DSIM_HOME environment variable not set"
        return $false
    }
    
    if (-not (Test-Path $env:DSIM_HOME)) {
        Write-Error "DSIM_HOME path does not exist: $env:DSIM_HOME"
        return $false
    }
    
    return $true
}

# Function to run AXI basic test
function Start-AXIBasicTest {
    param(
        [string]$ConfigFile,
        [string]$TestVerbosity,
        [int]$RandomSeed
    )
    
    Write-Host "🧪 Starting AXI Basic Operation Test" -ForegroundColor Green
    Write-Host "Config: $ConfigFile" -ForegroundColor Cyan
    Write-Host "Verbosity: $TestVerbosity" -ForegroundColor Cyan
    Write-Host "Seed: $RandomSeed" -ForegroundColor Cyan
    
    # Construct DSIM command
    $dsimCmd = @(
        "$env:DSIM_HOME\bin\dsim.exe"
        "-f", $ConfigFile
        "-sv_seed", $RandomSeed
        "+UVM_VERBOSITY=$TestVerbosity"
        "+UVM_TESTNAME=axi_basic_test"
        "-waves"
    )
    
    Write-Host "Executing: $($dsimCmd -join ' ')" -ForegroundColor Yellow
    
    # Run simulation
    try {
        $dsimExe = "$env:DSIM_HOME\bin\dsim.exe"
        $dsimArgs = @(
            "-f", $ConfigFile
            "-sv_seed", $RandomSeed
            "+UVM_VERBOSITY=$TestVerbosity"
        )
        
        & $dsimExe @dsimArgs
        $exitCode = $LASTEXITCODE
        
        if ($exitCode -eq 0) {
            Write-Host "✅ AXI Basic Test PASSED" -ForegroundColor Green
            return $true
        } else {
            Write-Host "❌ AXI Basic Test FAILED (Exit Code: $exitCode)" -ForegroundColor Red
            return $false
        }
    } catch {
        Write-Host "❌ Error running DSIM: $_" -ForegroundColor Red
        return $false
    }
}

# Main execution
try {
    Write-Host "🔧 AXI4-Lite Basic Operation Test" -ForegroundColor Magenta
    Write-Host "Purpose: Verify fundamental AXI Master + Register_Block functionality" -ForegroundColor Gray
    Write-Host ""
    
    # Check DSIM environment
    if (-not (Test-DSIMEnvironment)) {
        exit 1
    }
    
    # Change to simulation directory
    $simDir = Split-Path -Parent $MyInvocation.MyCommand.Path
    Set-Location $simDir
    
    Write-Host "Working directory: $(Get-Location)" -ForegroundColor Cyan
    
    # Select configuration file
    $configFile = "config/axi_basic_test.f"
    
    if (-not (Test-Path $configFile)) {
        Write-Error "Configuration file not found: $configFile"
        exit 1
    }
    
    # Run the test
    $success = Start-AXIBasicTest -ConfigFile $configFile -TestVerbosity $Verbosity -RandomSeed $Seed
    
    if ($success) {
        Write-Host ""
        Write-Host "🎉 AXI Basic Operation Test Completed Successfully!" -ForegroundColor Green
        Write-Host "✅ AXI Master and Register_Block basic functionality verified" -ForegroundColor Green
        Write-Host "🔍 Check waveform: axi_basic_test.mxd" -ForegroundColor Cyan
        exit 0
    } else {
        Write-Host ""
        Write-Host "❌ AXI Basic Operation Test Failed" -ForegroundColor Red
        Write-Host "🔍 Check simulation log and waveform for details" -ForegroundColor Yellow
        exit 1
    }
    
} catch {
    Write-Host "❌ Unexpected error: $_" -ForegroundColor Red
    exit 1
}