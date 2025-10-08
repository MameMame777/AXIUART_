# Register_Block Unit Test Execution Script
# Purpose: Phase 3 - Verify Register_Block AXI slave functionality

param(
    [string]$TestMode = "run",     # run or compile_only
    [string]$Verbosity = "medium", # low, medium, high
    [int]$Seed = 12345,
    [switch]$OpenWaveform = $false
)

Write-Host "🧪 Register_Block Unit Test - Phase 3" -ForegroundColor Cyan
Write-Host "====================================" -ForegroundColor Cyan

# Environment validation
if (-not $env:DSIM_HOME) {
    Write-Error "❌ DSIM_HOME environment variable not set"
    exit 1
}

if (-not (Test-Path $env:DSIM_HOME)) {
    Write-Error "❌ DSIM_HOME path does not exist: $env:DSIM_HOME"
    exit 1
}

# Path configuration
$DSIMPath = Join-Path $env:DSIM_HOME "bin\dsim.exe"
$ConfigFile = "dsim_config_register_block.f"
$TestName = "register_block_unit_test"
$LogFile = "${TestName}.log"
$WaveformFile = "${TestName}.mxd"

Write-Host "📁 DSIM Path: $DSIMPath" -ForegroundColor Yellow
Write-Host "📄 Config File: $ConfigFile" -ForegroundColor Yellow
Write-Host "📊 Log File: $LogFile" -ForegroundColor Yellow

# Verify files exist
if (-not (Test-Path $ConfigFile)) {
    Write-Error "❌ Configuration file not found: $ConfigFile"
    exit 1
}

if (-not (Test-Path $DSIMPath)) {
    Write-Error "❌ DSIM executable not found: $DSIMPath"
    exit 1
}

# Build DSIM arguments
$DSIMArgs = @(
    "-f", $ConfigFile,
    "-sv",
    "-waves", $WaveformFile
)

# Add verbosity
switch ($Verbosity) {
    "low"    { $DSIMArgs += @() }
    "medium" { $DSIMArgs += @() }
    "high"   { $DSIMArgs += @() }
}

# Compilation only mode
if ($TestMode -eq "compile_only") {
    Write-Host "🔧 Compilation-only mode" -ForegroundColor Green
    $DSIMArgs += @("-c")
}

# Clean previous results
if (Test-Path $LogFile) { Remove-Item $LogFile -Force }
if (Test-Path $WaveformFile) { Remove-Item $WaveformFile -Force }
if (Test-Path "dsim_work") { Remove-Item "dsim_work" -Recurse -Force }

Write-Host "🚀 Starting Register_Block Unit Test..." -ForegroundColor Green
Write-Host "Command: $DSIMPath $($DSIMArgs -join ' ')" -ForegroundColor Gray

try {
    # Execute DSIM
    $Process = Start-Process -FilePath $DSIMPath -ArgumentList $DSIMArgs -NoNewWindow -Wait -PassThru -RedirectStandardOutput $LogFile -RedirectStandardError "${TestName}_error.log"
    
    # Check results
    if ($Process.ExitCode -eq 0) {
        Write-Host "✅ Simulation completed successfully" -ForegroundColor Green
        
        # Parse log for test results
        if (Test-Path $LogFile) {
            $LogContent = Get-Content $LogFile
            
            # Look for test results
            $PassedLines = $LogContent | Select-String "PASS:"
            $FailedLines = $LogContent | Select-String "FAIL:"
            $SummaryLines = $LogContent | Select-String "Register_Block Unit Test"
            
            Write-Host "`n📊 Test Results Summary:" -ForegroundColor Cyan
            if ($PassedLines) {
                Write-Host "✅ Passed Tests: $($PassedLines.Count)" -ForegroundColor Green
            }
            if ($FailedLines) {
                Write-Host "❌ Failed Tests: $($FailedLines.Count)" -ForegroundColor Red
            }
            
            # Display summary lines
            foreach ($line in $SummaryLines) {
                if ($line -match "SUCCESSFUL") {
                    Write-Host $line -ForegroundColor Green
                } elseif ($line -match "FAILED") {
                    Write-Host $line -ForegroundColor Red
                }
            }
        }
        
        # Waveform info
        if (Test-Path $WaveformFile) {
            Write-Host "📈 Waveform file generated: $WaveformFile" -ForegroundColor Yellow
            if ($OpenWaveform) {
                Write-Host "🔍 Opening waveform viewer..." -ForegroundColor Green
                Start-Process -FilePath (Join-Path $env:DSIM_HOME "bin\simvision.exe") -ArgumentList $WaveformFile
            }
        }
        
    } else {
        Write-Host "❌ Simulation failed with exit code: $($Process.ExitCode)" -ForegroundColor Red
        
        # Show error details
        if (Test-Path "${TestName}_error.log") {
            $ErrorContent = Get-Content "${TestName}_error.log"
            if ($ErrorContent) {
                Write-Host "`n🔍 Error Details:" -ForegroundColor Red
                $ErrorContent | ForEach-Object { Write-Host "   $_" -ForegroundColor Red }
            }
        }
        
        exit $Process.ExitCode
    }
    
} catch {
    Write-Error "❌ Failed to execute DSIM: $_"
    exit 1
}

Write-Host "`n🎯 Register_Block Unit Test completed!" -ForegroundColor Cyan
Write-Host "Log file: $LogFile" -ForegroundColor Gray
if (Test-Path $WaveformFile) {
    Write-Host "Waveform file: $WaveformFile" -ForegroundColor Gray
}