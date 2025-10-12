#!/usr/bin/env pwsh

# Enhanced DSIM UVM runner with mandatory reporting standards
# Compliance: UVM Reporting Strategy Implementation (October 10, 2025)
[CmdletBinding()]
param(
    [ValidateSet("run", "compile")]
    [string]$Mode = "run",

    [string]$TestName = "uart_axi4_basic_test",

    [ValidateSet("UVM_NONE", "UVM_LOW", "UVM_MEDIUM", "UVM_HIGH", "UVM_FULL")]
    [string]$Verbosity = "UVM_MEDIUM",

    [int]$Seed = 1,

    [ValidateSet("on", "off")]
    [string]$Waves = "off",

    [ValidateSet("on", "off")]
    [string]$Coverage = "on",

    [ValidateSet("on", "off")]
    [string]$ClearWaveforms = "on",

    [string]$LogDir = "logs",

    [string]$WaveDir = "..\\..\\archive\\waveforms",

    [string]$MetricsDb = "metrics.db",

    [string]$ConfigFile = "..\\uvm\\dsim_config.f",

    # MANDATORY: Enhanced reporting parameters (October 10, 2025 Standards)
    [switch]$ReportAnalysis = $true,  # DEFAULT ENABLED per guidelines
    [switch]$DetailedReporting = $false,
    [string]$ReportFilter = "ALL",

    [string[]]$ExtraArgs = @()
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

# Utility functions - defined first
function Write-Status {
    param(
        [string]$Message,
        [ConsoleColor]$Color = [ConsoleColor]::White
    )
    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    Write-Host "[$timestamp] $Message" -ForegroundColor $Color
}

# Enhanced reporting announcement
if ($ReportAnalysis) {
    Write-Status "Enhanced UVM report analysis enabled by default (October 10, 2025 Standards)" ([ConsoleColor]::Green)
}

function Analyze-UVMReports {
    param(
        [string]$LogFile,
        [string]$TestName
    )
    
    Write-Status "=== UVM ENHANCED REPORT ANALYSIS (October 10, 2025 Standards) ===" ([ConsoleColor]::Yellow)
    
    if (-not (Test-Path $LogFile)) {
        Write-Status "Warning: Log file '$LogFile' not found. Skipping analysis." ([ConsoleColor]::Red)
        return
    }
    
    # Read log content
    $content = Get-Content $LogFile -Raw
    
    # Extract report counts by severity
    if ($content -match '\*\* Report counts by severity\s+(.*?)\*\* Report counts by id') {
        $severitySection = $Matches[1]
        Write-Status "Report Counts by Severity:" ([ConsoleColor]::Green)
        $severitySection -split "`n" | Where-Object { $_ -match '^\s*UVM_' } | ForEach-Object {
            $line = $_.Trim()
            if ($line -match 'UVM_ERROR') {
                Write-Host "  $line" -ForegroundColor Red
            } elseif ($line -match 'UVM_WARNING') {
                Write-Host "  $line" -ForegroundColor Yellow
            } else {
                Write-Host "  $line" -ForegroundColor White
            }
        }
    }
    
    # Enhanced report counts by ID analysis
    if ($content -match '\*\* Report counts by id\s+(.*?)\n\n') {
        $idSection = $Matches[1]
        Write-Status "`nReport Counts by ID (Component Analysis):" ([ConsoleColor]::Green)
        
        $reportData = @()
        $idSection -split "`n" | Where-Object { $_ -match '^\[.*\]\s+\d+' } | ForEach-Object {
            if ($_ -match '^\[([^\]]+)\]\s+(\d+)(.*)') {
                $component = $Matches[1]
                $count = [int]$Matches[2]
                $comment = $Matches[3].Trim()
                
                $reportData += [PSCustomObject]@{
                    Component = $component
                    Count = $count
                    Comment = $comment
                }
                
                # Color coding based on volume
                $color = if ($count -gt 50) { [ConsoleColor]::Red } 
                        elseif ($count -gt 20) { [ConsoleColor]::Yellow } 
                        elseif ($count -gt 10) { [ConsoleColor]::Cyan } 
                        else { [ConsoleColor]::White }
                        
                Write-Host "  [$component] $count $comment" -ForegroundColor $color
            }
        }
        
        # Enhanced summary statistics
        if ($reportData -and $reportData.Length -gt 0) {
            $totalReports = ($reportData | Measure-Object -Property Count -Sum).Sum
            $topReporter = $reportData | Sort-Object Count -Descending | Select-Object -First 1
            $componentCount = @($reportData).Length
            $avgReports = [math]::Round($totalReports / $componentCount, 1)
            
            Write-Status "`n=== ENHANCED REPORT SUMMARY for $TestName ===" ([ConsoleColor]::Green)
            Write-Host "  Total Reports Generated: $totalReports" -ForegroundColor White
            Write-Host "  Active Components: $componentCount" -ForegroundColor White
            Write-Host "  Average Reports per Component: $avgReports" -ForegroundColor White
            $topReporterCount = if ($topReporter) { $topReporter.Count } else { 0 }
            Write-Host "  Highest Volume Component: [$($topReporter.Component)] $topReporterCount" -ForegroundColor Yellow
            
            # Performance classification
            $classification = if ($totalReports -lt 50) { "Low Volume" }
                            elseif ($totalReports -lt 200) { "Medium Volume" }
                            else { "High Volume" }
            Write-Host "  Test Classification: $classification" -ForegroundColor Magenta
            
            # Component analysis with recommendations
            $highVolume = $reportData | Where-Object { $_.Count -gt 20 }
            $highVolumeCount = @($highVolume).Length
            if ($highVolumeCount -gt 0) {
                Write-Status "`nHigh Volume Components (>20 reports) - Optimization Recommended:" ([ConsoleColor]::Yellow)
                $highVolume | Sort-Object Count -Descending | ForEach-Object {
                    $recommendation = switch -Regex ($_.Component) {
                        "MONITOR" { "Consider reducing monitor verbosity to UVM_LOW" }
                        "DRIVER" { "Driver reports normal, monitor for patterns" }
                        "SCOREBOARD" { "High activity expected for verification" }
                        "COVERAGE" { "Coverage collection active - normal behavior" }
                        default { "Review component verbosity settings" }
                    }
                    $itemCount = $_.Count
                    Write-Host "  [$($_.Component)] $itemCount - $recommendation" -ForegroundColor Yellow
                }
            }
            
            # Test-specific patterns
            $testSpecific = $reportData | Where-Object { $_.Component -match $TestName -or $_.Component -match "DIAG|DEBUG" }
            $testSpecificCount = @($testSpecific).Length
            if ($testSpecificCount -gt 0) {
                Write-Status "`nTest-Specific Report Categories:" ([ConsoleColor]::Cyan)
                $testSpecific | ForEach-Object {
                    $specificCount = $_.Count
                    Write-Host "  [$($_.Component)] $specificCount" -ForegroundColor Cyan
                }
            }
        }
    }
    
    # Error and warning analysis
    $errorLines = $content -split "`n" | Where-Object { $_ -match "UVM_ERROR" }
    $warningLines = $content -split "`n" | Where-Object { $_ -match "UVM_WARNING" }
    $testMessages = $content -split "`n" | Where-Object { $_ -match "SIMPLE_WRITE_TEST|DEBUG_WRITE_SEQ" }
    $errors = @($errorLines).Length
    $warnings = @($warningLines).Length
    
    if ($errors -gt 0 -or $warnings -gt 0) {
        Write-Status "`n=== QUALITY METRICS ===" ([ConsoleColor]::Red)
        Write-Host "  UVM_ERROR Count: $errors" -ForegroundColor $(if ($errors -gt 0) { [ConsoleColor]::Red } else { [ConsoleColor]::Green })
        Write-Host "  UVM_WARNING Count: $warnings" -ForegroundColor $(if ($warnings -gt 0) { [ConsoleColor]::Yellow } else { [ConsoleColor]::Green })
        
        if ($errors -eq 0 -and $warnings -eq 0) {
            Write-Host "  ✓ TEST PASSED - No errors or warnings detected" -ForegroundColor Green
        } else {
            Write-Host "  ⚠ Review required - Errors/warnings detected" -ForegroundColor Red
        }
    }
    
    # Display test-specific messages if found
    if ($testMessages -and @($testMessages).Length -gt 0) {
        $messageCount = @($testMessages).Length
        Write-Status "`nTest-Specific Messages ($messageCount):" ([ConsoleColor]::Green)
        $testMessages | Select-Object -First 5 | ForEach-Object {
            Write-Host "  $_" -ForegroundColor Cyan
        }
        if ($messageCount -gt 5) {
            Write-Host "  ... and $($messageCount - 5) more messages" -ForegroundColor Gray
        }
    }
    
    Write-Status "=== END ENHANCED REPORT ANALYSIS ===" ([ConsoleColor]::Yellow)
}

function Resolve-RelativePath {
    param([string]$Path, [string]$BasePath)
    if ([System.IO.Path]::IsPathRooted($Path)) {
        return [System.IO.Path]::GetFullPath($Path)
    }
    return [System.IO.Path]::GetFullPath((Join-Path -Path $BasePath -ChildPath $Path))
}

function Test-DsimEnvironment {
    $requiredVars = @("DSIM_HOME", "DSIM_ROOT", "DSIM_LIB_PATH")
    $errors = @()

    foreach ($name in $requiredVars) {
        $value = [Environment]::GetEnvironmentVariable($name)
        if ([string]::IsNullOrWhiteSpace($value)) {
            $errors += "$name is not set."
            continue
        }
        if (-not (Test-Path $value)) {
            $errors += "$name path '$value' does not exist."
        } else {
            Write-Status "$name = $value" ([ConsoleColor]::Cyan)
        }
    }

    $licenseVar = [Environment]::GetEnvironmentVariable('DSIM_LICENSE')
    if ([string]::IsNullOrWhiteSpace($licenseVar)) {
        $defaultLicense = Join-Path $env:USERPROFILE 'AppData\Local\metrics-ca\dsim-license.json'
        if (Test-Path $defaultLicense) {
            Write-Status "DSIM_LICENSE not set. Using detected license: $defaultLicense" ([ConsoleColor]::Yellow)
            $env:DSIM_LICENSE = $defaultLicense
            $licenseVar = $defaultLicense
        } else {
            $errors += "DSIM_LICENSE is not set and default license '$defaultLicense' was not found."
        }
    } elseif (-not (Test-Path $licenseVar)) {
        $errors += "DSIM_LICENSE path '$licenseVar' does not exist."
    } else {
        Write-Status "DSIM_LICENSE found: $licenseVar" ([ConsoleColor]::Cyan)
    }

    $errorCount = @($errors).Length
    if ($errorCount -gt 0) {
        $errors | ForEach-Object { Write-Status $_ ([ConsoleColor]::Red) }
        throw "DSIM environment validation failed."
    }

    $exeCandidates = @(
        (Join-Path (Join-Path $env:DSIM_HOME 'bin') 'dsim.exe'),
        (Join-Path (Join-Path $env:DSIM_HOME 'bin') 'dsim')
    )

    foreach ($candidate in $exeCandidates) {
        if (Test-Path $candidate) {
            Write-Status "Using DSIM executable: $candidate" ([ConsoleColor]::Green)
            return $candidate
        }
    }

    throw "Unable to locate dsim executable under DSIM_HOME."
}

# Get script directory (handle both script execution and interactive mode)
if ($PSCommandPath) {
    $scriptRoot = Split-Path -Parent $PSCommandPath
} else {
    $scriptRoot = Get-Location
}
try {
    $dsimExe = Test-DsimEnvironment

    $configPath = Resolve-RelativePath -Path $ConfigFile -BasePath $scriptRoot
    if (-not (Test-Path $configPath)) {
        throw "Configuration file not found: $configPath"
    }
    Write-Status "Configuration file: $configPath" ([ConsoleColor]::Green)

    $logRoot = Resolve-RelativePath -Path $LogDir -BasePath $scriptRoot
    $waveRoot = Resolve-RelativePath -Path $WaveDir -BasePath $scriptRoot

    foreach ($dir in @($logRoot, $waveRoot)) {
        if (-not (Test-Path $dir)) {
            Write-Status "Creating directory: $dir" ([ConsoleColor]::Yellow)
            New-Item -ItemType Directory -Path $dir -Force | Out-Null
        }
    }

    # Clear old waveform files before new simulation (only if waveforms enabled)
    if ($ClearWaveforms -eq 'on' -and $Waves -eq 'on' -and (Test-Path $waveRoot)) {
        try {
            $oldWaveforms = @(Get-ChildItem -Path $waveRoot -Filter "*.mxd" -ErrorAction SilentlyContinue)
            $waveformCount = @($oldWaveforms).Length
            if ($oldWaveforms -and $waveformCount -gt 0) {
                Write-Status "Clearing $waveformCount old waveform files from $waveRoot" ([ConsoleColor]::Yellow)
                $oldWaveforms | ForEach-Object {
                    if ($_ -and $_.Name) {
                        try {
                            Remove-Item $_.FullName -Force -ErrorAction Stop
                            Write-Status "  Removed: $($_.Name)" ([ConsoleColor]::DarkGray)
                        } catch {
                            Write-Status "  Warning: Failed to remove $($_.Name): $($_.Exception.Message)" ([ConsoleColor]::DarkYellow)
                        }
                    }
                }
            } else {
                Write-Status "No old waveform files to clear in $waveRoot" ([ConsoleColor]::DarkGray)
            }
        } catch {
            Write-Status "Warning: Error accessing waveform directory: $($_.Exception.Message)" ([ConsoleColor]::DarkYellow)
        }
    } elseif ($ClearWaveforms -eq 'off') {
        Write-Status "Waveform clearing disabled" ([ConsoleColor]::DarkGray)
    }

    $timestamp = Get-Date -Format 'yyyyMMdd_HHmmss'
    $logFile = Join-Path $logRoot ("{0}_{1}.log" -f $TestName, $timestamp)
    $waveFile = Join-Path $waveRoot ("{0}_{1}.mxd" -f $TestName, $timestamp)
    $metricsFile = if ([System.IO.Path]::IsPathRooted($MetricsDb)) { $MetricsDb } else { Join-Path $scriptRoot $MetricsDb }
    $coverageDir = Join-Path $scriptRoot 'coverage_report'

    Write-Status "Mode: $Mode" ([ConsoleColor]::Green)
    Write-Status "Test: $TestName" ([ConsoleColor]::Green)
    Write-Status "Verbosity: $Verbosity" ([ConsoleColor]::Green)
    Write-Status "Seed: $Seed" ([ConsoleColor]::Green)
    Write-Status "Log file: $logFile" ([ConsoleColor]::Green)

    $dsimArgs = @('-f', $configPath, "+UVM_TESTNAME=$TestName")
    $dsimArgs += "+UVM_VERBOSITY=$Verbosity"
    $dsimArgs += '-sv_seed', $Seed.ToString()
    $dsimArgs += '-l', $logFile

    # Enhanced reporting configuration
    if ($DetailedReporting) {
        $dsimArgs += '+UVM_REPORT_DETAILED=1'
        $dsimArgs += '+define+ENHANCED_REPORTING'
        Write-Status "Enhanced UVM reporting enabled" ([ConsoleColor]::Green)
    }
    
    if ($ReportFilter -ne 'ALL') {
        $dsimArgs += "+UVM_REPORT_FILTER=$ReportFilter"
        Write-Status "Report filter: $ReportFilter" ([ConsoleColor]::Cyan)
    }

    if ($Mode -eq 'compile') {
        $dsimArgs += '-compile'
        Write-Status "Compile-only mode enabled" ([ConsoleColor]::Yellow)
    }

    if ($Waves -eq 'on') {
        $dsimArgs += '+access+rwb', '-waves', $waveFile, '+define+WAVES'
        Write-Status "Waveform capture enabled: $waveFile" ([ConsoleColor]::Green)
    } else {
        Write-Status "Waveform capture disabled (use -Waves on to enable for debugging)" ([ConsoleColor]::Cyan)
    }

    if ($Coverage -eq 'on' -and $Mode -eq 'run') {
        $coverageScope = Join-Path (Split-Path -Parent $configPath) 'coverage_scope.specs'
        $dsimArgs += '-code-cov', 'all'
        if (Test-Path $coverageScope) {
            $dsimArgs += '-code-cov-scope-specs', $coverageScope
        } else {
            Write-Status "coverage_scope.specs not found; proceeding without scope filtering" ([ConsoleColor]::Yellow)
        }
        $dsimArgs += '-cov-db', $metricsFile, '+define+ENABLE_COVERAGE'
        Write-Status "Coverage enabled: $metricsFile" ([ConsoleColor]::Green)
    } else {
        Write-Status "Coverage disabled" ([ConsoleColor]::Yellow)
    }

    $extraArgCount = @($ExtraArgs).Length
    if ($extraArgCount -gt 0) {
        Write-Status "Extra arguments: $($ExtraArgs -join ' ')" ([ConsoleColor]::Yellow)
        $dsimArgs += $ExtraArgs
    }

    Write-Status "Starting DSIM..." ([ConsoleColor]::Cyan)
    Write-Status "$dsimExe $($dsimArgs -join ' ')" ([ConsoleColor]::DarkGray)

    $startTime = Get-Date
    $configDir = Split-Path -Parent $configPath
    Push-Location $configDir
    try {
        & $dsimExe @dsimArgs
        $exitCode = $LASTEXITCODE
    }
    finally {
        Pop-Location
    }
    $duration = (Get-Date) - $startTime

    Write-Status "DSIM finished in $($duration.ToString('hh\:mm\:ss\.ff'))" ([ConsoleColor]::Cyan)

    if ($exitCode -ne 0) {
        Write-Status "Simulation failed with exit code $exitCode" ([ConsoleColor]::Red)
        exit $exitCode
    }

    Write-Status "Simulation completed successfully" ([ConsoleColor]::Green)

    if (Test-Path $logFile) {
        $logContent = Get-Content $logFile -Raw
        if ($logContent -match 'UVM_ERROR\s*:\s*(\d+)') {
            $uvmError = [int]$Matches[1]
            if ($uvmError -eq 0) {
                Write-Status "UVM_ERROR = 0" ([ConsoleColor]::Green)
            } else {
                Write-Status "UVM_ERROR = $uvmError" ([ConsoleColor]::Red)
            }
        }
    }

    if ($Coverage -eq 'on' -and $Mode -eq 'run' -and (Test-Path $metricsFile)) {
        if (-not (Test-Path $coverageDir)) {
            New-Item -ItemType Directory -Path $coverageDir -Force | Out-Null
        }
        Write-Status "Generating coverage report..." ([ConsoleColor]::Cyan)
        $dcreportExe = Join-Path (Join-Path $env:DSIM_HOME 'bin') 'dcreport.exe'
        & $dcreportExe $metricsFile '-out_dir' $coverageDir
        Write-Status "Coverage report generated at $coverageDir" ([ConsoleColor]::Green)
    }

    if ($Waves -eq 'on' -and $Mode -eq 'run' -and (Test-Path $waveFile)) {
        Write-Status "Waveform available: $waveFile" ([ConsoleColor]::Green)
    } elseif ($Waves -eq 'off') {
        Write-Status "Waveform generation disabled (use -Waves on if debugging needed)" ([ConsoleColor]::Cyan)
    }

    # MANDATORY: Enhanced Report Analysis (Default Enabled per October 10, 2025 Standards)
    if ($ReportAnalysis -and (Test-Path $logFile)) {
        Write-Status "Executing mandatory UVM report analysis..." ([ConsoleColor]::Cyan)
        Analyze-UVMReports -LogFile $logFile -TestName $TestName
    } elseif (-not (Test-Path $logFile)) {
        Write-Status "Warning: Log file not found for analysis. Check simulation execution." ([ConsoleColor]::Red)
    }
    
    # Final compliance check
    Write-Status "=== ENHANCED UVM EXECUTION COMPLETE ===" ([ConsoleColor]::Green)
    if ($ReportAnalysis) {
        Write-Status "✓ Enhanced reporting analysis completed per October 10, 2025 standards" ([ConsoleColor]::Green)
    } else {
        Write-Status "⚠ Enhanced reporting analysis was disabled (not recommended)" ([ConsoleColor]::Yellow)
    }
} catch {
    Write-Status "Error: $($_.Exception.Message)" ([ConsoleColor]::Red)
    exit 1
}

exit 0