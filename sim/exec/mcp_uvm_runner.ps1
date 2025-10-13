#!/usr/bin/env pwsh

# MCP Server Optimized DSIM UVM Runner
# Compliance: UVM Verification Quality Assurance Instructions (October 10, 2025)
# Optimized for MCP server run_in_terminal functionality
[CmdletBinding()]
param(
    [ValidateSet("run", "compile")]
    [string]$Mode = "run",

    [string]$TestName = "uart_axi4_basic_test",

    [ValidateSet("UVM_NONE", "UVM_LOW", "UVM_MEDIUM", "UVM_HIGH", "UVM_FULL")]
    [string]$Verbosity = "UVM_MEDIUM",

    [int]$Seed = 1,

    [ValidateSet("on", "off")]
    [string]$Waves = "off",  # Default disabled per user request

    [ValidateSet("on", "off")]
    [string]$Coverage = "on",

    [ValidateSet("on", "off")]
    [string]$ClearWaveforms = "on",

    [string]$LogDir = "logs",

    [string]$WaveDir = "..\\..\\archive\\waveforms",

    [string]$MetricsDb = "metrics.db",

    [string]$ConfigFile = "..\\uvm\\dsim_config.f",

    # MCP Server Optimized: Enhanced reporting parameters
    [switch]$ReportAnalysis = $true,  # DEFAULT ENABLED per guidelines
    [switch]$DetailedReporting = $false,
    [string]$ReportFilter = "ALL",
    [switch]$MCPOptimized = $true,    # MCP-specific optimizations

    [string[]]$ExtraArgs = @()
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

# MCP Server utility functions
function Write-MCPStatus {
    param(
        [string]$Message,
        [ConsoleColor]$Color = [ConsoleColor]::White
    )
    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    Write-Host "[$timestamp] [MCP-UVM] $Message" -ForegroundColor $Color
}

function Write-MCPSection {
    param(
        [string]$Title,
        [ConsoleColor]$Color = [ConsoleColor]::Cyan
    )
    $separator = "=" * 60
    Write-Host $separator -ForegroundColor $Color
    Write-Host "MCP-UVM: $Title" -ForegroundColor $Color
    Write-Host $separator -ForegroundColor $Color
}

# Enhanced reporting for MCP environment
if ($ReportAnalysis) {
    Write-MCPStatus "Enhanced UVM report analysis enabled (MCP Optimized)" ([ConsoleColor]::Green)
}

function Analyze-UVMReports-MCP {
    param(
        [string]$LogFile,
        [string]$TestName
    )
    
    Write-MCPSection "UVM ENHANCED REPORT ANALYSIS (MCP Optimized)" ([ConsoleColor]::Yellow)
    
    if (-not (Test-Path $LogFile)) {
        Write-MCPStatus "Warning: Log file '$LogFile' not found. Skipping analysis." ([ConsoleColor]::Red)
        return
    }
    
    # Read log content
    $content = Get-Content $LogFile -Raw
    
    # Extract report counts by severity with MCP formatting
    if ($content -match '\*\* Report counts by severity\s+(.*?)\*\* Report counts by id') {
        $severitySection = $Matches[1]
        Write-MCPStatus "Report Counts by Severity:" ([ConsoleColor]::Green)
        $severitySection -split "`n" | Where-Object { $_ -match '^\s*UVM_' } | ForEach-Object {
            $line = $_.Trim()
            if ($line -match 'UVM_ERROR') {
                Write-Host "  [MCP] $line" -ForegroundColor Red
            } elseif ($line -match 'UVM_WARNING') {
                Write-Host "  [MCP] $line" -ForegroundColor Yellow
            } else {
                Write-Host "  [MCP] $line" -ForegroundColor White
            }
        }
    }
    
    # Enhanced report counts by ID analysis with MCP formatting
    if ($content -match '\*\* Report counts by id\s+(.*?)\n\n') {
        $idSection = $Matches[1]
        Write-MCPStatus "Report Counts by ID (Component Analysis):" ([ConsoleColor]::Green)
        
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
                
                # Color coding based on volume for MCP
                $color = if ($count -gt 50) { [ConsoleColor]::Red } 
                        elseif ($count -gt 20) { [ConsoleColor]::Yellow } 
                        elseif ($count -gt 10) { [ConsoleColor]::Cyan } 
                        else { [ConsoleColor]::White }
                        
                Write-Host "  [MCP] [$component] $count $comment" -ForegroundColor $color
            }
        }
        
        # Enhanced summary statistics for MCP
        if ($reportData -and $reportData.Length -gt 0) {
            $totalReports = ($reportData | Measure-Object -Property Count -Sum).Sum
            $topReporter = $reportData | Sort-Object Count -Descending | Select-Object -First 1
            $componentCount = @($reportData).Length
            $avgReports = [math]::Round($totalReports / $componentCount, 1)
            
            Write-MCPSection "ENHANCED REPORT SUMMARY for $TestName" ([ConsoleColor]::Green)
            Write-Host "  [MCP] Total Reports Generated: $totalReports" -ForegroundColor White
            Write-Host "  [MCP] Active Components: $componentCount" -ForegroundColor White
            Write-Host "  [MCP] Average Reports per Component: $avgReports" -ForegroundColor White
            $topReporterCount = if ($topReporter) { $topReporter.Count } else { 0 }
            Write-Host "  [MCP] Highest Volume Component: [$($topReporter.Component)] $topReporterCount" -ForegroundColor Yellow
            
            # Performance classification
            $classification = if ($totalReports -lt 50) { "Low Volume" }
                            elseif ($totalReports -lt 200) { "Medium Volume" }
                            else { "High Volume" }
            Write-Host "  [MCP] Test Classification: $classification" -ForegroundColor Magenta
        }
    }
    
    # Error and warning analysis for MCP
    $errorLines = $content -split "`n" | Where-Object { $_ -match "UVM_ERROR" }
    $warningLines = $content -split "`n" | Where-Object { $_ -match "UVM_WARNING" }
    $errors = @($errorLines).Length
    $warnings = @($warningLines).Length
    
    if ($errors -gt 0 -or $warnings -gt 0) {
        Write-MCPSection "QUALITY METRICS" ([ConsoleColor]::Red)
        Write-Host "  [MCP] UVM_ERROR Count: $errors" -ForegroundColor $(if ($errors -gt 0) { [ConsoleColor]::Red } else { [ConsoleColor]::Green })
        Write-Host "  [MCP] UVM_WARNING Count: $warnings" -ForegroundColor $(if ($warnings -gt 0) { [ConsoleColor]::Yellow } else { [ConsoleColor]::Green })
        
        if ($errors -eq 0 -and $warnings -eq 0) {
            Write-Host "  [MCP] ✓ TEST PASSED - No errors or warnings detected" -ForegroundColor Green
        } else {
            Write-Host "  [MCP] ⚠ Review required - Errors/warnings detected" -ForegroundColor Red
        }
    }
    
    Write-MCPSection "END ENHANCED REPORT ANALYSIS" ([ConsoleColor]::Yellow)
}

function Resolve-RelativePath-MCP {
    param([string]$Path, [string]$BasePath)
    if ([System.IO.Path]::IsPathRooted($Path)) {
        return [System.IO.Path]::GetFullPath($Path)
    }
    return [System.IO.Path]::GetFullPath((Join-Path -Path $BasePath -ChildPath $Path))
}

function Test-DsimEnvironment-MCP {
    Write-MCPSection "DSIM ENVIRONMENT VALIDATION (MCP Optimized)" ([ConsoleColor]::Cyan)
    
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
            Write-MCPStatus "$name = $value" ([ConsoleColor]::Cyan)
        }
    }

    # License validation with MCP optimization
    $licenseVar = [Environment]::GetEnvironmentVariable('DSIM_LICENSE')
    if ([string]::IsNullOrWhiteSpace($licenseVar)) {
        $defaultLicense = Join-Path $env:USERPROFILE 'AppData\Local\metrics-ca\dsim-license.json'
        if (Test-Path $defaultLicense) {
            Write-MCPStatus "DSIM_LICENSE not set. Using detected license: $defaultLicense" ([ConsoleColor]::Yellow)
            $env:DSIM_LICENSE = $defaultLicense
            $licenseVar = $defaultLicense
        } else {
            $errors += "DSIM_LICENSE is not set and default license '$defaultLicense' was not found."
        }
    } elseif (-not (Test-Path $licenseVar)) {
        $errors += "DSIM_LICENSE path '$licenseVar' does not exist."
    } else {
        Write-MCPStatus "DSIM_LICENSE found: $licenseVar" ([ConsoleColor]::Cyan)
    }

    $errorCount = @($errors).Length
    if ($errorCount -gt 0) {
        $errors | ForEach-Object { Write-MCPStatus $_ ([ConsoleColor]::Red) }
        throw "DSIM environment validation failed."
    }

    # Executable validation with MCP optimization
    $exeCandidates = @(
        (Join-Path (Join-Path $env:DSIM_HOME 'bin') 'dsim.exe'),
        (Join-Path (Join-Path $env:DSIM_HOME 'bin') 'dsim')
    )

    foreach ($candidate in $exeCandidates) {
        if (Test-Path $candidate) {
            Write-MCPStatus "Using DSIM executable: $candidate" ([ConsoleColor]::Green)
            return $candidate
        }
    }

    throw "Unable to locate dsim executable under DSIM_HOME."
}

# Get script directory (MCP optimized)
if ($PSCommandPath) {
    $scriptRoot = Split-Path -Parent $PSCommandPath
} else {
    $scriptRoot = Get-Location
}

# Main execution block with MCP optimization
try {
    Write-MCPSection "MCP-OPTIMIZED UVM SIMULATION STARTING" ([ConsoleColor]::Green)
    
    $dsimExe = Test-DsimEnvironment-MCP

    $configPath = Resolve-RelativePath-MCP -Path $ConfigFile -BasePath $scriptRoot
    if (-not (Test-Path $configPath)) {
        throw "Configuration file not found: $configPath"
    }
    Write-MCPStatus "Configuration file: $configPath" ([ConsoleColor]::Green)

    $logRoot = Resolve-RelativePath-MCP -Path $LogDir -BasePath $scriptRoot
    $waveRoot = Resolve-RelativePath-MCP -Path $WaveDir -BasePath $scriptRoot

    foreach ($dir in @($logRoot, $waveRoot)) {
        if (-not (Test-Path $dir)) {
            Write-MCPStatus "Creating directory: $dir" ([ConsoleColor]::Yellow)
            New-Item -ItemType Directory -Path $dir -Force | Out-Null
        }
    }

    # MCP-optimized waveform cleanup
    if ($ClearWaveforms -eq 'on' -and $Waves -eq 'on' -and (Test-Path $waveRoot)) {
        try {
            $oldWaveforms = @(Get-ChildItem -Path $waveRoot -Filter "*.mxd" -ErrorAction SilentlyContinue)
            $waveformCount = @($oldWaveforms).Length
            if ($oldWaveforms -and $waveformCount -gt 0) {
                Write-MCPStatus "Clearing $waveformCount old waveform files from $waveRoot" ([ConsoleColor]::Yellow)
                $oldWaveforms | ForEach-Object {
                    if ($_ -and $_.Name) {
                        try {
                            Remove-Item $_.FullName -Force -ErrorAction Stop
                            Write-MCPStatus "  Removed: $($_.Name)" ([ConsoleColor]::DarkGray)
                        } catch {
                            Write-MCPStatus "  Warning: Failed to remove $($_.Name): $($_.Exception.Message)" ([ConsoleColor]::DarkYellow)
                        }
                    }
                }
            } else {
                Write-MCPStatus "No old waveform files to clear in $waveRoot" ([ConsoleColor]::DarkGray)
            }
        } catch {
            Write-MCPStatus "Warning: Error accessing waveform directory: $($_.Exception.Message)" ([ConsoleColor]::DarkYellow)
        }
    }

    # File naming with timestamp
    $timestamp = Get-Date -Format 'yyyyMMdd_HHmmss'
    $logFile = Join-Path $logRoot ("{0}_{1}.log" -f $TestName, $timestamp)
    $waveFile = Join-Path $waveRoot ("{0}_{1}.mxd" -f $TestName, $timestamp)
    $metricsFile = if ([System.IO.Path]::IsPathRooted($MetricsDb)) { $MetricsDb } else { Join-Path $scriptRoot $MetricsDb }
    $coverageDir = Join-Path $scriptRoot 'coverage_report'

    # Display MCP-optimized configuration
    Write-MCPSection "SIMULATION CONFIGURATION" ([ConsoleColor]::Green)
    Write-MCPStatus "Mode: $Mode" ([ConsoleColor]::Green)
    Write-MCPStatus "Test: $TestName" ([ConsoleColor]::Green)
    Write-MCPStatus "Verbosity: $Verbosity" ([ConsoleColor]::Green)
    Write-MCPStatus "Seed: $Seed" ([ConsoleColor]::Green)
    Write-MCPStatus "Log file: $logFile" ([ConsoleColor]::Green)
    Write-MCPStatus "MCP Optimized: $MCPOptimized" ([ConsoleColor]::Magenta)

    # Build DSIM arguments
    $dsimArgs = @('-f', $configPath, "+UVM_TESTNAME=$TestName")
    $dsimArgs += "+UVM_VERBOSITY=$Verbosity"
    $dsimArgs += '-sv_seed', $Seed.ToString()
    $dsimArgs += '-l', $logFile

    # Enhanced reporting configuration for MCP
    if ($DetailedReporting) {
        $dsimArgs += '+UVM_REPORT_DETAILED=1'
        $dsimArgs += '+define+ENHANCED_REPORTING'
        Write-MCPStatus "Enhanced UVM reporting enabled" ([ConsoleColor]::Green)
    }
    
    if ($ReportFilter -ne 'ALL') {
        $dsimArgs += "+UVM_REPORT_FILTER=$ReportFilter"
        Write-MCPStatus "Report filter: $ReportFilter" ([ConsoleColor]::Cyan)
    }

    if ($Mode -eq 'compile') {
        $dsimArgs += '-genimage', 'compiled_image'
        Write-MCPStatus "Compile-only mode enabled (using -genimage)" ([ConsoleColor]::Yellow)
    }

    # MCP-optimized waveform configuration (default enabled)
    if ($Waves -eq 'on') {
        $dsimArgs += '+acc+b', '-waves', $waveFile, '+define+WAVES'
        Write-MCPStatus "Waveform capture enabled: $waveFile" ([ConsoleColor]::Green)
    } else {
        Write-MCPStatus "Waveform capture disabled" ([ConsoleColor]::Cyan)
    }

    # Coverage configuration
    if ($Coverage -eq 'on' -and $Mode -eq 'run') {
        $coverageScope = Join-Path (Split-Path -Parent $configPath) 'coverage_scope.specs'
        $dsimArgs += '-code-cov', 'all'
        if (Test-Path $coverageScope) {
            $dsimArgs += '-code-cov-scope-specs', $coverageScope
        } else {
            Write-MCPStatus "coverage_scope.specs not found; proceeding without scope filtering" ([ConsoleColor]::Yellow)
        }
        $dsimArgs += '-cov-db', $metricsFile, '+define+ENABLE_COVERAGE'
        Write-MCPStatus "Coverage enabled: $metricsFile" ([ConsoleColor]::Green)
    } else {
        Write-MCPStatus "Coverage disabled" ([ConsoleColor]::Yellow)
    }

    # Extra arguments
    $extraArgCount = @($ExtraArgs).Length
    if ($extraArgCount -gt 0) {
        Write-MCPStatus "Extra arguments: $($ExtraArgs -join ' ')" ([ConsoleColor]::Yellow)
        $dsimArgs += $ExtraArgs
    }

    # Execute simulation
    Write-MCPSection "DSIM SIMULATION EXECUTION" ([ConsoleColor]::Cyan)
    Write-MCPStatus "$dsimExe $($dsimArgs -join ' ')" ([ConsoleColor]::DarkGray)

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

    Write-MCPStatus "DSIM finished in $($duration.ToString('hh\:mm\:ss\.ff'))" ([ConsoleColor]::Cyan)

    if ($exitCode -ne 0) {
        Write-MCPStatus "Simulation failed with exit code $exitCode" ([ConsoleColor]::Red)
        exit $exitCode
    }

    Write-MCPStatus "Simulation completed successfully" ([ConsoleColor]::Green)

    # Parse UVM results
    if (Test-Path $logFile) {
        $logContent = Get-Content $logFile -Raw
        if ($logContent -match 'UVM_ERROR\s*:\s*(\d+)') {
            $uvmError = [int]$Matches[1]
            if ($uvmError -eq 0) {
                Write-MCPStatus "UVM_ERROR = 0" ([ConsoleColor]::Green)
            } else {
                Write-MCPStatus "UVM_ERROR = $uvmError" ([ConsoleColor]::Red)
            }
        }
    }

    # Coverage report generation
    if ($Coverage -eq 'on' -and $Mode -eq 'run' -and (Test-Path $metricsFile)) {
        if (-not (Test-Path $coverageDir)) {
            New-Item -ItemType Directory -Path $coverageDir -Force | Out-Null
        }
        Write-MCPStatus "Generating coverage report..." ([ConsoleColor]::Cyan)
        $dcreportExe = Join-Path (Join-Path $env:DSIM_HOME 'bin') 'dcreport.exe'
        & $dcreportExe $metricsFile '-out_dir' $coverageDir
        Write-MCPStatus "Coverage report generated at $coverageDir" ([ConsoleColor]::Green)
    }

    # Waveform status
    if ($Waves -eq 'on' -and $Mode -eq 'run' -and (Test-Path $waveFile)) {
        Write-MCPStatus "Waveform available: $waveFile" ([ConsoleColor]::Green)
    }

    # MANDATORY: Enhanced Report Analysis (MCP Optimized)
    if ($ReportAnalysis -and (Test-Path $logFile)) {
        Write-MCPStatus "Executing mandatory UVM report analysis (MCP Optimized)..." ([ConsoleColor]::Cyan)
        Analyze-UVMReports-MCP -LogFile $logFile -TestName $TestName
    } elseif (-not (Test-Path $logFile)) {
        Write-MCPStatus "Warning: Log file not found for analysis. Check simulation execution." ([ConsoleColor]::Red)
    }
    
    # Final compliance check
    Write-MCPSection "MCP-OPTIMIZED UVM EXECUTION COMPLETE" ([ConsoleColor]::Green)
    if ($ReportAnalysis) {
        Write-MCPStatus "✓ Enhanced reporting analysis completed (MCP Optimized)" ([ConsoleColor]::Green)
    } else {
        Write-MCPStatus "⚠ Enhanced reporting analysis was disabled (not recommended)" ([ConsoleColor]::Yellow)
    }
    
    # MCP-specific final status
    Write-MCPStatus "✓ MCP server execution completed successfully" ([ConsoleColor]::Green)
    Write-MCPStatus "Log: $logFile" ([ConsoleColor]::Cyan)
    if ($Waves -eq 'on') {
        Write-MCPStatus "Waveform: $waveFile" ([ConsoleColor]::Cyan)
    }
    
} catch {
    Write-MCPStatus "Error: $($_.Exception.Message)" ([ConsoleColor]::Red)
    exit 1
}

exit 0