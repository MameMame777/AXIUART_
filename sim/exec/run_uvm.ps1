#!/usr/bin/env pwsh

# Advanced DSIM UVM runner aligned with comprehensive work instructions
[CmdletBinding()]
param(
    [ValidateSet("run", "compile")]
    [string]$Mode = "run",

    [string]$TestName = "uart_axi4_basic_test",

    [ValidateSet("UVM_NONE", "UVM_LOW", "UVM_MEDIUM", "UVM_HIGH", "UVM_FULL")]
    [string]$Verbosity = "UVM_MEDIUM",

    [int]$Seed = 1,

    [ValidateSet("on", "off")]
    [string]$Waves = "on",

    [ValidateSet("on", "off")]
    [string]$Coverage = "on",

    [string]$LogDir = "logs",

    [string]$WaveDir = "..\\..\\archive\\waveforms",

    [string]$MetricsDb = "metrics.db",

    [string]$ConfigFile = "..\\uvm\\dsim_config.f",

    [string[]]$ExtraArgs = @()
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

function Write-Status {
    param(
        [string]$Message,
        [ConsoleColor]$Color = [ConsoleColor]::White
    )
    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    Write-Host "[$timestamp] $Message" -ForegroundColor $Color
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

    if ($errors.Count -gt 0) {
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

$scriptRoot = Split-Path -Parent $PSCommandPath
Push-Location $scriptRoot
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

    if ($Mode -eq 'compile') {
        $dsimArgs += '-compile'
        Write-Status "Compile-only mode enabled" ([ConsoleColor]::Yellow)
    }

    if ($Waves -eq 'on') {
        $dsimArgs += '+access+rwb', '-waves', $waveFile, '+define+WAVES'
        Write-Status "Waveform capture enabled: $waveFile" ([ConsoleColor]::Green)
    } else {
        Write-Status "Waveform capture disabled" ([ConsoleColor]::Yellow)
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

    if ($ExtraArgs.Count -gt 0) {
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
    }
}
finally {
    Pop-Location
}

exit 0