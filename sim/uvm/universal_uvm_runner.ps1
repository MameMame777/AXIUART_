# Universal UVM Runner - Reusable across multiple projects
# This script provides a standardized interface for running UVM tests with DSIM
# Usage: .\universal_uvm_runner.ps1 -ConfigFile <config.f> [other options]

param(
    [Parameter(Mandatory=$true)]
    [string]$ConfigFile,
    
    [string]$TestName = "base_test",
    [string]$TopModule = "tb_top", 
    [int]$Seed = 1,
    [string]$Verbosity = "UVM_MEDIUM",
    [switch]$Waves = $false,
    [switch]$Coverage = $false,
    [switch]$CleanFirst = $false,
    [switch]$CompileOnly = $false,
    [string]$LogFile = "",
    [string]$WorkLib = "work",
    [string]$ExtraDefines = "",
    [string]$ExtraArgs = "",
    [int]$TimeoutMinutes = 30
)

# Configuration and globals
$script:DSIM_EXE = ""
$script:START_TIME = Get-Date

# Enhanced logging functions with timestamps
function Write-Log {
    param(
        [string]$Message,
        [string]$Level = "INFO",
        [ConsoleColor]$Color = [ConsoleColor]::White
    )
    
    $timestamp = Get-Date -Format "HH:mm:ss.fff"
    $formatted = "[$timestamp][$Level] $Message"
    Write-Host $formatted -ForegroundColor $Color
}

function Write-Success { param([string]$Message) Write-Log $Message "SUCCESS" Green }
function Write-Warning { param([string]$Message) Write-Log $Message "WARNING" Yellow }
function Write-Error { param([string]$Message) Write-Log $Message "ERROR" Red }
function Write-Info { param([string]$Message) Write-Log $Message "INFO" Cyan }
function Write-Debug { param([string]$Message) Write-Log $Message "DEBUG" DarkGray }

# Enhanced environment validation
function Test-DSIMEnvironment {
    Write-Info "Validating DSIM environment..."
    
    # Check required environment variables
    $required_vars = @{
        "DSIM_HOME" = "DSIM installation directory"
        "DSIM_ROOT" = "DSIM root directory (usually same as DSIM_HOME)"
    }
    
    $missing_vars = @()
    
    foreach ($var in $required_vars.Keys) {
        $value = [Environment]::GetEnvironmentVariable($var)
        if ([string]::IsNullOrEmpty($value)) {
            $missing_vars += $var
            Write-Error "$var is not set - $($required_vars[$var])"
        } else {
            Write-Success "$var = $value"
            
            # Verify path exists
            if (-not (Test-Path $value)) {
                Write-Warning "Path $value does not exist for $var"
            }
        }
    }
    
    if ($missing_vars.Count -gt 0) {
        Write-Error "Missing environment variables: $($missing_vars -join ', ')"
        Write-Info "Please set these variables before running:"
        Write-Info "  set DSIM_HOME=C:\path\to\dsim\installation"
        Write-Info "  set DSIM_ROOT=%DSIM_HOME%"
        throw "Environment validation failed"
    }
    
    # Locate DSIM executable
    $possible_paths = @(
        (Join-Path $env:DSIM_HOME "bin\dsim.exe"),
        (Join-Path $env:DSIM_HOME "bin\dsim"),
        (Join-Path $env:DSIM_ROOT "bin\dsim.exe"),
        (Join-Path $env:DSIM_ROOT "bin\dsim")
    )
    
    foreach ($path in $possible_paths) {
        if (Test-Path $path) {
            $script:DSIM_EXE = $path
            Write-Success "Found DSIM executable: $path"
            break
        }
    }
    
    if ([string]::IsNullOrEmpty($script:DSIM_EXE)) {
        Write-Error "DSIM executable not found in any expected location"
        Write-Info "Searched paths:"
        foreach ($path in $possible_paths) {
            Write-Info "  $path"
        }
        throw "DSIM executable not found"
    }
    
    # Test DSIM version
    try {
        $version_output = & $script:DSIM_EXE -version 2>&1
        Write-Info "DSIM version: $($version_output | Select-Object -First 1)"
    }
    catch {
        Write-Warning "Could not retrieve DSIM version: $_"
    }
    
    Write-Success "DSIM environment validation passed"
}

# Enhanced artifact cleanup
function Clean-Artifacts {
    Write-Info "Cleaning simulation artifacts..."
    
    $artifacts = @(
        # Log files
        "dsim.log", "transcript", "*.log",
        
        # Waveform files  
        "*.mxd", "*.vcd", "*.wlf", "*.fsdb",
        
        # Coverage files
        "coverage.db", "metrics.db", "*.cov", "cov_work",
        
        # Work libraries
        "work", "dsim_work", $WorkLib,
        
        # Temporary files
        "*.tmp", ".coverage", "vsim.wlf"
    )
    
    $cleaned_count = 0
    foreach ($pattern in $artifacts) {
        $items = Get-ChildItem -Path $pattern -ErrorAction SilentlyContinue
        foreach ($item in $items) {
            try {
                Remove-Item $item.FullName -Recurse -Force
                Write-Debug "Removed: $($item.Name)"
                $cleaned_count++
            }
            catch {
                Write-Warning "Could not remove $($item.Name): $_"
            }
        }
    }
    
    Write-Success "Cleaned $cleaned_count artifacts"
}

# Validate configuration file
function Test-ConfigurationFile {
    param([string]$ConfigPath)
    
    if (-not (Test-Path $ConfigPath)) {
        throw "Configuration file not found: $ConfigPath"
    }
    
    Write-Success "Configuration file found: $ConfigPath"
    
    # Parse config file for basic validation
    $content = Get-Content $ConfigPath
    $file_count = 0
    $missing_files = @()
    
    foreach ($line in $content) {
        $line = $line.Trim()
        if ($line.StartsWith("#") -or [string]::IsNullOrEmpty($line) -or $line.StartsWith("+") -or $line.StartsWith("-")) {
            continue
        }
        
        # Assume it's a file path
        $file_path = $line
        if (-not (Test-Path $file_path)) {
            $missing_files += $file_path
        } else {
            $file_count++
        }
    }
    
    Write-Info "Found $file_count source files"
    
    if ($missing_files.Count -gt 0) {
        Write-Warning "$($missing_files.Count) files not found:"
        foreach ($file in $missing_files | Select-Object -First 5) {
            Write-Warning "  $file"
        }
        if ($missing_files.Count -gt 5) {
            Write-Warning "  ... and $($missing_files.Count - 5) more"
        }
    }
}

# Build comprehensive argument list
function Build-SimulationArguments {
    Write-Info "Building simulation arguments..."
    
    $args = @()
    
    # Configuration file
    $args += "-f", $ConfigFile
    
    # Work library
    $args += "-work", $WorkLib
    
    # Top module
    $args += "-top", $TopModule
    
    # UVM test configuration
    $args += "+UVM_TESTNAME=$TestName"
    $args += "+UVM_VERBOSITY=$Verbosity"
    $args += "+UVM_CONFIG_DB_TRACE"
    $args += "+UVM_OBJECTION_TRACE"
    
    # Seed
    $args += "-sv_seed", $Seed.ToString()
    
    # Compilation mode
    if ($CompileOnly) {
        $args += "-compile"
        Write-Info "Compile-only mode enabled"
    }
    
    # Waveform generation
    if ($Waves) {
        $timestamp = Get-Date -Format "yyyyMMdd_HHmmss"
        $wave_file = "${TestName}_${timestamp}.mxd"
        $args += "-waves", $wave_file
        $args += "+define+WAVES"
        Write-Info "Waveforms will be saved to: $wave_file"
    }
    
    # Coverage collection
    if ($Coverage) {
        $cov_db = "coverage_${TestName}_$(Get-Date -Format 'yyyyMMdd_HHmmss').db"
        $args += "+define+ENABLE_COVERAGE"
        $args += "-cover", "all"
        $args += "-coverdb", $cov_db
        Write-Info "Coverage database: $cov_db"
    }
    
    # Debug access
    $args += "+access+r"
    
    # Extra defines
    if (-not [string]::IsNullOrEmpty($ExtraDefines)) {
        foreach ($define in $ExtraDefines.Split(',')) {
            $args += "+define+$($define.Trim())"
        }
        Write-Info "Extra defines: $ExtraDefines"
    }
    
    # Extra arguments
    if (-not [string]::IsNullOrEmpty($ExtraArgs)) {
        $extra_array = $ExtraArgs.Split(' ') | Where-Object { $_ -ne '' }
        $args += $extra_array
        Write-Info "Extra arguments: $ExtraArgs"
    }
    
    # Log file
    if (-not [string]::IsNullOrEmpty($LogFile)) {
        $args += "-logfile", $LogFile
    }
    
    Write-Debug "Final arguments: $($args -join ' ')"
    return $args
}

# Execute simulation with timeout and monitoring
function Start-SimulationWithMonitoring {
    param([string[]]$Arguments)
    
    Write-Info "Starting DSIM simulation..."
    Write-Info "Command: $script:DSIM_EXE $($Arguments -join ' ')"
    
    $simulation_start = Get-Date
    $process = $null
    
    try {
        # Start process with timeout
        $psi = New-Object System.Diagnostics.ProcessStartInfo
        $psi.FileName = $script:DSIM_EXE
        $psi.Arguments = $Arguments -join ' '
        $psi.UseShellExecute = $false
        $psi.RedirectStandardOutput = $true
        $psi.RedirectStandardError = $true
        
        $process = [System.Diagnostics.Process]::Start($psi)
        
        # Monitor with timeout
        $timeout_ms = $TimeoutMinutes * 60 * 1000
        if ($process.WaitForExit($timeout_ms)) {
            $exit_code = $process.ExitCode
        } else {
            Write-Error "Simulation timed out after $TimeoutMinutes minutes"
            $process.Kill()
            $exit_code = -1
        }
    }
    catch {
        Write-Error "Failed to start simulation: $_"
        return -1
    }
    finally {
        if ($process -and -not $process.HasExited) {
            try { $process.Kill() } catch { }
        }
        if ($process) { $process.Dispose() }
    }
    
    $simulation_end = Get-Date
    $duration = $simulation_end - $simulation_start
    
    Write-Info "Simulation completed in $($duration.TotalSeconds) seconds"
    return $exit_code
}

# Enhanced results analysis
function Get-DetailedResults {
    $log_files = @("dsim.log")
    if (-not [string]::IsNullOrEmpty($LogFile) -and (Test-Path $LogFile)) {
        $log_files += $LogFile
    }
    
    $results = @{
        UVM_ERROR = 0
        UVM_FATAL = 0  
        UVM_WARNING = 0
        UVM_INFO = 0
        TEST_PASSED = $false
        COMPILATION_FAILED = $false
        RUNTIME_ERROR = $false
        COVERAGE_GENERATED = $false
        WAVEFORM_GENERATED = $false
        SIMULATION_TIME = ""
        ERROR_DETAILS = @()
    }
    
    foreach ($log_file in $log_files) {
        if (Test-Path $log_file) {
            $content = Get-Content $log_file -Raw
            
            # Count UVM messages
            $results.UVM_ERROR += ($content | Select-String "UVM_ERROR" -AllMatches).Matches.Count
            $results.UVM_FATAL += ($content | Select-String "UVM_FATAL" -AllMatches).Matches.Count
            $results.UVM_WARNING += ($content | Select-String "UVM_WARNING" -AllMatches).Matches.Count
            $results.UVM_INFO += ($content | Select-String "UVM_INFO" -AllMatches).Matches.Count
            
            # Test status
            if ($content -match "TEST PASSED|TEST.*PASSED|\*\*\* TEST PASSED \*\*\*") {
                $results.TEST_PASSED = $true
            }
            
            # Error detection
            if ($content -match "Error-\[|Compile error|\*E,|Fatal:|Error:") {
                $results.COMPILATION_FAILED = $true
                $error_lines = $content | Select-String "Error-\[|Compile error|\*E,|Fatal:|Error:" | Select-Object -First 5
                $results.ERROR_DETAILS += $error_lines.Line
            }
            
            # Runtime errors
            if ($content -match "Runtime error|Segmentation fault|Access violation") {
                $results.RUNTIME_ERROR = $true
            }
            
            # Coverage and waveforms
            if ($content -match "Coverage database|\.cov|\.coverdb") {
                $results.COVERAGE_GENERATED = $true
            }
            
            if ($content -match "\.mxd|\.vcd|\.wlf|waves") {
                $results.WAVEFORM_GENERATED = $true
            }
            
            # Simulation time
            $time_match = $content | Select-String "Simulation time:|Total time:" | Select-Object -First 1
            if ($time_match) {
                $results.SIMULATION_TIME = $time_match.Line
            }
        }
    }
    
    return $results
}

# Comprehensive results display
function Show-DetailedResults {
    param([hashtable]$Results)
    
    $duration = (Get-Date) - $script:START_TIME
    
    Write-Info ""
    Write-Info "=== SIMULATION RESULTS SUMMARY ==="
    Write-Info "Total execution time: $($duration.ToString("mm\:ss"))"
    Write-Info ""
    
    # UVM message counts
    Write-Info "UVM Messages:"
    Write-Info "  INFO: $($Results.UVM_INFO)"
    
    if ($Results.UVM_WARNING -eq 0) {
        Write-Success "  WARNING: $($Results.UVM_WARNING)"
    } else {
        Write-Warning "  WARNING: $($Results.UVM_WARNING)"
    }
    
    if ($Results.UVM_ERROR -eq 0) {
        Write-Success "  ERROR: $($Results.UVM_ERROR)"
    } else {
        Write-Error "  ERROR: $($Results.UVM_ERROR)"
    }
    
    if ($Results.UVM_FATAL -eq 0) {
        Write-Success "  FATAL: $($Results.UVM_FATAL)"
    } else {
        Write-Error "  FATAL: $($Results.UVM_FATAL)"
    }
    
    Write-Info ""
    
    # Additional info
    if ($Results.COVERAGE_GENERATED) {
        Write-Success "Coverage data generated"
    }
    
    if ($Results.WAVEFORM_GENERATED) {
        Write-Success "Waveform files generated"
    }
    
    if ($Results.ERROR_DETAILS.Count -gt 0) {
        Write-Error "Error details:"
        foreach ($error in $Results.ERROR_DETAILS) {
            Write-Error "  $error"
        }
    }
    
    Write-Info ""
    
    # Final status determination
    if ($Results.COMPILATION_FAILED) {
        Write-Error "*** COMPILATION FAILED ***"
        return $false
    }
    elseif ($Results.RUNTIME_ERROR) {
        Write-Error "*** RUNTIME ERROR ***"
        return $false
    }
    elseif ($Results.UVM_FATAL -gt 0) {
        Write-Error "*** FATAL ERRORS DETECTED ***"
        return $false
    }
    elseif ($Results.UVM_ERROR -eq 0 -and ($Results.TEST_PASSED -or $CompileOnly)) {
        if ($CompileOnly) {
            Write-Success "*** COMPILATION SUCCESSFUL ***"
        } else {
            Write-Success "*** TEST PASSED ***"
        }
        return $true
    }
    else {
        Write-Error "*** TEST FAILED ***"
        return $false
    }
}

# Main execution function
function Main {
    try {
        Write-Info "=== Universal UVM Test Runner ==="
        Write-Info "Configuration: $ConfigFile"
        Write-Info "Test: $TestName"
        Write-Info "Top Module: $TopModule"
        Write-Info "Seed: $Seed"
        Write-Info "Verbosity: $Verbosity"
        Write-Info "Timeout: $TimeoutMinutes minutes"
        Write-Info ""
        
        # Environment validation
        Test-DSIMEnvironment
        
        # Configuration validation
        Test-ConfigurationFile $ConfigFile
        
        # Cleanup if requested
        if ($CleanFirst) {
            Clean-Artifacts
        }
        
        # Setup default log file
        if ([string]::IsNullOrEmpty($LogFile)) {
            $timestamp = Get-Date -Format "yyyyMMdd_HHmmss"
            $LogFile = "${TestName}_${timestamp}.log"
        }
        
        # Build arguments and run
        $sim_args = Build-SimulationArguments
        $exit_code = Start-SimulationWithMonitoring $sim_args
        
        # Analyze and display results
        $results = Get-DetailedResults
        $success = Show-DetailedResults $results
        
        if ($success) {
            Write-Success "Script completed successfully!"
            exit 0
        } else {
            Write-Error "Script completed with errors!"
            exit 1
        }
    }
    catch {
        Write-Error "Script execution failed: $_"
        Write-Error $_.ScriptStackTrace
        exit 1
    }
}

# Entry point
if ($MyInvocation.InvocationName -ne '.') {
    Main
}