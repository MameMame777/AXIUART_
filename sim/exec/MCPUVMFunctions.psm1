# MCP Server UVM Execution Functions
# Optimized wrapper functions for convenient UVM simulation execution

function Invoke-MCPUVMTest {
    <#
    .SYNOPSIS
    Execute UVM test with MCP server optimization
    
    .DESCRIPTION
    Convenient wrapper function for MCP server to execute UVM tests with enhanced reporting and analysis
    
    .PARAMETER TestName
    Name of the UVM test to execute (default: uart_axi4_basic_test)
    
    .PARAMETER Mode
    Execution mode: 'run' or 'compile' (default: run)
    
    .PARAMETER Verbosity
    UVM verbosity level (default: UVM_MEDIUM)
    
    .PARAMETER Waves
    Enable waveform capture: 'on' or 'off' (default: off)
    
    .PARAMETER Seed
    Simulation seed (default: 1)
    
    .PARAMETER Coverage
    Enable coverage collection: 'on' or 'off' (default: on)
    
    .PARAMETER QuickTest
    Run quick test with minimal logging (default: false)
    
    .EXAMPLE
    Invoke-MCPUVMTest -TestName "uart_axi4_basic_test"
    
    .EXAMPLE
    Invoke-MCPUVMTest -TestName "uart_axi4_scoreboard_test" -Verbosity UVM_HIGH -Seed 42
    
    .EXAMPLE
    Invoke-MCPUVMTest -Mode compile  # Compile only
    #>
    
    [CmdletBinding()]
    param(
        [string]$TestName = "uart_axi4_basic_test",
        
        [ValidateSet("run", "compile")]
        [string]$Mode = "run",
        
        [ValidateSet("UVM_NONE", "UVM_LOW", "UVM_MEDIUM", "UVM_HIGH", "UVM_FULL")]
        [string]$Verbosity = "UVM_MEDIUM",
        
        [ValidateSet("on", "off")]
        [string]$Waves = "off",
        
        [int]$Seed = 1,
        
        [ValidateSet("on", "off")]
        [string]$Coverage = "on",
        
        [switch]$QuickTest = $false,
        
        [string[]]$ExtraArgs = @()
    )
    
    Write-Host "🚀 MCP-UVM: Starting simulation with optimized settings" -ForegroundColor Green
    
    # Navigate to execution directory (get current script directory)
    $originalLocation = Get-Location
    $scriptDir = Split-Path -Parent $PSCommandPath
    if (-not $scriptDir) {
        $scriptDir = "e:\Nautilus\workspace\fpgawork\AXIUART_\sim\exec"  # fallback
    }
    
    try {
        Set-Location $scriptDir
        
        # Build command arguments
        $mcpArgs = @{
            TestName = $TestName
            Mode = $Mode
            Verbosity = $Verbosity
            Waves = $Waves
            Seed = $Seed
            Coverage = $Coverage
        }
        
        # Add MCP optimization flag
        $mcpArgs.MCPOptimized = $true
        
        # Quick test optimizations
        if ($QuickTest) {
            $mcpArgs.Verbosity = "UVM_LOW"
            $mcpArgs.Coverage = "off"
            Write-Host "🏃 MCP-UVM: Quick test mode enabled" -ForegroundColor Yellow
        }
        
        # Add extra arguments
        if ($ExtraArgs.Count -gt 0) {
            $mcpArgs.ExtraArgs = $ExtraArgs
        }
        
        # Execute MCP-optimized UVM runner
        Write-Host "🔧 MCP-UVM: Executing with parameters:" -ForegroundColor Cyan
        Write-Host "  Test: $TestName" -ForegroundColor White
        Write-Host "  Mode: $Mode" -ForegroundColor White
        Write-Host "  Verbosity: $Verbosity" -ForegroundColor White
        Write-Host "  Waves: $Waves" -ForegroundColor White
        Write-Host "  Seed: $Seed" -ForegroundColor White
        Write-Host "  Coverage: $Coverage" -ForegroundColor White
        
        & .\mcp_uvm_runner.ps1 @mcpArgs
        
        $exitCode = $LASTEXITCODE
        if ($exitCode -eq 0) {
            Write-Host "✅ MCP-UVM: Simulation completed successfully" -ForegroundColor Green
        } else {
            Write-Host "❌ MCP-UVM: Simulation failed with exit code $exitCode" -ForegroundColor Red
        }
        
        return $exitCode
        
    } finally {
        Set-Location $originalLocation
    }
}

function Invoke-MCPUVMQuickTest {
    <#
    .SYNOPSIS
    Execute quick UVM test for rapid iteration
    
    .DESCRIPTION
    Optimized for fast execution with minimal logging and no coverage
    
    .PARAMETER TestName
    Name of the UVM test to execute
    
    .EXAMPLE
    Invoke-MCPUVMQuickTest -TestName "uart_axi4_basic_test"
    #>
    
    [CmdletBinding()]
    param(
        [string]$TestName = "uart_axi4_basic_test"
    )
    
    return Invoke-MCPUVMTest -TestName $TestName -QuickTest -Verbosity UVM_LOW -Coverage "off"
}

function Invoke-MCPUVMCompileOnly {
    <#
    .SYNOPSIS
    Compile UVM testbench without simulation
    
    .DESCRIPTION
    Quick compilation check for syntax and dependency validation
    
    .EXAMPLE
    Invoke-MCPUVMCompileOnly
    #>
    
    [CmdletBinding()]
    param()
    
    return Invoke-MCPUVMTest -Mode compile
}

function Invoke-MCPUVMWithWaves {
    <#
    .SYNOPSIS
    Execute UVM test with waveform capture enabled
    
    .DESCRIPTION
    Optimized for debugging with waveform capture and high verbosity
    
    .PARAMETER TestName
    Name of the UVM test to execute
    
    .PARAMETER Seed
    Simulation seed for reproducibility
    
    .EXAMPLE
    Invoke-MCPUVMWithWaves -TestName "uart_axi4_basic_test" -Seed 42
    #>
    
    [CmdletBinding()]
    param(
        [string]$TestName = "uart_axi4_basic_test",
        [int]$Seed = 1
    )
    
    return Invoke-MCPUVMTest -TestName $TestName -Waves on -Verbosity UVM_HIGH -Seed $Seed
}

function Get-MCPUVMStatus {
    <#
    .SYNOPSIS
    Get status of recent UVM simulations
    
    .DESCRIPTION
    Display recent log files and simulation results
    
    .EXAMPLE
    Get-MCPUVMStatus
    #>
    
    [CmdletBinding()]
    param()
    
    Write-Host "📊 MCP-UVM: Recent simulation status" -ForegroundColor Cyan
    
    # Get directories relative to script location
    $scriptDir = Split-Path -Parent $PSCommandPath
    if (-not $scriptDir) {
        $scriptDir = "e:\Nautilus\workspace\fpgawork\AXIUART_\sim\exec"  # fallback
    }
    
    $logDir = Join-Path $scriptDir "logs"
    $waveDir = Join-Path (Split-Path (Split-Path $scriptDir -Parent) -Parent) "archive\waveforms"
    
    if (Test-Path $logDir) {
        $recentLogs = Get-ChildItem -Path $logDir -Filter "*.log" | Sort-Object LastWriteTime -Descending | Select-Object -First 5
        
        Write-Host "`n📝 Recent log files:" -ForegroundColor Green
        foreach ($log in $recentLogs) {
            $size = [math]::Round($log.Length / 1KB, 1)
            Write-Host "  $($log.Name) ($($size)KB) - $($log.LastWriteTime)" -ForegroundColor White
        }
    }
    
    if (Test-Path $waveDir) {
        $recentWaves = Get-ChildItem -Path $waveDir -Filter "*.mxd" | Sort-Object LastWriteTime -Descending | Select-Object -First 3
        
        Write-Host "`n🌊 Recent waveform files:" -ForegroundColor Green
        foreach ($wave in $recentWaves) {
            $size = [math]::Round($wave.Length / 1MB, 1)
            Write-Host "  $($wave.Name) ($($size)MB) - $($wave.LastWriteTime)" -ForegroundColor White
        }
    }
}

function Show-MCPUVMHelp {
    <#
    .SYNOPSIS
    Display MCP-UVM usage help
    
    .DESCRIPTION
    Show available MCP-optimized UVM functions and examples
    
    .EXAMPLE
    Show-MCPUVMHelp
    #>
    
    Write-Host @"
🔬 MCP-UVM: SystemVerilog UVM Test Execution Framework
=====================================================

Available Functions:
-------------------
Invoke-MCPUVMTest        - Main UVM test execution function
Invoke-MCPUVMQuickTest   - Quick test execution (minimal logging)
Invoke-MCPUVMCompileOnly - Compile-only mode for syntax checking
Invoke-MCPUVMWithWaves   - Test execution with waveform capture
Get-MCPUVMStatus         - Show recent simulation results
Show-MCPUVMHelp          - Display this help

Quick Start Examples:
--------------------
# Basic test execution
Invoke-MCPUVMTest

# Run specific test with high verbosity
Invoke-MCPUVMTest -TestName "uart_axi4_scoreboard_test" -Verbosity UVM_HIGH

# Quick iteration testing
Invoke-MCPUVMQuickTest -TestName "uart_axi4_basic_test"

# Compile only (syntax check)
Invoke-MCPUVMCompileOnly

# Debug with waveforms
Invoke-MCPUVMWithWaves -TestName "uart_axi4_basic_test" -Seed 42

# Check recent results
Get-MCPUVMStatus

Available Tests:
---------------
- uart_axi4_basic_test        : Basic functionality test
- uart_axi4_scoreboard_test   : Scoreboard validation test  
- uart_axi4_coverage_test     : Coverage collection test
- uart_axi4_register_test     : Register access test

Environment Requirements:
------------------------
- DSIM_HOME: $env:DSIM_HOME
- DSIM_ROOT: $env:DSIM_ROOT
- DSIM_LIB_PATH: $env:DSIM_LIB_PATH

For detailed parameter information, use: Get-Help <FunctionName> -Detailed
"@ -ForegroundColor Yellow
}

# Export functions for easy access
Export-ModuleMember -Function @(
    'Invoke-MCPUVMTest',
    'Invoke-MCPUVMQuickTest', 
    'Invoke-MCPUVMCompileOnly',
    'Invoke-MCPUVMWithWaves',
    'Get-MCPUVMStatus',
    'Show-MCPUVMHelp'
)

# Display welcome message
Write-Host "🔬 MCP-UVM functions loaded. Use 'Show-MCPUVMHelp' for usage information." -ForegroundColor Green