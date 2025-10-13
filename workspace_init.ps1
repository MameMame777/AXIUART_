# Workspace-specific MCP-UVM Auto-loader
# Created: October 13, 2025
# Purpose: Safe, workspace-isolated MCP-UVM environment setup

# This script only affects the current PowerShell session
# No system-wide changes are made

Write-Host @"
🏢 AXIUART Workspace Environment
===============================
Loading workspace-specific MCP-UVM functions...
"@ -ForegroundColor Cyan

# Verify we're in the correct workspace
$expectedWorkspace = "AXIUART_"
$currentPath = Get-Location
if ($currentPath.Path -notlike "*$expectedWorkspace*") {
    Write-Host "⚠️  Warning: Not in AXIUART workspace. Current location: $($currentPath.Path)" -ForegroundColor Yellow
    Write-Host "📍 Expected workspace pattern: *$expectedWorkspace*" -ForegroundColor Yellow
    $choice = Read-Host "Continue anyway? (y/N)"
    if ($choice -ne 'y' -and $choice -ne 'Y') {
        Write-Host "❌ Workspace setup cancelled" -ForegroundColor Red
        return
    }
}

# Define workspace root
$workspaceRoot = "e:\Nautilus\workspace\fpgawork\AXIUART_"
if (-not (Test-Path $workspaceRoot)) {
    Write-Host "❌ Workspace root not found: $workspaceRoot" -ForegroundColor Red
    return
}

# Load MCP-UVM functions (workspace-specific)
$mcpSetupScript = Join-Path $workspaceRoot "sim\exec\setup_mcp_uvm.ps1"
if (Test-Path $mcpSetupScript) {
    try {
        . $mcpSetupScript
        Write-Host "✅ MCP-UVM functions loaded for this session" -ForegroundColor Green
    }
    catch {
        Write-Host "❌ Failed to load MCP-UVM: $($_.Exception.Message)" -ForegroundColor Red
        return
    }
}
else {
    Write-Host "❌ MCP setup script not found: $mcpSetupScript" -ForegroundColor Red
    return
}

# Create workspace-specific convenience functions (session-only)
function global:Set-UVMWorkingDirectory {
    Set-Location (Join-Path $workspaceRoot "sim\uvm")
    Write-Host "📁 Changed to UVM directory" -ForegroundColor Green
}

function global:Set-RTLWorkingDirectory {
    Set-Location (Join-Path $workspaceRoot "rtl")
    Write-Host "📁 Changed to RTL directory" -ForegroundColor Green
}

function global:Set-WorkspaceRoot {
    Set-Location $workspaceRoot
    Write-Host "📁 Changed to workspace root" -ForegroundColor Green
}

function global:Test-WorkspaceMCPUVM {
    Write-Host "`n🔍 Workspace MCP-UVM Status Check:" -ForegroundColor Cyan
    
    $mcpCommands = @(
        "Invoke-MCPUVMTest",
        "Invoke-MCPUVMQuickTest", 
        "Invoke-MCPUVMCompileOnly",
        "Get-MCPUVMStatus",
        "Show-MCPUVMHelp"
    )
    
    $allAvailable = $true
    foreach ($cmd in $mcpCommands) {
        $exists = Get-Command $cmd -ErrorAction SilentlyContinue
        if ($exists) {
            Write-Host "  ✅ $cmd" -ForegroundColor Green
        }
        else {
            Write-Host "  ❌ $cmd" -ForegroundColor Red
            $allAvailable = $false
        }
    }
    
    if ($allAvailable) {
        Write-Host "`n✅ All MCP-UVM functions are available" -ForegroundColor Green
        Write-Host "💡 Ready for UVM simulation" -ForegroundColor Cyan
    }
    else {
        Write-Host "`n❌ Some MCP-UVM functions are missing" -ForegroundColor Red
        Write-Host "💡 Try running this script again or check setup_mcp_uvm.ps1" -ForegroundColor Yellow
    }
}

function global:Show-WorkspaceHelp {
    Write-Host @"

🏢 AXIUART Workspace Commands (Session-Only)
============================================
Set-UVMWorkingDirectory    - Navigate to UVM simulation directory
Set-RTLWorkingDirectory    - Navigate to RTL source directory  
Set-WorkspaceRoot          - Navigate to workspace root
Test-WorkspaceMCPUVM       - Check MCP-UVM function availability
Show-WorkspaceHelp         - Show this help

🔬 MCP-UVM Commands (if loaded)
===============================
Invoke-MCPUVMTest          - Run UVM tests with MCP optimization
Invoke-MCPUVMQuickTest     - Quick UVM test execution
Invoke-MCPUVMCompileOnly   - Compile-only verification
Get-MCPUVMStatus           - Check simulation status
Show-MCPUVMHelp            - Show MCP-UVM specific help

Note: These functions only exist in this PowerShell session
      No system-wide changes have been made
"@ -ForegroundColor Cyan
}

Write-Host @"
✅ Workspace Environment Ready
==============================
Current workspace: $workspaceRoot
Session-specific functions loaded (no system changes)

Type 'Show-WorkspaceHelp' for available commands
Type 'Test-WorkspaceMCPUVM' to verify MCP-UVM functions
"@ -ForegroundColor Green