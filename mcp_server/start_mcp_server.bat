@echo off
REM DSIM UVM MCP Server Launcher
REM Created by setup script

echo Starting DSIM UVM MCP Server...

REM Set workspace directory
set WORKSPACE_DIR=%~dp0..

REM Check Python availability
python --version >nul 2>&1
if errorlevel 1 (
    echo Error: Python is not available in PATH
    pause
    exit /b 1
)

REM Check DSIM environment
if not defined DSIM_HOME (
    echo Error: DSIM_HOME environment variable is not set
    pause
    exit /b 1
)

REM Start MCP server
python "%~dp0dsim_uvm_server.py" --workspace "%WORKSPACE_DIR%"

pause
