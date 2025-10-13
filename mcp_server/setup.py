#!/usr/bin/env python3
"""
Setup script for DSIM UVM MCP Server
Installs dependencies and configures the environment
"""

import os
import sys
import subprocess
import json
from pathlib import Path

def install_mcp_package():
    """Install MCP package using pip"""
    print("🔧 Installing MCP package...")
    
    try:
        # Try installing MCP package
        result = subprocess.run([
            sys.executable, "-m", "pip", "install", "mcp"
        ], capture_output=True, text=True, check=True)
        
        print("✅ MCP package installed successfully")
        return True
        
    except subprocess.CalledProcessError as e:
        print(f"❌ Failed to install MCP package: {e}")
        print(f"STDOUT: {e.stdout}")
        print(f"STDERR: {e.stderr}")
        
        # Try alternative installation methods
        print("🔄 Trying alternative installation...")
        
        try:
            # Try installing from PyPI with specific version
            result = subprocess.run([
                sys.executable, "-m", "pip", "install", "model-context-protocol"
            ], capture_output=True, text=True, check=True)
            
            print("✅ Alternative MCP package installed")
            return True
            
        except subprocess.CalledProcessError as e2:
            print(f"❌ Alternative installation also failed: {e2}")
            return False

def install_requirements():
    """Install requirements from requirements.txt"""
    print("📦 Installing requirements...")
    
    requirements_file = Path(__file__).parent / "requirements.txt"
    
    if not requirements_file.exists():
        print("❌ requirements.txt not found")
        return False
    
    try:
        result = subprocess.run([
            sys.executable, "-m", "pip", "install", "-r", str(requirements_file)
        ], capture_output=True, text=True, check=True)
        
        print("✅ Requirements installed successfully")
        return True
        
    except subprocess.CalledProcessError as e:
        print(f"❌ Failed to install requirements: {e}")
        print(f"STDERR: {e.stderr}")
        return False

def verify_dsim_environment():
    """Verify DSIM environment variables"""
    print("🔍 Verifying DSIM environment...")
    
    dsim_home = os.environ.get('DSIM_HOME')
    
    if not dsim_home:
        print("⚠️  DSIM_HOME not set in environment")
        print("   Please set DSIM_HOME to your DSIM installation directory")
        return False
        
    dsim_path = Path(dsim_home)
    if not dsim_path.exists():
        print(f"❌ DSIM_HOME path does not exist: {dsim_home}")
        return False
        
    dsim_exe = dsim_path / "bin" / "dsim.exe"
    if not dsim_exe.exists():
        print(f"❌ DSIM executable not found: {dsim_exe}")
        return False
        
    print(f"✅ DSIM environment verified: {dsim_home}")
    return True

def create_launcher_script():
    """Create a launcher script for the MCP server"""
    print("📝 Creating launcher script...")
    
    launcher_content = '''@echo off
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
'''
    
    launcher_file = Path(__file__).parent / "start_mcp_server.bat"
    
    try:
        with open(launcher_file, 'w', encoding='utf-8') as f:
            f.write(launcher_content)
        print(f"✅ Launcher script created: {launcher_file}")
        return True
    except Exception as e:
        print(f"❌ Failed to create launcher script: {e}")
        return False

def test_mcp_server():
    """Test MCP server functionality"""
    print("🧪 Testing MCP server...")
    
    server_file = Path(__file__).parent / "dsim_uvm_server.py"
    
    if not server_file.exists():
        print("❌ MCP server file not found")
        return False
    
    try:
        # Try importing the server module
        result = subprocess.run([
            sys.executable, "-c", 
            "import sys; sys.path.append(r'{}'); from dsim_uvm_server import DSIMSimulationServer; print('✅ MCP server module loaded successfully')".format(str(server_file.parent))
        ], capture_output=True, text=True, timeout=10)
        
        if result.returncode == 0:
            print("✅ MCP server module test passed")
            return True
        else:
            print(f"❌ MCP server module test failed: {result.stderr}")
            return False
            
    except subprocess.TimeoutExpired:
        print("❌ MCP server test timed out")
        return False
    except Exception as e:
        print(f"❌ MCP server test error: {e}")
        return False

def main():
    """Main setup function"""
    print("🚀 DSIM UVM MCP Server Setup")
    print("=" * 50)
    
    success_count = 0
    total_steps = 5
    
    # Step 1: Install MCP package
    if install_mcp_package():
        success_count += 1
    
    # Step 2: Install requirements
    if install_requirements():
        success_count += 1
    
    # Step 3: Verify DSIM environment
    if verify_dsim_environment():
        success_count += 1
    
    # Step 4: Create launcher script
    if create_launcher_script():
        success_count += 1
    
    # Step 5: Test MCP server
    if test_mcp_server():
        success_count += 1
    
    # Summary
    print("\n" + "=" * 50)
    print(f"📊 Setup Summary: {success_count}/{total_steps} steps completed")
    
    if success_count == total_steps:
        print("🎉 Setup completed successfully!")
        print("\n💡 Next steps:")
        print("1. Run: start_mcp_server.bat")
        print("2. Configure your MCP client to use the server")
        print("3. Test with tools like run_uvm_simulation")
    else:
        print("⚠️  Setup completed with some issues")
        print("   Please review the error messages above")
    
    return success_count == total_steps

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)