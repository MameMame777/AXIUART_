#!/usr/bin/env python3
"""DSIM Environment Setup Script"""

import os
import sys
from pathlib import Path

def setup_dsim_environment():
    """Setup DSIM environment variables"""
    
    # Default DSIM installation path
    dsim_home = "C:\\Users\\Nautilus\\AppData\\Local\\metrics-ca\\dsim\\20240422.0.0"
    
    print("Setting up DSIM environment variables...")
    
    # Set environment variables
    os.environ['DSIM_HOME'] = dsim_home
    os.environ['DSIM_ROOT'] = dsim_home
    os.environ['DSIM_LIB_PATH'] = f"{dsim_home}\\lib"
    
    # Check if DSIM_LICENSE is already set, if not try to auto-configure
    if not os.environ.get('DSIM_LICENSE'):
        license_paths = [
            Path(dsim_home).parent / "dsim-license.json",
            Path(dsim_home) / "dsim-license.json",
            Path("C:\\Users\\Nautilus\\AppData\\Local\\metrics-ca\\dsim-license.json")
        ]
        
        for license_path in license_paths:
            if license_path.exists():
                os.environ['DSIM_LICENSE'] = str(license_path)
                print(f"Auto-configured DSIM_LICENSE: {license_path}")
                break
    
    # Verify setup
    print("\\n=== DSIM Environment Status ===")
    print(f"DSIM_HOME: {os.environ.get('DSIM_HOME', 'NOT SET')}")
    print(f"DSIM_ROOT: {os.environ.get('DSIM_ROOT', 'NOT SET')}")
    print(f"DSIM_LIB_PATH: {os.environ.get('DSIM_LIB_PATH', 'NOT SET')}")
    print(f"DSIM_LICENSE: {os.environ.get('DSIM_LICENSE', 'NOT SET')}")
    
    # Check DSIM executable
    dsim_exe = Path(dsim_home) / "bin" / "dsim.exe"
    if dsim_exe.exists():
        print(f"✅ DSIM Executable: {dsim_exe}")
    else:
        print(f"❌ DSIM Executable not found: {dsim_exe}")
        return False
    
    print("\\n✅ DSIM environment setup completed successfully!")
    return True

if __name__ == "__main__":
    success = setup_dsim_environment()
    sys.exit(0 if success else 1)