"""
AXIUART Driver GUI Test Script

Simple test script to verify GUI functionality without hardware connection.
"""

import sys
import os

# Add current directory to path for module imports
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from core import COMManager
import tkinter as tk


def test_com_port_scanning():
    """Test COM port scanning functionality."""
    print("Testing COM port scanning...")
    com_manager = COMManager()
    
    # Test port scanning
    ports = com_manager.scan_ports()
    print(f"Available COM ports: {ports}")
    
    # Test detailed port list
    port_info = com_manager.list_ports()
    print("Detailed port information:")
    for port in port_info:
        print(f"  {port.device} - {port.description}")
    
    return len(ports) > 0


def test_tkinter_basic():
    """Test basic tkinter functionality."""
    print("Testing tkinter basic functionality...")
    
    try:
        root = tk.Tk()
        root.withdraw()  # Hide window
        
        # Test basic widgets
        label = tk.Label(root, text="Test")
        button = tk.Button(root, text="Test Button")
        entry = tk.Entry(root)
        
        print("✓ Tkinter widgets created successfully")
        root.destroy()
        return True
        
    except Exception as e:
        print(f"✗ Tkinter test failed: {e}")
        return False


def main():
    """Run basic functionality tests."""
    print("AXIUART Driver GUI - Basic Functionality Test")
    print("=" * 50)
    
    # Test 1: Tkinter basic functionality
    tkinter_ok = test_tkinter_basic()
    
    # Test 2: COM port scanning
    com_ok = test_com_port_scanning()
    
    print("\nTest Results:")
    print(f"Tkinter functionality: {'✓ OK' if tkinter_ok else '✗ FAIL'}")
    print(f"COM port scanning: {'✓ OK' if com_ok else '✗ FAIL'}")
    
    if tkinter_ok and com_ok:
        print("\n✓ All basic tests passed. GUI should work correctly.")
        print("You can now run 'python gui_app.py' to start the full GUI.")
    else:
        print("\n✗ Some tests failed. Please check the error messages above.")
    
    return tkinter_ok and com_ok


if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)