#!/usr/bin/env python3
"""
AXIUART Driver GUI Application

Main entry point for the AXIUART Driver graphical user interface.
Provides comprehensive interface for UART-AXI4 protocol communication with FPGA hardware.

Usage:
    python gui_app.py

Features:
- Connection management with COM port selection
- Register access with read/write operations
- Real-time status monitoring
- Communication logging
- RTS/CTS flow control support
"""

import sys
import os

# Add current directory to path for module imports
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from gui.main_window import MainWindow


def main():
    """Main entry point for the GUI application."""
    try:
        print("Starting AXIUART Driver GUI...")
        app = MainWindow()
        app.run()
    except KeyboardInterrupt:
        print("\nApplication interrupted by user")
        sys.exit(0)
    except Exception as e:
        print(f"Failed to start GUI application: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()