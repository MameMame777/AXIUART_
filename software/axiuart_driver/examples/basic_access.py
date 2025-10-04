"""
Basic Usage Example for AXIUART Driver

Demonstrates basic register read/write operations.
"""

import sys
import os
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from core.com_manager import COMManager
from core.uart_protocol import UARTProtocol, ProtocolError
from core.register_map import RegisterMap

def basic_register_access(port_name: str = "COM3", baudrate: int = 115200):
    """
    Basic register access example
    
    Args:
        port_name: COM port name
        baudrate: Baud rate
    """
    # Create COM manager and protocol handler
    com = COMManager()
    protocol = UARTProtocol(com)
    
    try:
        # Connect to COM port
        print(f"Connecting to {port_name} at {baudrate} bps...")
        if not com.connect(port_name, baudrate):
            print("Connection failed!")
            return
        
        print("Connected successfully!")
        
        # Read version register
        print("\n--- Reading Version Register ---")
        try:
            version = protocol.register_read(RegisterMap.VERSION)
            print(f"VERSION: 0x{version:08X}")
        except ProtocolError as e:
            print(f"Version read failed: {e}")
        
        # Read status register
        print("\n--- Reading Status Register ---")
        try:
            status = protocol.register_read(RegisterMap.STATUS)
            print(f"STATUS: 0x{status:08X}")
        except ProtocolError as e:
            print(f"Status read failed: {e}")
        
        # Enable bridge
        print("\n--- Enabling Bridge ---")
        try:
            protocol.register_write(RegisterMap.CONTROL, RegisterMap.CONTROL_BRIDGE_ENABLE)
            print("Bridge enabled")
            
            # Read back control register
            control = protocol.register_read(RegisterMap.CONTROL)
            print(f"CONTROL: 0x{control:08X}")
        except ProtocolError as e:
            print(f"Bridge enable failed: {e}")
        
        # Read counters
        print("\n--- Reading Counters ---")
        try:
            tx_count = protocol.register_read(RegisterMap.TX_COUNT)
            rx_count = protocol.register_read(RegisterMap.RX_COUNT)
            print(f"TX_COUNT: {tx_count}")
            print(f"RX_COUNT: {rx_count}")
        except ProtocolError as e:
            print(f"Counter read failed: {e}")
        
        # Show statistics
        print("\n--- Protocol Statistics ---")
        stats = protocol.get_statistics()
        for key, value in stats.items():
            print(f"{key}: {value}")
        
    finally:
        # Always disconnect
        com.disconnect()
        print("\nDisconnected")

def scan_and_test():
    """Scan for COM ports and test basic functionality"""
    com = COMManager()
    
    # Scan for available ports
    print("Scanning for COM ports...")
    ports = com.scan_ports()
    
    if not ports:
        print("No COM ports found!")
        return
    
    print(f"Found ports: {ports}")
    
    # Try first available port
    test_port = ports[0]
    print(f"\nTesting with {test_port}...")
    basic_register_access(test_port)

if __name__ == "__main__":
    if len(sys.argv) > 1:
        port = sys.argv[1]
        baudrate = int(sys.argv[2]) if len(sys.argv) > 2 else 115200
        basic_register_access(port, baudrate)
    else:
        scan_and_test()