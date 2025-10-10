#!/usr/bin/env python3
"""
Test basic registers (non-test registers) to see if they work correctly
"""

import serial
import time
import sys

def calculate_crc8(data):
    """Calculate CRC8 with polynomial 0x07"""
    crc = 0
    for byte in data:
        crc ^= byte
        for _ in range(8):
            if crc & 0x80:
                crc = (crc << 1) ^ 0x07
            else:
                crc <<= 1
            crc &= 0xFF
    return crc

def send_read_command(ser, address):
    """Send read command and return response"""
    try:
        frame = [
            0xA5,  # SOF
            0xA0,  # Read command
            (address >> 24) & 0xFF,
            (address >> 16) & 0xFF,
            (address >> 8) & 0xFF,
            address & 0xFF,
        ]
        
        crc = calculate_crc8(frame[1:])
        frame.append(crc)
        
        ser.write(bytes(frame))
        time.sleep(0.1)
        
        response = ser.read(ser.in_waiting)
        return response
        
    except Exception as e:
        print(f"Error: {e}")
        return None

def test_basic_registers():
    """Test basic system registers"""
    
    # Basic system registers
    basic_registers = [
        {'name': 'REG_CONTROL', 'addr': 0x1000, 'expected': 'Bridge enable bit'},
        {'name': 'REG_STATUS', 'addr': 0x1004, 'expected': 'Status flags'},
        {'name': 'REG_CONFIG', 'addr': 0x1008, 'expected': 'Configuration'},
        {'name': 'REG_DEBUG', 'addr': 0x100C, 'expected': 'Debug control'},
        {'name': 'REG_TX_COUNT', 'addr': 0x1010, 'expected': 'TX counter'},
        {'name': 'REG_RX_COUNT', 'addr': 0x1014, 'expected': 'RX counter'},
        {'name': 'REG_FIFO_STAT', 'addr': 0x1018, 'expected': 'FIFO status'},
        {'name': 'REG_VERSION', 'addr': 0x101C, 'expected': 'Version 0x00010000'},
    ]
    
    try:
        ser = serial.Serial('COM3', 115200, timeout=1)
        time.sleep(0.1)
        
        print("=== Basic Register Test ===")
        print("Testing system registers to check if they return correct values\n")
        
        print("Register        Address   Response Value      Pattern Type")
        print("-------------   -------   ------------------  -------------")
        
        for reg in basic_registers:
            response = send_read_command(ser, reg['addr'])
            
            if response and len(response) >= 8:
                data_bytes = response[3:7]
                data_value = int.from_bytes(data_bytes, byteorder='big')
                
                # Check pattern type
                if (data_value & 0xFFFFFF00) == 0xF0202200:
                    pattern_type = "F02022XX pattern"
                elif (data_value & 0xFFFFFF00) == 0x40202200:
                    pattern_type = "402022XX pattern"
                elif (data_value & 0xFFFFFF00) == 0x40602200:
                    pattern_type = "406022XX pattern"
                else:
                    pattern_type = "Real data?"
                
                print(f"{reg['name']:13}   0x{reg['addr']:04X}    0x{data_value:08X}        {pattern_type}")
                
                # Special check for VERSION register
                if reg['name'] == 'REG_VERSION' and data_value == 0x00010000:
                    print(f"               ✅ VERSION register shows correct value!")
                elif reg['name'] == 'REG_CONTROL':
                    bridge_enable = data_value & 0x1
                    print(f"               Bridge enable bit: {bridge_enable}")
                    
            else:
                print(f"{reg['name']:13}   0x{reg['addr']:04X}    No response         Communication error")
            
            time.sleep(0.05)
        
        print("\n=== Analysis ===")
        print("If basic registers also show pattern data instead of real values,")
        print("this indicates the issue is at the AXI4-Lite interface level.")
        print("If basic registers work correctly, the issue is specific to test registers.")
        
        ser.close()
        
    except serial.SerialException as e:
        print(f"Serial communication error: {e}")
        return False
    except Exception as e:
        print(f"Unexpected error: {e}")
        return False
    
    return True

if __name__ == "__main__":
    success = test_basic_registers()
    if not success:
        sys.exit(1)