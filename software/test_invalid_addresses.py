#!/usr/bin/env python3
"""
Test invalid address to see if it follows the same pattern
"""

import serial
import time

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

def test_invalid_address():
    """Test an invalid address to see response pattern"""
    
    try:
        ser = serial.Serial('COM3', 115200, timeout=1)
        time.sleep(0.1)
        
        print("=== Invalid Address Test ===")
        print("Testing what happens with non-existent address")
        print()
        
        # Test multiple addresses to see pattern
        test_addresses = [
            0x0000,  # Should be invalid
            0x0500,  # Should be invalid
            0x1000,  # Valid: REG_CONTROL
            0x101C,  # Valid: REG_VERSION
            0x2000,  # Should be invalid
        ]
        
        for addr in test_addresses:
            print(f"Testing address 0x{addr:04X}:")
            
            frame = [
                0xA5,  # SOF
                0xA0,  # Read command
                (addr >> 24) & 0xFF,
                (addr >> 16) & 0xFF,
                (addr >> 8) & 0xFF,
                addr & 0xFF,
            ]
            
            crc = calculate_crc8(frame[1:])
            frame.append(crc)
            
            print(f"  📤 Sending: {' '.join(f'{b:02X}' for b in frame)}")
            ser.write(bytes(frame))
            time.sleep(0.15)
            
            response = ser.read(ser.in_waiting)
            if response:
                print(f"  📥 Received ({len(response)} bytes): {' '.join(f'{b:02X}' for b in response)}")
                
                if len(response) >= 7:
                    # Try to extract data (assuming 4-byte data in middle)
                    if len(response) >= 7:
                        data_start = 3  # Usually after SOF, STATUS, CMD
                        data_bytes = response[data_start:data_start+4]
                        if len(data_bytes) == 4:
                            data_value = int.from_bytes(data_bytes, byteorder='big')
                            print(f"  📊 Data value: 0x{data_value:08X}")
                        
                            # Check pattern
                            if (data_value & 0xFFFFFF00) == 0x40202200:
                                last_byte = data_value & 0xFF
                                addr_calc = (addr >> 2) & 0xFF
                                print(f"  🔍 Pattern: 0x402022{last_byte:02X}, Address/4: 0x{addr_calc:02X}")
            else:
                print("  ❌ No response")
                
            print()
            time.sleep(0.1)
        
        print("=== Pattern Analysis ===")
        print("If all addresses return 0x402022XX pattern:")
        print("- The issue is NOT in Register_Block logic")
        print("- Something at AXI4-Lite level is generating this pattern")
        print("- Possible causes: AXI4-Lite master, bridge, or routing issue")
        
        ser.close()
        
    except Exception as e:
        print(f"Error: {e}")

if __name__ == "__main__":
    test_invalid_address()