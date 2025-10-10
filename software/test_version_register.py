#!/usr/bin/env python3
"""
Detailed VERSION register test to isolate the issue
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
        
        print(f"📤 Sending: {' '.join(f'{b:02X}' for b in frame)}")
        ser.write(bytes(frame))
        time.sleep(0.15)  # Slightly longer wait
        
        response = ser.read(ser.in_waiting)
        if response:
            print(f"📥 Received: {response.hex().upper()}")
            print(f"📥 Received bytes: {' '.join(f'{b:02X}' for b in response)}")
        return response
        
    except Exception as e:
        print(f"Error: {e}")
        return None

def test_version_register():
    """Detailed test of VERSION register"""
    
    try:
        ser = serial.Serial('COM3', 115200, timeout=1)
        time.sleep(0.1)
        
        print("=== VERSION Register Detailed Test ===")
        print("Expected: 0x00010000 (Version 1.0.0)")
        print("Testing Address: 0x101C")
        print()
        
        # Test VERSION register
        address = 0x101C
        print(f"Testing VERSION register at address 0x{address:04X}")
        
        response = send_read_command(ser, address)
        
        if response and len(response) >= 8:
            # Parse response
            sof = response[0]
            status = response[1]
            cmd = response[2]
            data_bytes = response[3:7]
            crc = response[7]
            
            data_value = int.from_bytes(data_bytes, byteorder='big')
            
            print(f"\n📋 Response Analysis:")
            print(f"   SOF: 0x{sof:02X}")
            print(f"   STATUS: 0x{status:02X}")
            print(f"   CMD: 0x{cmd:02X}")
            print(f"   Data bytes: {' '.join(f'{b:02X}' for b in data_bytes)}")
            print(f"   CRC: 0x{crc:02X}")
            print(f"   Data value: 0x{data_value:08X}")
            
            if data_value == 0x00010000:
                print("\n✅ SUCCESS: VERSION register returns correct value!")
                print("   This means Register_Block read logic is working correctly.")
            else:
                print(f"\n❌ MISMATCH: Expected 0x00010000, got 0x{data_value:08X}")
                
                # Check pattern type
                if (data_value & 0xFFFFFF00) == 0xF0202200:
                    print("   🚨 F02022XX pattern detected")
                elif (data_value & 0xFFFFFF00) == 0x40202200:
                    print("   🚨 402022XX pattern detected") 
                elif (data_value & 0xFFFFFF00) == 0x40602200:
                    print("   🚨 406022XX pattern detected")
                else:
                    print("   🔍 Unknown pattern - this might be real data!")
                    
        elif response and len(response) > 0:
            print(f"\n⚠️ Unexpected response length: {len(response)} bytes")
            print(f"   Response: {response.hex().upper()}")
        else:
            print("\n❌ No response received")
            
        print("\n=== Analysis ===")
        print("If VERSION register works correctly:")
        print("- Register_Block read logic is functional")
        print("- Issue is with specific test register addresses")
        print("- Problem might be in address decoding or AXI routing")
        print()
        print("If VERSION register also shows pattern:")
        print("- Issue is at AXI4-Lite interface level")
        print("- Read data path is being overridden")
        print("- Need to check AXI4-Lite master or bridge logic")
        
        ser.close()
        
    except serial.SerialException as e:
        print(f"Serial communication error: {e}")
        return False
    except Exception as e:
        print(f"Unexpected error: {e}")
        return False
    
    return True

if __name__ == "__main__":
    success = test_version_register()
    if not success:
        sys.exit(1)