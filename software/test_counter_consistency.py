#!/usr/bin/env python3
"""
Test script to verify if the 0xF02022XX counter values are consistent
across multiple test runs and analyze counter behavior patterns.
"""

import serial
import time
import sys

def send_frame(ser, frame_bytes):
    """Send a frame and return the response"""
    try:
        ser.write(frame_bytes)
        time.sleep(0.1)  # Wait for response
        
        response = ser.read(ser.in_waiting)
        return response
    except Exception as e:
        print(f"Error during communication: {e}")
        return None

def test_counter_pattern():
    """Test counter consistency across multiple runs"""
    try:
        # Initialize serial connection
        ser = serial.Serial('COM3', 115200, timeout=1)
        time.sleep(0.1)
        
        print("=== Counter Consistency Test ===")
        print("Testing if 0xF02022XX counter values are always the same...\n")
        
        # Test addresses
        test_addresses = [0x1020, 0x1024, 0x1028, 0x102C]
        
        # Run multiple test cycles
        for cycle in range(5):
            print(f"--- Test Cycle {cycle + 1} ---")
            
            cycle_results = []
            
            for addr in test_addresses:
                # Read command frame: [SOF, CMD, LEN, ADDR_bytes, CRC]
                frame = [
                    0xAD,  # SOF (using old protocol)
                    0xA0,  # Read command
                    0x00,  # Length = 0 for read
                    (addr >> 24) & 0xFF,  # Address byte 3
                    (addr >> 16) & 0xFF,  # Address byte 2
                    (addr >> 8) & 0xFF,   # Address byte 1
                    addr & 0xFF,          # Address byte 0
                ]
                
                # Calculate CRC over all bytes except SOF
                crc = 0
                for byte in frame[1:]:
                    crc ^= byte
                    for _ in range(8):
                        if crc & 0x80:
                            crc = (crc << 1) ^ 0x07
                        else:
                            crc <<= 1
                        crc &= 0xFF
                
                frame.append(crc)
                
                # Send frame and get response
                response = send_frame(ser, bytes(frame))
                
                if response and len(response) >= 8:
                    # Extract 32-bit data from response
                    data_bytes = response[3:7]  # 4 data bytes
                    data_value = int.from_bytes(data_bytes, byteorder='big')
                    last_byte = data_bytes[3]  # Last byte
                    
                    result = {
                        'address': addr,
                        'full_value': data_value,
                        'last_byte': last_byte,
                        'response_hex': response.hex()
                    }
                    cycle_results.append(result)
                    
                    print(f"  0x{addr:04X} -> 0x{data_value:08X} (last byte: 0x{last_byte:02X})")
                else:
                    print(f"  0x{addr:04X} -> No valid response")
                
                time.sleep(0.05)  # Small delay between commands
            
            print()
            
            # Wait between cycles
            if cycle < 4:  # Don't wait after last cycle
                print("Waiting 2 seconds before next cycle...\n")
                time.sleep(2)
        
        print("=== Analysis ===")
        print("If counter values are always the same, this suggests:")
        print("1. Counter resets to same initial value on each power cycle")
        print("2. Counter state is not persistent across transactions") 
        print("3. Pattern might be from uninitialized memory or fixed ROM")
        
        ser.close()
        
    except serial.SerialException as e:
        print(f"Serial communication error: {e}")
        return False
    except Exception as e:
        print(f"Unexpected error: {e}")
        return False
    
    return True

if __name__ == "__main__":
    success = test_counter_pattern()
    if not success:
        sys.exit(1)