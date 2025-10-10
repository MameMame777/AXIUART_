#!/usr/bin/env python3
"""
Extended Test Register Pattern Analysis
Test the mathematical relationship: Last Byte = 0x40 + (Address >> 2)
with additional test registers at different addresses
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
        # Read command frame: [SOF, CMD, ADDR_bytes, CRC]
        frame = [
            0xA5,  # SOF
            0xA0,  # Read command
            (address >> 24) & 0xFF,  # Address byte 3
            (address >> 16) & 0xFF,  # Address byte 2
            (address >> 8) & 0xFF,   # Address byte 1
            address & 0xFF,          # Address byte 0
        ]
        
        # Calculate CRC over all bytes except SOF
        crc = calculate_crc8(frame[1:])
        frame.append(crc)
        
        # Send frame
        ser.write(bytes(frame))
        time.sleep(0.1)  # Wait for response
        
        response = ser.read(ser.in_waiting)
        return response
        
    except Exception as e:
        print(f"Error during communication: {e}")
        return None

def test_extended_pattern():
    """Test extended register pattern with various addresses"""
    
    # Extended test registers with different address patterns
    test_registers = [
        # Original registers
        {'name': 'REG_TEST_0', 'addr': 0x1020, 'offset': 0x020},
        {'name': 'REG_TEST_1', 'addr': 0x1024, 'offset': 0x024},
        {'name': 'REG_TEST_2', 'addr': 0x1028, 'offset': 0x028},
        {'name': 'REG_TEST_3', 'addr': 0x102C, 'offset': 0x02C},
        # Extended registers to test pattern
        {'name': 'REG_TEST_4', 'addr': 0x1040, 'offset': 0x040},
        {'name': 'REG_TEST_5', 'addr': 0x1050, 'offset': 0x050},
        {'name': 'REG_TEST_6', 'addr': 0x1080, 'offset': 0x080},
        {'name': 'REG_TEST_7', 'addr': 0x1100, 'offset': 0x100},
    ]
    
    try:
        # Initialize serial connection
        ser = serial.Serial('COM3', 115200, timeout=1)
        time.sleep(0.1)
        
        print("=== Extended Pattern Analysis Test ===")
        print("Testing mathematical relationship: Last Byte = 0x40 + (Address >> 2)\n")
        
        print("Register     Address   Offset   Predicted   Actual   Match   ASCII")
        print("----------   -------   ------   ---------   ------   -----   -----")
        
        all_predictions_correct = True
        
        for reg in test_registers:
            # Calculate prediction based on mathematical formula
            addr_div_4 = reg['addr'] >> 2
            predicted_last_byte = 0x40 + (addr_div_4 & 0xFF)
            
            # Send read command
            response = send_read_command(ser, reg['addr'])
            
            if response and len(response) >= 8:
                # Extract data from response
                data_bytes = response[3:7]  # 4 data bytes
                actual_full_value = int.from_bytes(data_bytes, byteorder='big')
                actual_last_byte = data_bytes[3]  # Last byte
                
                # Check if prediction matches
                match = "✓" if actual_last_byte == predicted_last_byte else "✗"
                if actual_last_byte != predicted_last_byte:
                    all_predictions_correct = False
                
                # ASCII representation
                ascii_char = chr(actual_last_byte) if 32 <= actual_last_byte <= 126 else '?'
                
                print(f"{reg['name']:10}   0x{reg['addr']:04X}   0x{reg['offset']:03X}   0x{predicted_last_byte:02X}      0x{actual_last_byte:02X}   {match:^5}   '{ascii_char}'")
                
                # Show full pattern for first few registers
                if reg['name'] in ['REG_TEST_0', 'REG_TEST_4', 'REG_TEST_7']:
                    print(f"           Full value: 0x{actual_full_value:08X}")
                
            else:
                print(f"{reg['name']:10}   0x{reg['addr']:04X}   0x{reg['offset']:03X}   0x{predicted_last_byte:02X}      --    ✗     ?")
                print(f"           No valid response")
                all_predictions_correct = False
            
            time.sleep(0.05)  # Small delay between commands
        
        print()
        print("=== Analysis Results ===")
        
        if all_predictions_correct:
            print("🎯 MATHEMATICAL RELATIONSHIP CONFIRMED!")
            print("   Formula: Last Byte = 0x40 + (Address >> 2)")
            print("   This proves the pattern is address-calculation based")
        else:
            print("❌ Mathematical relationship does NOT hold for all addresses")
            print("   Pattern may be more complex or have address range limits")
        
        print("\n=== Pattern Implications ===")
        print("1. The 0xF02022XX pattern is deterministic based on address")
        print("2. Address decoding is working correctly in hardware")
        print("3. But actual register values are not being returned")
        print("4. Instead, an address-derived value is generated")
        
        print("\n=== Next Investigation Steps ===")
        print("1. Check if pattern holds for non-test register addresses")
        print("2. Investigate what generates the 0xF02022 prefix")
        print("3. Determine why address calculation overrides register values")
        
        ser.close()
        
    except serial.SerialException as e:
        print(f"Serial communication error: {e}")
        return False
    except Exception as e:
        print(f"Unexpected error: {e}")
        return False
    
    return True

if __name__ == "__main__":
    success = test_extended_pattern()
    if not success:
        sys.exit(1)