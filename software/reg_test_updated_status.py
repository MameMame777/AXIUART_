#!/usr/bin/env python3
"""
Updated REG_TEST test that handles multiple success status codes
Handles STATUS 0x00, 0x40, 0x80 as success codes per Frame_Builder logic
"""

import serial
import time
import sys

def create_frame(sof, cmd, addr_bytes, data_bytes=None):
    """Create a frame with SOF, CMD, ADDR, optional DATA, and CRC"""
    frame = [sof, cmd] + addr_bytes
    if data_bytes:
        frame.extend(data_bytes)
    
    # Calculate CRC (simple XOR for now)
    crc = 0
    for byte in frame:
        crc ^= byte
    frame.append(crc)
    return frame

def is_success_status(status):
    """Check if status code indicates success per Frame_Builder logic"""
    return status in [0x00, 0x40, 0x80]

def parse_response(data):
    """Parse received response data"""
    if len(data) < 3:
        return None
    
    sof = data[0]
    status = data[1]
    cmd_echo = data[2]
    
    if len(data) >= 8:  # Read response
        data_bytes = data[3:7]
        crc = data[7]
        value = (data_bytes[3] << 24) | (data_bytes[2] << 16) | (data_bytes[1] << 8) | data_bytes[0]
        return {
            'type': 'read',
            'sof': sof,
            'status': status,
            'cmd_echo': cmd_echo,
            'data': data_bytes,
            'value': value,
            'crc': crc,
            'success': is_success_status(status)
        }
    else:  # Write response
        crc = data[3] if len(data) >= 4 else 0
        return {
            'type': 'write',
            'sof': sof,
            'status': status,
            'cmd_echo': cmd_echo,
            'crc': crc,
            'success': is_success_status(status)
        }

def test_register_write_read(ser, addr, test_value, name):
    """Test write and read for a specific register"""
    print(f"\n📍 Testing {name} (0x{addr:08X})")
    print("-" * 50)
    
    addr_bytes = [
        (addr >> 0) & 0xFF,
        (addr >> 8) & 0xFF,
        (addr >> 16) & 0xFF,
        (addr >> 24) & 0xFF
    ]
    
    # Write test value
    test_data = [
        (test_value >> 0) & 0xFF,
        (test_value >> 8) & 0xFF,
        (test_value >> 16) & 0xFF,
        (test_value >> 24) & 0xFF
    ]
    
    print(f"🔧 Writing 0x{test_value:08X}")
    write_frame = create_frame(0xA5, 0x20, addr_bytes, test_data)
    print(f"📤 Sending: {' '.join(f'{b:02X}' for b in write_frame)}")
    
    ser.write(bytes(write_frame))
    time.sleep(0.1)
    
    response = ser.read(8)
    if response:
        print(f"📥 Received: {' '.join(f'{b:02X}' for b in response)}")
        parsed = parse_response(response)
        if parsed:
            print(f"📋 Status: 0x{parsed['status']:02X}, Success: {parsed['success']}")
            if parsed['success']:
                print("✅ Write command accepted")
            else:
                print(f"❌ Write failed with status 0x{parsed['status']:02X}")
                return False
    else:
        print("❌ No write response received")
        return False
    
    # Read back value
    print("📖 Reading back...")
    read_frame = create_frame(0xA5, 0xA0, addr_bytes)
    print(f"📤 Sending: {' '.join(f'{b:02X}' for b in read_frame)}")
    
    ser.write(bytes(read_frame))
    time.sleep(0.1)
    
    response = ser.read(8)
    if response:
        print(f"📥 Received: {' '.join(f'{b:02X}' for b in response)}")
        parsed = parse_response(response)
        if parsed and parsed['type'] == 'read':
            print(f"📋 Status: 0x{parsed['status']:02X}, Success: {parsed['success']}")
            print(f"📋 Read value: 0x{parsed['value']:08X}")
            
            if not parsed['success']:
                print(f"❌ Read failed with status 0x{parsed['status']:02X}")
                return False
            
            if parsed['value'] == test_value:
                print("🎉 SUCCESS: Write-read cycle worked!")
                return True
            else:
                print(f"❌ MISMATCH: Expected 0x{test_value:08X}, got 0x{parsed['value']:08X}")
                if (parsed['value'] & 0xFFFFF000) == 0xF0220000:
                    print("🚨 Still showing test pattern generator - AXI write not reaching registers")
                return False
    else:
        print("❌ No read response received")
        return False

def main():
    """Main test function"""
    print("🧪 Updated REG_TEST Status Code Test")
    print("Handles STATUS 0x00, 0x40, 0x80 as success codes")
    print("=" * 60)
    
    try:
        # Connect to UART
        ser = serial.Serial('COM3', 115200, timeout=2)
        print("✅ Connected to COM3")
        time.sleep(0.1)
        
        # Clear any pending data
        ser.reset_input_buffer()
        
        # Test cases
        test_cases = [
            (0x00001020, 0x11111111, "REG_TEST_0"),
            (0x00001024, 0x22222222, "REG_TEST_1"), 
            (0x00001028, 0x33333333, "REG_TEST_2"),
            (0x0000102C, 0x44444444, "REG_TEST_3")
        ]
        
        results = []
        for addr, value, name in test_cases:
            result = test_register_write_read(ser, addr, value, name)
            results.append((name, result))
        
        # Summary
        print("\n" + "=" * 60)
        print("📊 TEST SUMMARY")
        print("=" * 60)
        success_count = 0
        for name, result in results:
            status = "✅ PASSED" if result else "❌ FAILED"
            print(f"   {name}: {status}")
            if result:
                success_count += 1
        
        print(f"\nOverall Results:")
        print(f"   Successful registers: {success_count}/{len(results)}")
        print(f"   Success rate: {100.0 * success_count / len(results):.1f}%")
        
        if success_count == len(results):
            print("\n🎉 ALL TESTS PASSED - REG_TEST registers working correctly!")
            return True
        elif success_count > 0:
            print(f"\n⚠️  PARTIAL SUCCESS - {success_count}/{len(results)} registers working")
            return False
        else:
            print("\n🚨 ALL TESTS FAILED - Check AXI implementation and ILA analysis")
            return False
            
    except Exception as e:
        print(f"❌ Test failed: {e}")
        return False
    finally:
        if 'ser' in locals():
            ser.close()
            print("🔌 Disconnected")

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)