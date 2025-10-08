#!/usr/bin/env python3
"""
REG_TEST ILA Debug Test
Fast test to trigger ILA for debugging AXI write issues
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
            'crc': crc
        }
    else:  # Write response
        crc = data[3] if len(data) >= 4 else 0
        return {
            'type': 'write',
            'sof': sof,
            'status': status,
            'cmd_echo': cmd_echo,
            'crc': crc
        }

def test_ila_trigger():
    """Perform quick test to trigger ILA for debugging"""
    
    try:
        # Connect to UART
        ser = serial.Serial('COM3', 115200, timeout=2)
        print("🔗 Connected to COM3 for ILA trigger test")
        time.sleep(0.1)
        
        # Clear any pending data
        ser.reset_input_buffer()
        
        print("\n🎯 ILA Debug Test - Triggering AXI Write Transaction")
        print("=" * 60)
        
        # Test REG_TEST_0 write - this should trigger ILA
        addr_bytes = [0x20, 0x10, 0x00, 0x00]  # 0x00001020 in little endian
        test_data = [0xAA, 0xBB, 0xCC, 0xDD]   # Test pattern
        
        print(f"📤 Writing test pattern 0xDDCCBBAA to REG_TEST_0 (0x00001020)")
        
        frame = create_frame(0xA5, 0x20, addr_bytes, test_data)
        print(f"📤 Sending: {' '.join(f'{b:02X}' for b in frame)}")
        
        ser.write(bytes(frame))
        time.sleep(0.1)
        
        # Read response
        response = ser.read(8)
        if response:
            print(f"📥 Received: {' '.join(f'{b:02X}' for b in response)}")
            parsed = parse_response(response)
            if parsed:
                print(f"📋 Status: 0x{parsed['status']:02X}, CMD_ECHO: 0x{parsed['cmd_echo']:02X}")
                if parsed['status'] == 0x80:
                    print("✅ Write command received by FPGA")
                else:
                    print(f"❌ Error status: 0x{parsed['status']:02X}")
        else:
            print("❌ No response received")
        
        print("\n📖 Reading back to verify ILA capture...")
        
        # Read back the value
        read_frame = create_frame(0xA5, 0xA0, addr_bytes)
        print(f"📤 Sending: {' '.join(f'{b:02X}' for b in read_frame)}")
        
        ser.write(bytes(read_frame))
        time.sleep(0.1)
        
        response = ser.read(8)
        if response:
            print(f"📥 Received: {' '.join(f'{b:02X}' for b in response)}")
            parsed = parse_response(response)
            if parsed and parsed['type'] == 'read':
                print(f"📋 Read value: 0x{parsed['value']:08X}")
                if parsed['value'] == 0xDDCCBBAA:
                    print("🎉 SUCCESS: Write operation worked!")
                    return True
                else:
                    print(f"❌ MISMATCH: Expected 0xDDCCBBAA, got 0x{parsed['value']:08X}")
                    if (parsed['value'] & 0xFFFFF000) == 0xF0220000:
                        print("🚨 Still showing test pattern generator - AXI write not reaching registers")
                    return False
        else:
            print("❌ No read response received")
            return False
            
    except Exception as e:
        print(f"❌ Test failed: {e}")
        return False
    finally:
        if 'ser' in locals():
            ser.close()
            print("🔌 Disconnected")

if __name__ == "__main__":
    print("🧪 REG_TEST ILA Debug Trigger Test")
    print("This test sends a write command to trigger ILA capture")
    print("Check ILA waveforms for AXI handshake analysis\n")
    
    success = test_ila_trigger()
    
    print("\n" + "=" * 60)
    if success:
        print("🎉 Test completed successfully - check ILA for write transaction details")
    else:
        print("❌ Test shows AXI write not reaching registers - analyze ILA waveforms")
        print("🔍 Key signals to check in ILA:")
        print("   - awvalid_int: Should assert during WRITE_ADDR state")
        print("   - axi_awready: Should respond from Register_Block")
        print("   - aw_handshake: Should pulse when both are high")
        print("   - state: Should progress WRITE_ADDR → WRITE_DATA → WRITE_RESP")
        print("   - timeout_counter: Should reset, not reach 2500")
        print("   - axi_state (Register_Block): Should follow AXI slave protocol")
    
    sys.exit(0 if success else 1)