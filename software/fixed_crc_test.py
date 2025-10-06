#!/usr/bin/env python3
"""
AXIUART Fixed CRC Register Test
Correct CRC8 implementation to fix Status=0x40 errors
"""

import serial
import struct
import time

# プロトコル定数
PROTOCOL_SOF_HOST = 0xA5

class FixedRegisterTest:
    def __init__(self, port='COM3', baudrate=115200):
        self.ser = serial.Serial(port, baudrate, timeout=2)
        print(f"✅ Connected to {port} at {baudrate} baud")
    
    def crc8_correct(self, data):
        """正しいCRC8計算 (polynomial 0x2F)"""
        crc = 0x00
        for byte in data:
            crc ^= byte
            for _ in range(8):
                if crc & 0x80:
                    crc = (crc << 1) ^ 0x2F
                else:
                    crc <<= 1
                crc &= 0xFF
        return crc
    
    def read_register_fixed(self, addr):
        """正しいCRCでレジスタ読み取り"""
        # Build read command frame
        frame = bytearray([PROTOCOL_SOF_HOST, 0xA0])  # SOF + READ_CMD
        frame.extend(struct.pack('<I', addr))         # 32-bit address, little-endian
        frame.extend([0x00])                          # LEN=0
        
        # Calculate correct CRC
        crc = self.crc8_correct(frame[1:])  # CRC excludes SOF
        frame.append(crc)
        
        print(f"📤 Sending: {' '.join(f'{b:02X}' for b in frame)}")
        
        # Send and receive
        self.ser.write(frame)
        time.sleep(0.1)  # Allow processing time
        response = self.ser.read(20)
        
        if response:
            print(f"📥 Received ({len(response)} bytes): {' '.join(f'{b:02X}' for b in response)}")
            return response
        else:
            print("❌ No response")
            return None
    
    def write_register_fixed(self, addr, value):
        """正しいCRCでレジスタ書き込み"""
        # Build write command frame
        frame = bytearray([PROTOCOL_SOF_HOST, 0x20])  # SOF + WRITE_CMD
        frame.extend(struct.pack('<I', addr))         # 32-bit address, little-endian
        frame.extend([0x00])                          # LEN=0
        frame.extend(struct.pack('<I', value))        # 32-bit data, little-endian
        
        # Calculate correct CRC
        crc = self.crc8_correct(frame[1:])  # CRC excludes SOF
        frame.append(crc)
        
        print(f"📤 Sending: {' '.join(f'{b:02X}' for b in frame)}")
        
        # Send and receive
        self.ser.write(frame)
        time.sleep(0.1)
        response = self.ser.read(20)
        
        if response:
            print(f"📥 Received ({len(response)} bytes): {' '.join(f'{b:02X}' for b in response)}")
            return response
        else:
            print("❌ No response")
            return None
    
    def close(self):
        self.ser.close()
        print("🔌 Disconnected from UART")

def main():
    print("🔧 AXIUART Fixed CRC Register Test")
    print("=" * 50)
    
    tester = FixedRegisterTest()
    
    try:
        # Test 1: Version Register Read (expected value: 0x00010000)
        print("\n📍 Test 1: Version Register Read (0x0000101C)")
        response = tester.read_register_fixed(0x0000101C)
        
        if response and len(response) >= 8:
            sof, status, cmd = response[0], response[1], response[2]
            data_bytes = response[3:7]
            version_value = struct.unpack('<I', data_bytes)[0]
            print(f"   Version: 0x{version_value:08X}")
            if version_value == 0x00010000:
                print("   ✅ Version register correct!")
        
        # Test 2: Test Register 0 Write and Read
        print("\n📍 Test 2: Test Register Write & Read")
        test_addr = 0x00001020
        test_value = 0xCAFEBABE
        
        print(f"   Writing 0x{test_value:08X} to 0x{test_addr:08X}")
        write_response = tester.write_register_fixed(test_addr, test_value)
        
        if write_response and len(write_response) >= 2:
            sof, status = write_response[0], write_response[1]
            if status == 0x80 or status == 0x00:  # Check both possible OK values
                print("   ✅ Write successful")
                
                # Read back
                print("   Reading back...")
                read_response = tester.read_register_fixed(test_addr)
                
                if read_response and len(read_response) >= 8:
                    data_bytes = read_response[3:7]
                    readback_value = struct.unpack('<I', data_bytes)[0]
                    print(f"   Read-back: 0x{readback_value:08X}")
                    
                    if readback_value == test_value:
                        print("   🎉 SUCCESS: Register write/read works perfectly!")
                    else:
                        print(f"   ❌ MISMATCH: Expected 0x{test_value:08X}, got 0x{readback_value:08X}")
            else:
                print(f"   ❌ Write failed: STATUS=0x{status:02X}")
    
    except Exception as e:
        print(f"❌ Error: {e}")
    
    finally:
        tester.close()
    
    print("\n" + "=" * 50)
    print("🔧 Fixed CRC test complete")

if __name__ == "__main__":
    main()