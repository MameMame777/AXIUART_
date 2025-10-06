#!/usr/bin/env python3
"""
AXIUART Simple Register Test
Basic connectivity and version register test
"""

import serial
import struct
import time

# プロトコル定数
PROTOCOL_SOF_HOST = 0xA5

class SimpleRegisterTest:
    def __init__(self, port='COM3', baudrate=115200):
        self.ser = serial.Serial(port, baudrate, timeout=2)
        print(f"✅ Connected to {port} at {baudrate} baud")
    
    def crc8(self, data):
        """CRC8計算 (polynomial 0x2F)"""
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
    
    def read_register(self, addr):
        """レジスタ読み取り"""
        # Build read command frame
        frame = bytearray([PROTOCOL_SOF_HOST, 0xA0])  # SOF + READ_CMD
        frame.extend(struct.pack('<I', addr))         # 32-bit address, little-endian
        frame.extend([0x00])                          # LEN=0
        
        # Calculate and append CRC
        crc = self.crc8(frame[1:])  # CRC excludes SOF
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
    
    def close(self):
        self.ser.close()
        print("🔌 Disconnected from UART")

def main():
    print("🔍 AXIUART Simple Register Test")
    print("=" * 50)
    
    tester = SimpleRegisterTest()
    
    try:
        # Test 1: Version Register (should return 0x00010000)
        print("\n📍 Test 1: Version Register (0x0000101C)")
        print("Expected frame: A5 A0 1C 10 00 00 90")
        response = tester.read_register(0x0000101C)
        
        # Test 2: Control Register (0x00001000)
        print("\n📍 Test 2: Control Register (0x00001000)")
        print("Expected frame: A5 A0 00 10 00 00 57")
        response = tester.read_register(0x00001000)
        
        # Test 3: Test Register 0 (0x00001020)
        print("\n📍 Test 3: Test Register 0 (0x00001020)")
        print("Expected frame: A5 A0 20 10 00 00 BB")
        response = tester.read_register(0x00001020)
        
        # Analyze any response received
        if response and len(response) >= 2:
            sof, status = response[0], response[1]
            print(f"\n📊 Response Analysis:")
            print(f"   SOF: 0x{sof:02X} (expected: 0xAD)")
            print(f"   STATUS: 0x{status:02X}")
            
            if status == 0x80:
                print("   ✅ STATUS OK (0x80)")
            elif status == 0x40:
                print("   ⚠️  STATUS Error (0x40) - possible address/access issue")
            elif status == 0x00:
                print("   ✅ STATUS OK (0x00) - protocol spec value")
            else:
                print(f"   ❓ Unknown STATUS: 0x{status:02X}")
    
    except Exception as e:
        print(f"❌ Error: {e}")
    
    finally:
        tester.close()
    
    print("\n" + "=" * 50)
    print("🔍 Simple test complete")

if __name__ == "__main__":
    main()