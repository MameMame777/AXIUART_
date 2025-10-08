#!/usr/bin/env python3
"""
UART Protocol Debug Tool
Analyze actual FPGA responses to understand the protocol
"""

import serial
import time
import struct

class ProtocolDebugger:
    def __init__(self, port='COM3', baudrate=115200):
        self.port = port
        self.baudrate = baudrate
        self.serial = None

    def connect(self):
        """Connect to serial port"""
        try:
            self.serial = serial.Serial(self.port, self.baudrate, timeout=2)
            time.sleep(0.1)
            print(f"✅ Connected to {self.port}")
            return True
        except Exception as e:
            print(f"❌ Connection failed: {e}")
            return False

    def disconnect(self):
        """Disconnect from serial port"""
        if self.serial and self.serial.is_open:
            self.serial.close()
            print("🔌 Disconnected")

    def calculate_crc8(self, data):
        """Calculate CRC-8 with polynomial 0x07"""
        crc = 0x00
        for byte in data:
            crc ^= byte
            for _ in range(8):
                if crc & 0x80:
                    crc = (crc << 1) ^ 0x07
                else:
                    crc <<= 1
                crc &= 0xFF
        return crc

    def hex_dump(self, data, label="Data"):
        """Print hex dump of data"""
        hex_str = " ".join(f"{b:02X}" for b in data)
        print(f"{label}: {hex_str} ({len(data)} bytes)")

    def test_read_protocol(self, address):
        """Test read with current protocol and dump response"""
        print(f"\n🔍 Testing READ protocol for address 0x{address:08X}")
        print("-" * 60)
        
        try:
            # Build read request: SOF (0xA5) + CMD (0xA0) + ADDR + CRC
            cmd_byte = 0xA0  # Read command: RW=1, INC=0, SIZE=10(32-bit), LEN=0000(1 beat)
            
            frame_data = bytearray()
            frame_data.append(cmd_byte)
            frame_data.extend(struct.pack('<I', address))
            
            crc = self.calculate_crc8(frame_data)
            
            complete_frame = bytearray([0xA5])
            complete_frame.extend(frame_data)
            complete_frame.append(crc)
            
            print("📤 Sending READ request:")
            self.hex_dump(complete_frame, "REQUEST")
            
            self.serial.write(complete_frame)
            
            # Read response - try different byte counts
            for byte_count in [4, 7, 8, 11, 15]:
                print(f"\n📥 Reading {byte_count} bytes:")
                response = self.serial.read(byte_count)
                self.hex_dump(response, f"RESPONSE({byte_count})")
                
                if len(response) > 0:
                    break
                    
            return response
            
        except Exception as e:
            print(f"❌ Error: {e}")
            return None

    def test_write_protocol(self, address, value):
        """Test write with current protocol and dump response"""
        print(f"\n🔍 Testing WRITE protocol for address 0x{address:08X}, value 0x{value:08X}")
        print("-" * 60)
        
        try:
            # Build write request: SOF (0xA5) + CMD (0x20) + ADDR + DATA + CRC
            cmd_byte = 0x20  # Write command: RW=0, INC=0, SIZE=10(32-bit), LEN=0000(1 beat)
            
            frame_data = bytearray()
            frame_data.append(cmd_byte)
            frame_data.extend(struct.pack('<I', address))
            frame_data.extend(struct.pack('<I', value))
            
            crc = self.calculate_crc8(frame_data)
            
            complete_frame = bytearray([0xA5])
            complete_frame.extend(frame_data)
            complete_frame.append(crc)
            
            print("📤 Sending WRITE request:")
            self.hex_dump(complete_frame, "REQUEST")
            
            self.serial.write(complete_frame)
            
            # Read response - try different byte counts
            for byte_count in [4, 7, 8, 11, 15]:
                print(f"\n📥 Reading {byte_count} bytes:")
                response = self.serial.read(byte_count)
                self.hex_dump(response, f"RESPONSE({byte_count})")
                
                if len(response) > 0:
                    break
                    
            return response
            
        except Exception as e:
            print(f"❌ Error: {e}")
            return None

    def test_legacy_protocol(self, address):
        """Test with legacy ASCII protocol"""
        print(f"\n🔍 Testing LEGACY ASCII protocol for address 0x{address:08X}")
        print("-" * 60)
        
        try:
            # Legacy protocol: 'R' + 4 bytes address
            cmd = b'R' + struct.pack('<I', address)
            
            print("📤 Sending LEGACY READ request:")
            self.hex_dump(cmd, "REQUEST")
            
            self.serial.write(cmd)
            
            # Read response
            for byte_count in [4, 5, 8, 11, 15]:
                print(f"\n📥 Reading {byte_count} bytes:")
                response = self.serial.read(byte_count)
                self.hex_dump(response, f"RESPONSE({byte_count})")
                
                if len(response) > 0:
                    break
                    
            return response
            
        except Exception as e:
            print(f"❌ Error: {e}")
            return None

    def run_comprehensive_protocol_test(self):
        """Run comprehensive protocol debugging"""
        print("🔬 UART Protocol Debugging Session")
        print("=" * 80)
        
        test_address = 0x00001020  # REG_TEST_0
        test_value = 0x12345678
        
        # Test 1: Current binary protocol READ
        self.test_read_protocol(test_address)
        
        # Test 2: Current binary protocol WRITE  
        self.test_write_protocol(test_address, test_value)
        
        # Test 3: Legacy ASCII protocol
        self.test_legacy_protocol(test_address)

def main():
    debugger = ProtocolDebugger()
    
    if not debugger.connect():
        return
        
    try:
        debugger.run_comprehensive_protocol_test()
    finally:
        debugger.disconnect()

if __name__ == "__main__":
    main()