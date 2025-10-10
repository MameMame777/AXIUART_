#!/usr/bin/env python3
"""
Correct Protocol Test
Test with proper UART-AXI4 protocol format
"""

import serial
import time
import struct

class CorrectProtocolTest:
    def __init__(self, port='COM3', baudrate=115200):
        self.port = port
        self.baudrate = baudrate
        self.serial = None
        
    def connect(self):
        """Connect to FPGA"""
        try:
            self.serial = serial.Serial(self.port, self.baudrate, timeout=2)
            time.sleep(0.1)
            print(f"✅ Connected to {self.port}")
            return True
        except Exception as e:
            print(f"❌ Connection failed: {e}")
            return False
    
    def disconnect(self):
        if self.serial and self.serial.is_open:
            self.serial.close()
            print("🔌 Disconnected")
    
    def crc8_calculate(self, data):
        """Calculate CRC-8 with polynomial 0x07"""
        crc = 0x00
        for byte in data:
            crc ^= byte
            for _ in range(8):
                if crc & 0x80:
                    crc = (crc << 1) ^ 0x07
                else:
                    crc = crc << 1
                crc &= 0xFF
        return crc
    
    def test_read_command(self, addr):
        """Test with correct READ command format according to protocol spec"""
        print(f"\n📖 Testing READ from 0x{addr:08X}")
        print("-" * 50)
        
        # Build correct READ command according to protocol spec v0.1.1
        frame = bytearray()
        frame.append(0xA5)  # SOF (host→device)
        
        # CMD for READ: RW=1, INC=0, SIZE=32bit(10), LEN=1
        # Bit pattern: 1_0_10_0001 = 0x91
        frame.append(0x91)  # READ command
        
        # Address (little-endian, 4 bytes)
        frame.extend(struct.pack('<I', addr))
        
        # Calculate CRC over CMD + ADDR (bytes 1-5)
        crc = self.crc8_calculate(frame[1:])
        frame.append(crc)
        
        print(f"📤 Sending READ: {' '.join(f'{b:02X}' for b in frame)}")
        print(f"   Format: SOF(A5) CMD(91) ADDR({addr:08X}) CRC({crc:02X})")
        
        # Send
        self.serial.reset_input_buffer()
        self.serial.write(frame)
        self.serial.flush()
        time.sleep(0.1)
        
        # Receive
        response = self.serial.read(100)
        if response:
            print(f"📥 Received: {' '.join(f'{b:02X}' for b in response)}")
            self.analyze_response(response, 'READ')
            return response
        else:
            print("❌ No response")
            return None
    
    def test_write_command(self, addr, value):
        """Test with correct WRITE command format according to protocol spec"""
        print(f"\n📝 Testing WRITE 0x{value:08X} to 0x{addr:08X}")
        print("-" * 50)
        
        # Build correct WRITE command according to protocol spec v0.1.1
        frame = bytearray()
        frame.append(0xA5)  # SOF (host→device)
        
        # CMD for WRITE: RW=0, INC=0, SIZE=32bit(10), LEN=1
        # Bit pattern: 0_0_10_0001 = 0x21
        frame.append(0x21)  # WRITE command
        
        # Address (little-endian, 4 bytes)
        frame.extend(struct.pack('<I', addr))
        
        # Data (little-endian, 4 bytes for 32-bit)
        frame.extend(struct.pack('<I', value))
        
        # Calculate CRC over CMD + ADDR + DATA (bytes 1-9)
        crc = self.crc8_calculate(frame[1:])
        frame.append(crc)
        
        print(f"📤 Sending WRITE: {' '.join(f'{b:02X}' for b in frame)}")
        print(f"   Format: SOF(A5) CMD(21) ADDR({addr:08X}) DATA({value:08X}) CRC({crc:02X})")
        
        # Send
        self.serial.reset_input_buffer()
        self.serial.write(frame)
        self.serial.flush()
        time.sleep(0.1)
        
        # Receive
        response = self.serial.read(100)
        if response:
            print(f"📥 Received: {' '.join(f'{b:02X}' for b in response)}")
            self.analyze_response(response, 'WRITE')
            return response
        else:
            print("❌ No response")
            return None
    
    def analyze_response(self, response, operation_type):
        """Analyze response according to protocol spec"""
        if not response:
            return
        
        print(f"📊 Response Analysis ({operation_type}):")
        
        if len(response) >= 2:
            sof, status = response[0], response[1]
            print(f"   SOF: 0x{sof:02X} (expected: 0x5A)")
            print(f"   STATUS: 0x{status:02X}")
            
            # Analyze status code
            if status == 0x00:
                print("   ✅ STATUS: SUCCESS (0x00)")
            elif status == 0x01:
                print("   ❌ STATUS: CRC_ERR (0x01)")
            elif status == 0x02:
                print("   ❌ STATUS: CMD_ERR (0x02)")
            elif status == 0x03:
                print("   ❌ STATUS: ADDR_ALIGN (0x03)")
            elif status == 0x40:
                print("   ⚠️  STATUS: UNKNOWN ERROR (0x40)")
            elif status == 0x80:
                print("   ❓ STATUS: CUSTOM STATUS (0x80) - may be working")
            else:
                print(f"   ❓ STATUS: UNKNOWN (0x{status:02X})")
        
        if len(response) >= 3:
            cmd_echo = response[2]
            print(f"   CMD_ECHO: 0x{cmd_echo:02X}")
        
        if operation_type == 'READ' and len(response) >= 10:
            # For successful read: SOF + STATUS + CMD + ADDR + DATA + CRC
            addr_bytes = response[3:7]
            data_bytes = response[7:11]
            addr_echo = struct.unpack('<I', addr_bytes)[0]
            data_value = struct.unpack('<I', data_bytes)[0]
            print(f"   ADDR_ECHO: 0x{addr_echo:08X}")
            print(f"   DATA: 0x{data_value:08X}")
            
            # Check for test pattern generator
            if (data_value & 0xFFFFFF00) == 0xF0202200:
                print("   🚨 TEST PATTERN GENERATOR DETECTED!")
            else:
                print("   ✅ Data appears to be register content")
    
    def run_correct_protocol_test(self):
        """Run test with correct protocol format"""
        print("🚀 Correct Protocol Test")
        print("=" * 80)
        print("Testing with proper UART-AXI4 protocol v0.1.1 format")
        print("READ: SOF(A5) CMD(91) ADDR CRC")
        print("WRITE: SOF(A5) CMD(21) ADDR DATA CRC") 
        print("=" * 80)
        
        # Test addresses
        test_addresses = [
            0x00001020,  # REG_TEST_0
            0x00001024,  # REG_TEST_1
        ]
        
        for addr in test_addresses:
            # Test READ
            read_response = self.test_read_command(addr)
            
            # Test WRITE  
            test_value = 0x12345678
            write_response = self.test_write_command(addr, test_value)
            
            # Read back to verify
            if write_response:
                time.sleep(0.1)
                print(f"\n🔍 Reading back to verify write...")
                readback_response = self.test_read_command(addr)

def main():
    tester = CorrectProtocolTest()
    
    if not tester.connect():
        return
    
    try:
        tester.run_correct_protocol_test()
    finally:
        tester.disconnect()

if __name__ == "__main__":
    main()