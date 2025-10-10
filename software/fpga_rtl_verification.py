#!/usr/bin/env python3
"""
FPGA RTL Verification Script
Verify if the new RTL has been correctly deployed to FPGA
"""

import serial
import time
import struct

class FPGARTLVerification:
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
    
    def send_basic_read(self, addr):
        """Send basic read command with correct protocol"""
        frame = bytearray()
        frame.append(0xA5)  # SOF
        frame.append(0x80)  # READ command (0x80)
        frame.extend(struct.pack('<I', addr))  # Address (little-endian)
        frame.extend([0x00, 0x00])  # No data for read
        
        # Calculate CRC
        crc = self.crc8_calculate(frame[1:])
        frame.append(crc)
        
        print(f"📤 Sending: {' '.join(f'{b:02X}' for b in frame)}")
        
        # Send
        self.serial.reset_input_buffer()
        self.serial.write(frame)
        self.serial.flush()
        time.sleep(0.1)
        
        # Receive
        response = self.serial.read(100)
        if response:
            print(f"📥 Received: {' '.join(f'{b:02X}' for b in response)}")
            return response
        else:
            print("❌ No response")
            return None
    
    def verify_pattern_generator(self):
        """Check if test pattern generator is still active"""
        print("\n🔍 Checking for Test Pattern Generator...")
        print("=" * 60)
        
        # Test addresses that should contain register values
        test_addresses = [
            0x00001020,  # REG_TEST_0
            0x00001024,  # REG_TEST_1  
            0x00001028,  # REG_TEST_2
            0x0000102C   # REG_TEST_3
        ]
        
        pattern_detected = False
        
        for addr in test_addresses:
            print(f"\n📍 Testing address 0x{addr:08X}")
            response = self.send_basic_read(addr)
            
            if response and len(response) >= 8:
                sof, status = response[0], response[1]
                data_bytes = response[3:7]
                data_value = struct.unpack('<I', data_bytes)[0]
                
                print(f"   SOF: 0x{sof:02X}, STATUS: 0x{status:02X}")
                print(f"   Data: 0x{data_value:08X}")
                
                # Check for test pattern generator signature
                if (data_value & 0xFFFFFF00) == 0xF0202200:
                    print(f"   🚨 TEST PATTERN GENERATOR DETECTED: 0xF02022XX")
                    pattern_detected = True
                elif data_value == 0xDEADBEEF:
                    print(f"   ✅ Expected register value detected")
                elif data_value == 0x12345678:
                    print(f"   ✅ Expected register value detected") 
                else:
                    print(f"   ❓ Unknown value: 0x{data_value:08X}")
                    
            else:
                print(f"   ❌ Invalid response")
        
        return pattern_detected
    
    def check_register_functionality(self):
        """Check if registers are functioning correctly"""
        print("\n🔍 Checking Register Functionality...")
        print("=" * 60)
        
        # Try to write to REG_TEST_0
        addr = 0x00001020
        test_value = 0x12345678
        
        print(f"📝 Writing 0x{test_value:08X} to 0x{addr:08X}")
        
        # Write command
        frame = bytearray()
        frame.append(0xA5)  # SOF
        frame.append(0x00)  # WRITE command (0x00)
        frame.extend(struct.pack('<I', addr))  # Address
        frame.extend(struct.pack('<I', test_value))  # Data
        
        crc = self.crc8_calculate(frame[1:])
        frame.append(crc)
        
        print(f"📤 Write frame: {' '.join(f'{b:02X}' for b in frame)}")
        
        self.serial.reset_input_buffer()
        self.serial.write(frame)
        self.serial.flush()
        time.sleep(0.1)
        
        write_response = self.serial.read(100)
        if write_response:
            print(f"📥 Write response: {' '.join(f'{b:02X}' for b in write_response)}")
        
        # Read back
        time.sleep(0.1)
        print(f"📖 Reading back from 0x{addr:08X}")
        read_response = self.send_basic_read(addr)
        
        if read_response and len(read_response) >= 8:
            data_bytes = read_response[3:7]
            read_value = struct.unpack('<I', data_bytes)[0]
            print(f"📖 Read value: 0x{read_value:08X}")
            
            if read_value == test_value:
                print("✅ Register write/read successful!")
                return True
            else:
                print(f"❌ Value mismatch: wrote 0x{test_value:08X}, read 0x{read_value:08X}")
                return False
        else:
            print("❌ Read failed")
            return False
    
    def run_verification(self):
        """Run complete RTL verification"""
        print("🚀 FPGA RTL Verification")
        print("=" * 80)
        print("Purpose: Verify if new RTL has been correctly deployed")
        print("Expected: No test pattern generator, working registers")
        print("=" * 80)
        
        # Check for pattern generator
        pattern_active = self.verify_pattern_generator()
        
        # Check register functionality
        registers_working = self.check_register_functionality()
        
        # Summary
        print("\n" + "=" * 80)
        print("📊 VERIFICATION SUMMARY")
        print("=" * 80)
        
        if pattern_active:
            print("🚨 TEST PATTERN GENERATOR: STILL ACTIVE")
            print("   → Old RTL is still running on FPGA")
            print("   → New RTL deployment may have failed")
        else:
            print("✅ TEST PATTERN GENERATOR: NOT DETECTED")
            print("   → Old RTL appears to be removed")
        
        if registers_working:
            print("✅ REGISTER FUNCTIONALITY: WORKING")
            print("   → New RTL registers are functional")
        else:
            print("❌ REGISTER FUNCTIONALITY: NOT WORKING")
            print("   → New RTL may not be correctly deployed")
        
        print("\n🎯 CONCLUSION:")
        if not pattern_active and registers_working:
            print("✅ NEW RTL SUCCESSFULLY DEPLOYED")
        elif pattern_active:
            print("❌ OLD RTL STILL ACTIVE - DEPLOYMENT FAILED")
        else:
            print("❓ UNCLEAR STATE - FURTHER INVESTIGATION NEEDED")
        
        return not pattern_active and registers_working

def main():
    verifier = FPGARTLVerification()
    
    if not verifier.connect():
        return
    
    try:
        success = verifier.run_verification()
        exit_code = 0 if success else 1
        print(f"\n🔚 Verification complete (exit code: {exit_code})")
        
    finally:
        verifier.disconnect()

if __name__ == "__main__":
    main()