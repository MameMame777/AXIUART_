#!/usr/bin/env python3
"""
Test Register Access Script
Direct access to newly added test registers (0x00001020-0x0000102C)
Created: 2025-10-05

This script provides direct access to the test registers for debugging
and validation of the UART-AXI bridge functionality.
"""

import serial
import time
import struct
from typing import Optional, List, Tuple

class TestRegisterAccess:
    """Simplified test register access with SOF tolerance"""
    
    def __init__(self, port: str = "COM3", baudrate: int = 115200):
        self.port = port
        self.baudrate = baudrate
        self.serial = None
        
        # Test register addresses
        self.REG_TEST_0 = 0x00001020  # Pure read/write test
        self.REG_TEST_1 = 0x00001024  # Pattern test  
        self.REG_TEST_2 = 0x00001028  # Increment test
        self.REG_TEST_3 = 0x0000102C  # Mirror test
        
        # Protocol constants
        self.SOF_HOST_TO_DEVICE = 0xA5
        self.SOF_DEVICE_TO_HOST = 0x5A
        self.SOF_ALTERNATE = 0xAD  # Observed alternate SOF
        
        self.CMD_READ = 0xA0
        self.CMD_WRITE = 0x20
        
    def connect(self) -> bool:
        """Connect to UART"""
        try:
            self.serial = serial.Serial(
                port=self.port,
                baudrate=self.baudrate,
                bytesize=8,
                parity='N',
                stopbits=1,
                timeout=2.0
            )
            time.sleep(0.1)  # Allow connection to stabilize
            print(f"✅ Connected to {self.port} at {self.baudrate} baud")
            return True
        except Exception as e:
            print(f"❌ Connection failed: {e}")
            return False
    
    def disconnect(self):
        """Disconnect from UART"""
        if self.serial and self.serial.is_open:
            self.serial.close()
            print("🔌 Disconnected")
    
    def crc8_calculate(self, data: bytes) -> int:
        """Calculate CRC8 using polynomial 0x07"""
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
    
    def send_command(self, cmd: int, addr: int, data: Optional[int] = None) -> Optional[bytes]:
        """Send command and receive response with SOF tolerance"""
        if not self.serial or not self.serial.is_open:
            print("❌ UART not connected")
            return None
        
        try:
            # Clear input buffer
            self.serial.reset_input_buffer()
            
            # Build command frame
            if data is not None:  # Write command
                frame_data = struct.pack('<BBHIL', 
                                       self.SOF_HOST_TO_DEVICE,
                                       cmd, 
                                       addr & 0xFFFF,
                                       (addr >> 16) & 0xFFFF,
                                       data)
            else:  # Read command
                frame_data = struct.pack('<BBHI', 
                                       self.SOF_HOST_TO_DEVICE,
                                       cmd,
                                       addr & 0xFFFF, 
                                       (addr >> 16) & 0xFFFF)
            
            # Calculate and append CRC
            crc = self.crc8_calculate(frame_data[1:])  # Exclude SOF from CRC
            frame = frame_data + bytes([crc])
            
            # Send command
            self.serial.write(frame)
            self.serial.flush()
            
            # Receive response
            time.sleep(0.05)  # Wait for response
            
            # Read response with flexible SOF handling
            response = self.serial.read(32)  # Read up to 32 bytes
            
            if len(response) < 3:
                print(f"❌ Short response: {len(response)} bytes")
                return None
            
            # Check for valid SOF (accept both 0x5A and 0xAD)
            sof = response[0]
            if sof not in [self.SOF_DEVICE_TO_HOST, self.SOF_ALTERNATE]:
                print(f"⚠️  Unexpected SOF: 0x{sof:02X}")
                # Continue processing anyway
            
            return response
            
        except Exception as e:
            print(f"❌ Command error: {e}")
            return None
    
    def read_register(self, addr: int) -> Optional[int]:
        """Read 32-bit register value"""
        print(f"📖 Reading register 0x{addr:08X}")
        
        response = self.send_command(self.CMD_READ, addr)
        if response is None or len(response) < 8:
            print("❌ Read failed")
            return None
        
        try:
            # Parse response: SOF + STATUS + CMD + DATA + CRC
            sof, status, cmd_echo = struct.unpack('<BBB', response[0:3])
            
            if len(response) >= 8:
                data = struct.unpack('<L', response[3:7])[0]
                crc_received = response[7]
                
                # Verify CRC
                crc_calculated = self.crc8_calculate(response[1:7])
                if crc_received != crc_calculated:
                    print(f"⚠️  CRC mismatch: got 0x{crc_received:02X}, expected 0x{crc_calculated:02X}")
                
                print(f"✅ Read value: 0x{data:08X} (status=0x{status:02X})")
                return data
            else:
                print(f"❌ Response too short: {len(response)} bytes")
                return None
                
        except Exception as e:
            print(f"❌ Parse error: {e}")
            return None
    
    def write_register(self, addr: int, value: int) -> bool:
        """Write 32-bit register value"""
        print(f"📝 Writing 0x{value:08X} to register 0x{addr:08X}")
        
        response = self.send_command(self.CMD_WRITE, addr, value)
        if response is None or len(response) < 4:
            print("❌ Write failed")
            return False
        
        try:
            # Parse response: SOF + STATUS + CMD + CRC
            sof, status, cmd_echo, crc_received = struct.unpack('<BBBB', response[0:4])
            
            if status == 0x00:
                print("✅ Write successful")
                return True
            else:
                print(f"❌ Write error: status=0x{status:02X}")
                return False
                
        except Exception as e:
            print(f"❌ Parse error: {e}")
            return False
    
    def test_register(self, addr: int, name: str) -> bool:
        """Test a single register with read/write operations"""
        print(f"\n🧪 Testing {name} (0x{addr:08X})")
        print("-" * 40)
        
        # Read initial value
        initial = self.read_register(addr)
        if initial is None:
            return False
        
        # Write test pattern
        test_value = 0x12345678
        if not self.write_register(addr, test_value):
            return False
        
        # Read back
        readback = self.read_register(addr)
        if readback != test_value:
            print(f"❌ Verification failed: expected 0x{test_value:08X}, got 0x{readback:08X}")
            return False
        
        # Restore original value
        self.write_register(addr, initial)
        
        print(f"✅ {name} test passed")
        return True
    
    def run_all_tests(self) -> bool:
        """Run comprehensive test on all test registers"""
        print("🧪 Test Register Validation Suite")
        print("=" * 50)
        
        if not self.connect():
            return False
        
        try:
            results = []
            
            # Test each register
            results.append(self.test_register(self.REG_TEST_0, "TEST_REG_0"))
            results.append(self.test_register(self.REG_TEST_1, "TEST_REG_1")) 
            results.append(self.test_register(self.REG_TEST_2, "TEST_REG_2"))
            results.append(self.test_register(self.REG_TEST_3, "TEST_REG_3"))
            
            # Pattern test
            print(f"\n🎨 Pattern Test")
            print("-" * 40)
            patterns = [0x00000000, 0xFFFFFFFF, 0xAAAA5555, 0x55555555]
            pattern_ok = True
            
            for i, pattern in enumerate(patterns):
                addr = [self.REG_TEST_0, self.REG_TEST_1, self.REG_TEST_2, self.REG_TEST_3][i]
                if self.write_register(addr, pattern):
                    readback = self.read_register(addr)
                    if readback == pattern:
                        print(f"✅ Pattern 0x{pattern:08X} @ REG_TEST_{i}")
                    else:
                        print(f"❌ Pattern 0x{pattern:08X} @ REG_TEST_{i} failed")
                        pattern_ok = False
                else:
                    pattern_ok = False
            
            results.append(pattern_ok)
            
            # Summary
            print(f"\n📊 Test Summary")
            print("=" * 50)
            passed = sum(results)
            total = len(results)
            
            print(f"Tests passed: {passed}/{total}")
            
            if passed == total:
                print("🎉 All tests passed!")
                return True
            else:
                print("❌ Some tests failed")
                return False
                
        finally:
            self.disconnect()

def main():
    """Main test execution"""
    tester = TestRegisterAccess()
    success = tester.run_all_tests()
    
    if success:
        print("\n✅ Test register validation completed successfully")
    else:
        print("\n❌ Test register validation failed")
    
    return success

if __name__ == "__main__":
    main()