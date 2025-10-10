#!/usr/bin/env python3
"""
Hardware Diagnostic Test for UART-AXI4 Bridge
Comprehensive testing to identify the root cause of 0x702022XX pattern

Purpose:
- Identify why hardware returns 0x702022XX instead of actual register values
- Compare hardware behavior with UVM simulation results
- Perform systematic hardware debugging
"""

import serial
import time
import struct
import sys
from dataclasses import dataclass
from typing import List, Optional, Tuple

# UART-AXI4 Protocol Constants (v0.1.1)
SOF_BYTE = 0xA5
RESP_SOF_BYTE = 0x5A

# Command encoding
CMD_READ_8BIT = 0x80
CMD_READ_16BIT = 0x81
CMD_READ_32BIT = 0x82
CMD_WRITE_8BIT = 0x00
CMD_WRITE_16BIT = 0x01
CMD_WRITE_32BIT = 0x02

# Test register addresses
REG_TEST_0 = 0x00001020
REG_TEST_1 = 0x00001024
REG_TEST_2 = 0x00001028
REG_TEST_3 = 0x0000102C

# Expected initial values from RTL
EXPECTED_REG_TEST_0 = 0xDEADBEEF
EXPECTED_REG_TEST_1 = 0x12345678
EXPECTED_REG_TEST_2 = 0xABCDEF00
EXPECTED_REG_TEST_3 = 0x00000000

@dataclass
class TestResult:
    test_name: str
    expected: int
    actual: int
    success: bool
    error_msg: str = ""

class UARTAxi4Diagnostic:
    def __init__(self, port: str = 'COM3', baudrate: int = 115200):
        self.port = port
        self.baudrate = baudrate
        self.ser: Optional[serial.Serial] = None
        self.test_results: List[TestResult] = []

    def connect(self) -> bool:
        """Connect to UART port"""
        try:
            self.ser = serial.Serial(
                port=self.port,
                baudrate=self.baudrate,
                bytesize=serial.EIGHTBITS,
                parity=serial.PARITY_NONE,
                stopbits=serial.STOPBITS_ONE,
                timeout=2.0
            )
            print(f"✅ Connected to {self.port} at {self.baudrate} baud")
            
            # Clear any existing data
            self.ser.flushInput()
            self.ser.flushOutput()
            time.sleep(0.1)
            
            return True
        except Exception as e:
            print(f"❌ Failed to connect to {self.port}: {e}")
            return False

    def disconnect(self):
        """Disconnect from UART port"""
        if self.ser and self.ser.is_open:
            self.ser.close()
            print("🔌 Disconnected from UART")

    def crc8_calculate(self, data: bytes) -> int:
        """Calculate CRC8 using the polynomial x^8 + x^5 + x^4 + 1 (0x31)"""
        crc = 0
        for byte in data:
            crc ^= byte
            for _ in range(8):
                if crc & 0x80:
                    crc = (crc << 1) ^ 0x31
                else:
                    crc <<= 1
                crc &= 0xFF
        return crc

    def build_frame(self, cmd: int, addr: int, data: bytes = b'') -> bytes:
        """Build UART frame according to protocol v0.1.1"""
        frame = bytearray()
        frame.append(SOF_BYTE)
        frame.append(cmd)
        
        # Address (little-endian)
        frame.extend(struct.pack('<I', addr))
        
        # Data payload
        frame.extend(data)
        
        # Calculate CRC over CMD + ADDR + DATA
        crc_data = frame[1:]  # Exclude SOF
        crc = self.crc8_calculate(crc_data)
        frame.append(crc)
        
        return bytes(frame)

    def send_frame_and_wait_response(self, frame: bytes, timeout: float = 2.0) -> Tuple[bool, bytes]:
        """Send frame and wait for response"""
        if not self.ser:
            return False, b''
        
        try:
            # Send frame
            self.ser.write(frame)
            self.ser.flush()
            
            # Wait for response
            start_time = time.time()
            response = bytearray()
            
            while time.time() - start_time < timeout:
                if self.ser.in_waiting > 0:
                    byte = self.ser.read(1)
                    if byte:
                        response.extend(byte)
                        
                        # Check if we have a complete response
                        if len(response) >= 4:  # Minimum response size
                            if response[0] == RESP_SOF_BYTE:
                                # Basic response format check
                                if len(response) >= 4:
                                    return True, bytes(response)
                time.sleep(0.001)
            
            return False, bytes(response)
            
        except Exception as e:
            print(f"❌ Communication error: {e}")
            return False, b''

    def read_register_32bit(self, addr: int) -> Tuple[bool, int, bytes]:
        """Read 32-bit register and return success, value, and raw response"""
        frame = self.build_frame(CMD_READ_32BIT, addr)
        
        print(f"📤 READ 32-bit from 0x{addr:08X}")
        print(f"   Frame: {' '.join(f'0x{b:02X}' for b in frame)}")
        
        success, response = self.send_frame_and_wait_response(frame)
        
        if success and len(response) >= 8:
            # Parse response: SOF + STATUS + CMD_ECHO + DATA + CRC
            sof = response[0]
            status = response[1]
            cmd_echo = response[2]
            data_bytes = response[3:7]
            crc = response[7] if len(response) > 7 else 0
            
            value = struct.unpack('<I', data_bytes)[0]
            
            print(f"📥 Response: SOF=0x{sof:02X}, STATUS=0x{status:02X}, CMD=0x{cmd_echo:02X}")
            print(f"   Data: {' '.join(f'0x{b:02X}' for b in data_bytes)} -> 0x{value:08X}")
            print(f"   CRC: 0x{crc:02X}")
            
            return True, value, response
        else:
            print(f"❌ Read failed or incomplete response: {len(response)} bytes")
            if response:
                print(f"   Raw: {' '.join(f'0x{b:02X}' for b in response)}")
            return False, 0, response

    def write_register_32bit(self, addr: int, value: int) -> Tuple[bool, bytes]:
        """Write 32-bit register and return success and raw response"""
        data = struct.pack('<I', value)
        frame = self.build_frame(CMD_WRITE_32BIT, addr, data)
        
        print(f"📤 WRITE 32-bit to 0x{addr:08X} = 0x{value:08X}")
        print(f"   Frame: {' '.join(f'0x{b:02X}' for b in frame)}")
        
        success, response = self.send_frame_and_wait_response(frame)
        
        if success and len(response) >= 4:
            sof = response[0]
            status = response[1]
            cmd_echo = response[2] if len(response) > 2 else 0
            crc = response[3] if len(response) > 3 else 0
            
            print(f"📥 Response: SOF=0x{sof:02X}, STATUS=0x{status:02X}, CMD=0x{cmd_echo:02X}, CRC=0x{crc:02X}")
            
            return status == 0x00, response
        else:
            print(f"❌ Write failed or incomplete response: {len(response)} bytes")
            if response:
                print(f"   Raw: {' '.join(f'0x{b:02X}' for b in response)}")
            return False, response

    def test_register_initial_values(self) -> bool:
        """Test initial values of all test registers"""
        print("\n🔍 === Testing Register Initial Values ===")
        
        test_cases = [
            ("REG_TEST_0", REG_TEST_0, EXPECTED_REG_TEST_0),
            ("REG_TEST_1", REG_TEST_1, EXPECTED_REG_TEST_1),
            ("REG_TEST_2", REG_TEST_2, EXPECTED_REG_TEST_2),
            ("REG_TEST_3", REG_TEST_3, EXPECTED_REG_TEST_3),
        ]
        
        all_passed = True
        
        for name, addr, expected in test_cases:
            print(f"\n📋 Testing {name} (0x{addr:08X})")
            success, actual, raw_response = self.read_register_32bit(addr)
            
            if success:
                test_passed = (actual == expected)
                result = TestResult(
                    test_name=f"{name}_initial_value",
                    expected=expected,
                    actual=actual,
                    success=test_passed
                )
                
                if test_passed:
                    print(f"✅ {name}: Expected 0x{expected:08X}, Got 0x{actual:08X}")
                else:
                    print(f"❌ {name}: Expected 0x{expected:08X}, Got 0x{actual:08X}")
                    print(f"   Difference: 0x{actual ^ expected:08X}")
                    all_passed = False
                    
                    # Analyze the problematic pattern
                    if (actual & 0xFFFF0000) == 0x70200000:
                        print(f"   🚨 PATTERN DETECTED: 0x702022XX (actual: 0x{actual:08X})")
                        print(f"   🔍 This suggests a hardware-specific issue")
                
            else:
                result = TestResult(
                    test_name=f"{name}_initial_value",
                    expected=expected,
                    actual=0,
                    success=False,
                    error_msg="Communication failed"
                )
                print(f"❌ {name}: Communication failed")
                all_passed = False
            
            self.test_results.append(result)
            time.sleep(0.1)
        
        return all_passed

    def test_write_read_cycle(self) -> bool:
        """Test write-then-read cycles to verify register functionality"""
        print("\n🔄 === Testing Write-Read Cycles ===")
        
        test_values = [0x12345678, 0xABCDEF00, 0xDEADBEEF, 0x00000000]
        
        all_passed = True
        
        for i, test_value in enumerate(test_values):
            addr = REG_TEST_0  # Use REG_TEST_0 for write-read testing
            
            print(f"\n📝 Write-Read Test {i+1}: 0x{test_value:08X}")
            
            # Write test value
            write_success, write_response = self.write_register_32bit(addr, test_value)
            
            if not write_success:
                print(f"❌ Write failed for value 0x{test_value:08X}")
                all_passed = False
                continue
            
            time.sleep(0.05)  # Small delay between write and read
            
            # Read back the value
            read_success, read_value, read_response = self.read_register_32bit(addr)
            
            if read_success:
                test_passed = (read_value == test_value)
                result = TestResult(
                    test_name=f"write_read_cycle_{i+1}",
                    expected=test_value,
                    actual=read_value,
                    success=test_passed
                )
                
                if test_passed:
                    print(f"✅ Write-Read OK: 0x{test_value:08X}")
                else:
                    print(f"❌ Write-Read FAIL: Wrote 0x{test_value:08X}, Read 0x{read_value:08X}")
                    all_passed = False
                    
            else:
                result = TestResult(
                    test_name=f"write_read_cycle_{i+1}",
                    expected=test_value,
                    actual=0,
                    success=False,
                    error_msg="Read failed after write"
                )
                print(f"❌ Read failed after writing 0x{test_value:08X}")
                all_passed = False
            
            self.test_results.append(result)
            time.sleep(0.1)
        
        return all_passed

    def analyze_0x702022xx_pattern(self):
        """Analyze the specific 0x702022XX pattern"""
        print("\n🔬 === Analyzing 0x702022XX Pattern ===")
        
        # Read multiple registers to see if pattern is consistent
        addresses = [REG_TEST_0, REG_TEST_1, REG_TEST_2, REG_TEST_3]
        values = []
        
        for addr in addresses:
            success, value, _ = self.read_register_32bit(addr)
            if success:
                values.append(value)
                print(f"   0x{addr:08X} -> 0x{value:08X}")
        
        if values:
            # Check if all values follow the pattern
            pattern_count = sum(1 for v in values if (v & 0xFFFF0000) == 0x70200000)
            
            print(f"\n📊 Pattern Analysis:")
            print(f"   Total reads: {len(values)}")
            print(f"   0x702022XX pattern: {pattern_count}")
            print(f"   Pattern consistency: {(pattern_count/len(values)*100):.1f}%")
            
            if pattern_count == len(values):
                print("🚨 ALL reads return 0x702022XX pattern!")
                print("   This suggests:")
                print("   - Hardware may not be properly programmed")
                print("   - FPGA configuration issue")
                print("   - Clock/reset issues")
                print("   - Memory/register access problem")

    def run_comprehensive_test(self) -> bool:
        """Run comprehensive hardware diagnostic"""
        print("🚀 === UART-AXI4 Hardware Diagnostic Test ===")
        print(f"🎯 Target: Identify cause of 0x702022XX pattern")
        print(f"📊 Expected behavior: Actual register values as in UVM simulation")
        
        if not self.connect():
            return False
        
        try:
            # Test 1: Initial values
            print(f"\n⏰ Waiting for hardware to stabilize...")
            time.sleep(1.0)
            
            initial_test_passed = self.test_register_initial_values()
            
            # Test 2: Write-read cycles
            write_read_test_passed = self.test_write_read_cycle()
            
            # Test 3: Pattern analysis
            self.analyze_0x702022xx_pattern()
            
            # Summary
            print(f"\n📋 === Test Summary ===")
            total_tests = len(self.test_results)
            passed_tests = sum(1 for r in self.test_results if r.success)
            
            print(f"Total tests: {total_tests}")
            print(f"Passed: {passed_tests}")
            print(f"Failed: {total_tests - passed_tests}")
            print(f"Success rate: {(passed_tests/total_tests*100):.1f}%")
            
            # Detailed results
            print(f"\n📝 === Detailed Results ===")
            for result in self.test_results:
                status = "✅" if result.success else "❌"
                print(f"{status} {result.test_name}: Expected 0x{result.expected:08X}, Got 0x{result.actual:08X}")
                if result.error_msg:
                    print(f"    Error: {result.error_msg}")
            
            return passed_tests == total_tests
            
        finally:
            self.disconnect()

def main():
    """Main function"""
    if len(sys.argv) > 1:
        port = sys.argv[1]
    else:
        port = 'COM3'
    
    diagnostic = UARTAxi4Diagnostic(port)
    success = diagnostic.run_comprehensive_test()
    
    if success:
        print(f"\n🎉 All tests passed! Hardware working correctly.")
        sys.exit(0)
    else:
        print(f"\n⚠️  Some tests failed. Hardware diagnostic needed.")
        sys.exit(1)

if __name__ == "__main__":
    main()