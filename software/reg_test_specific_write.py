#!/usr/bin/env python3
"""
REG_TEST Register Specific Write Test
Direct access to REG_TEST_0 through REG_TEST_3 registers
Based on Register_Block.sv lines 41-45
"""

import serial
import time
import struct

class REGTestSpecificWriter:
    def __init__(self, port='COM3', baudrate=115200):
        self.port = port
        self.baudrate = baudrate
        self.serial = None
        
        # REG_TEST register addresses from Register_Block.sv
        self.REG_TEST_ADDRESSES = {
            'REG_TEST_0': 0x00001020,  # 12'h020
            'REG_TEST_1': 0x00001024,  # 12'h024  
            'REG_TEST_2': 0x00001028,  # 12'h028
            'REG_TEST_3': 0x0000102C   # 12'h02C
        }
        
        # Expected initial values from Register_Block.sv
        self.EXPECTED_INITIAL_VALUES = {
            'REG_TEST_0': 0xDEADBEEF,  # test_reg_0 <= 32'hDEADBEEF
            'REG_TEST_1': 0x12345678,  # test_reg_1 <= 32'h12345678
            'REG_TEST_2': 0xABCDEF00,  # test_reg_2 <= 32'hABCDEF00
            'REG_TEST_3': 0x00000000   # test_reg_3 <= 32'h00000000
        }
        
        # Test patterns to write
        self.TEST_PATTERNS = {
            'REG_TEST_0': 0x55AA55AA,  # Alternating pattern
            'REG_TEST_1': 0xFFFFFFFF,  # All ones
            'REG_TEST_2': 0x00000000,  # All zeros  
            'REG_TEST_3': 0xCAFEBABE   # Recognizable pattern
        }

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

    def write_register(self, address, value):
        """Write 32-bit value to register using correct UART bridge protocol"""
        try:
            # Correct UART bridge protocol format:
            # SOF (0xA5) | CMD | ADDR[3:0] | DATA[3:0] | CRC8
            # CMD format: RW=0, INC=0, SIZE=10 (32-bit), LEN=0000 (1 beat)
            cmd_byte = 0x20  # 0b00100000: RW=0(write), INC=0, SIZE=10(32-bit), LEN=0000(1 beat)
            
            # Build frame without SOF and CRC first
            frame_data = bytearray()
            frame_data.append(cmd_byte)
            frame_data.extend(struct.pack('<I', address))  # Little-endian address
            frame_data.extend(struct.pack('<I', value))    # Little-endian data
            
            # Calculate CRC over CMD+ADDR+DATA
            crc = self.calculate_crc8(frame_data)
            
            # Complete frame: SOF + CMD + ADDR + DATA + CRC
            complete_frame = bytearray([0xA5])  # SOF
            complete_frame.extend(frame_data)
            complete_frame.append(crc)
            
            self.serial.write(complete_frame)
            
            # Read response: SOF (0x5A) + STATUS + CMD + CRC
            response = self.serial.read(4)
            if len(response) == 4:
                sof, status, cmd_echo, crc_resp = response
                if sof == 0x5A and status == 0x00:  # Success response
                    return True, f"OK_STATUS_{status:02X}"
                else:
                    return False, f"ERROR_STATUS_{status:02X}"
            else:
                return False, f"TIMEOUT_LEN_{len(response)}"
                
        except Exception as e:
            print(f"❌ Write error: {e}")
            return False, str(e)

    def read_register(self, address):
        """Read 32-bit value from register using correct UART bridge protocol"""
        try:
            # Correct UART bridge read protocol format:
            # Request: SOF (0xA5) | CMD | ADDR[3:0] | CRC8
            # CMD format: RW=1, INC=0, SIZE=10 (32-bit), LEN=0000 (1 beat)
            cmd_byte = 0xA0  # 0b10100000: RW=1(read), INC=0, SIZE=10(32-bit), LEN=0000(1 beat)
            
            # Build frame without SOF and CRC first
            frame_data = bytearray()
            frame_data.append(cmd_byte)
            frame_data.extend(struct.pack('<I', address))  # Little-endian address
            
            # Calculate CRC over CMD+ADDR
            crc = self.calculate_crc8(frame_data)
            
            # Complete frame: SOF + CMD + ADDR + CRC
            complete_frame = bytearray([0xA5])  # SOF
            complete_frame.extend(frame_data)
            complete_frame.append(crc)
            
            self.serial.write(complete_frame)
            
            # Read response: SOF (0x5A) + STATUS + CMD + ADDR + DATA + CRC
            # Success response is 11 bytes: SOF(1) + STATUS(1) + CMD(1) + ADDR(4) + DATA(4) + CRC(1)
            response = self.serial.read(11)
            if len(response) == 11:
                sof = response[0]
                status = response[1]
                if sof == 0x5A and status == 0x00:  # Success response
                    # Extract 32-bit data from bytes 7-10 (little-endian)
                    value = struct.unpack('<I', response[7:11])[0]
                    return True, value, 'DATA'
                else:
                    return False, None, f'ERROR_STATUS_{status:02X}'
            else:
                return False, None, f'TIMEOUT_LEN_{len(response)}'
        except Exception as e:
            print(f"❌ Read error: {e}")
            return False, None, str(e)

    def test_single_register(self, reg_name):
        """Test a single REG_TEST register"""
        address = self.REG_TEST_ADDRESSES[reg_name]
        expected_initial = self.EXPECTED_INITIAL_VALUES[reg_name]
        test_pattern = self.TEST_PATTERNS[reg_name]
        
        print(f"\n📍 Testing {reg_name} (Address: 0x{address:08X})")
        print("-" * 60)
        
        # Step 1: Read initial value
        print("1️⃣ Reading initial value...")
        success, initial_value, status = self.read_register(address)
        if success:
            print(f"   Initial value: 0x{initial_value:08X}")
            if initial_value == expected_initial:
                print(f"   ✅ Matches expected initial value (0x{expected_initial:08X})")
            else:
                print(f"   ⚠️  Expected 0x{expected_initial:08X}, got 0x{initial_value:08X}")
        else:
            print(f"   ❌ Read failed: {status}")
            return False
        
        # Step 2: Write test pattern
        print(f"2️⃣ Writing test pattern 0x{test_pattern:08X}...")
        success, response = self.write_register(address, test_pattern)
        if success:
            print(f"   ✅ Write successful")
        else:
            print(f"   ❌ Write failed: {response}")
            return False
        
        # Step 3: Read back written value
        print("3️⃣ Reading back written value...")
        success, readback_value, status = self.read_register(address)
        if success:
            print(f"   Read back: 0x{readback_value:08X}")
            if readback_value == test_pattern:
                print(f"   ✅ PERFECT MATCH! Register is working correctly")
                return True
            else:
                print(f"   ❌ MISMATCH! Expected 0x{test_pattern:08X}, got 0x{readback_value:08X}")
                # Check if it's still the test pattern generator
                if (readback_value & 0xFFFFFF00) == 0xF0202200:
                    print(f"   🚨 Still showing test pattern generator (0xF02022XX)")
                return False
        else:
            print(f"   ❌ Read failed: {status}")
            return False

    def run_comprehensive_test(self):
        """Run comprehensive test on all REG_TEST registers"""
        print("🎯 REG_TEST Register Specific Write Test")
        print("=" * 80)
        print("Target: Direct access to REG_TEST_0 through REG_TEST_3")
        print("Objective: Verify register write/read functionality after FPGA update")
        print("=" * 80)
        
        results = {}
        
        for reg_name in ['REG_TEST_0', 'REG_TEST_1', 'REG_TEST_2', 'REG_TEST_3']:
            results[reg_name] = self.test_single_register(reg_name)
        
        # Summary
        print("\n" + "=" * 80)
        print("📊 TEST SUMMARY")
        print("=" * 80)
        
        successful_registers = sum(1 for success in results.values() if success)
        total_registers = len(results)
        
        for reg_name, success in results.items():
            status = "✅ WORKING" if success else "❌ FAILED"
            address = self.REG_TEST_ADDRESSES[reg_name]
            print(f"   {reg_name} (0x{address:08X}): {status}")
        
        print(f"\nOverall Results:")
        print(f"   Successful registers: {successful_registers}/{total_registers}")
        print(f"   Success rate: {(successful_registers/total_registers)*100:.1f}%")
        
        if successful_registers == total_registers:
            print("\n🎉 ALL REGISTERS WORKING! FPGA update was successful!")
        elif successful_registers > 0:
            print(f"\n⚠️  PARTIAL SUCCESS: {successful_registers} registers working")
        else:
            print("\n🚨 ALL REGISTERS FAILED: Test pattern generator still active")
        
        return results

def main():
    """Main execution function"""
    print("Starting REG_TEST Register Specific Write Test...")
    print("Based on Register_Block.sv lines 41-45")
    print()
    
    tester = REGTestSpecificWriter()
    
    if not tester.connect():
        return
    
    try:
        results = tester.run_comprehensive_test()
        
        # Save results to file
        timestamp = time.strftime("%Y%m%d_%H%M%S")
        results_file = f"reg_test_specific_results_{timestamp}.txt"
        
        with open(results_file, 'w') as f:
            f.write("REG_TEST Register Specific Write Test Results\n")
            f.write(f"Timestamp: {timestamp}\n")
            f.write("=" * 50 + "\n")
            for reg_name, success in results.items():
                address = tester.REG_TEST_ADDRESSES[reg_name]
                status = "SUCCESS" if success else "FAILED"
                f.write(f"{reg_name} (0x{address:08X}): {status}\n")
        
        print(f"\n💾 Results saved to: {results_file}")
        
    finally:
        tester.disconnect()

if __name__ == "__main__":
    main()