#!/usr/bin/env python3
"""
REG_TEST Register Working Protocol Test
Uses the verified working protocol from test_registers_updated.py
Based on actual FPGA implementation
"""

import serial
import time
import struct

class REGTestWorkingProtocol:
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

        # Protocol constants from working implementation
        self.PROTOCOL_SOF_RESPONSE = 0xAD      # Device→Host SOF
        self.PROTOCOL_STATUS_OK = 0x80         # Success status

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

    def send_command(self, cmd, addr, data=b""):
        """Send UART command and receive response - working protocol"""
        if not self.serial or not self.serial.is_open:
            return None

        # Build command frame according to working format
        frame = bytearray()
        frame.append(0xA5)  # SOF (host to device)
        frame.append(cmd)   # Command
        
        # Address (little-endian, 4 bytes)
        frame.extend(struct.pack('<I', addr))
        
        # For read commands, no additional fields needed
        if cmd == 0xA0:  # Read command
            pass
        elif cmd == 0x20:  # Write command  
            frame.extend(data)       # Data
        
        # Calculate and append CRC (exclude SOF)
        crc = self.crc8_calculate(frame[1:])
        frame.append(crc)
        
        print(f"📤 Sending: {' '.join(f'{b:02X}' for b in frame)}")
        
        # Clear input buffer and send
        self.serial.reset_input_buffer()
        self.serial.write(frame)
        self.serial.flush()
        
        # Wait for response
        time.sleep(0.1)
        
        # Read response
        response = self.serial.read(100)  # Read up to 100 bytes
        if response:
            print(f"📥 Received: {' '.join(f'{b:02X}' for b in response)}")
            return response
        else:
            print("❌ No response received")
            return None

    def read_register(self, addr):
        """Read 32-bit register using working protocol"""
        response = self.send_command(0xA0, addr)  # Read command
        
        if not response or len(response) < 8:
            print(f"❌ Invalid response length: {len(response) if response else 0}")
            return None, f"TIMEOUT_LEN_{len(response) if response else 0}"

        # Parse response (expecting 8 bytes total)
        # SOF[1] + STATUS[1] + CMD[1] + DATA[4] + CRC[1] = 8 bytes for read
        
        if len(response) == 8:
            sof, status, cmd = response[0], response[1], response[2]
            data_bytes = response[3:7]
            crc = response[7]
            
            print(f"📋 SOF: 0x{sof:02X}, STATUS: 0x{status:02X}, CMD: 0x{cmd:02X}")
            print(f"📋 Data bytes: {' '.join(f'{b:02X}' for b in data_bytes)}")
            print(f"📋 CRC: 0x{crc:02X}")
            
            # Extract 32-bit data (little-endian)
            data_value = struct.unpack('<I', data_bytes)[0]
            print(f"📋 Data value: 0x{data_value:08X}")
            
            # Check status
            if status == self.PROTOCOL_STATUS_OK:  # 0x80
                print("✅ Status OK")
                return data_value, 'DATA'
            elif status == 0x00:
                print("✅ Status OK (spec value)")
                return data_value, 'DATA'
            else:
                print(f"❌ Error status: 0x{status:02X}")
                return None, f'ERROR_STATUS_{status:02X}'
        
        print(f"❌ Unexpected response format (length: {len(response)})")
        return None, f'FORMAT_ERROR_{len(response)}'

    def write_register(self, addr, value):
        """Write 32-bit register using working protocol"""
        data = struct.pack('<I', value)  # 32-bit little-endian
        response = self.send_command(0x20, addr, data)  # Write command
        
        if not response:
            return False, "NO_RESPONSE"
        
        if len(response) >= 2:
            sof, status = response[0], response[1]
            print(f"📋 Write response - SOF: 0x{sof:02X}, STATUS: 0x{status:02X}")
            
            # Full response debugging
            print(f"📋 Full write response: {' '.join(f'{b:02X}' for b in response)}")
            if len(response) >= 4:
                cmd_echo = response[2]
                crc = response[3]
                print(f"📋 CMD_ECHO: 0x{cmd_echo:02X}, CRC: 0x{crc:02X}")
            
            # Check status (use working implementation values)
            if status == self.PROTOCOL_STATUS_OK:  # 0x80
                print("✅ Write Status OK")
                return True, f"OK_STATUS_{status:02X}"
            elif status == 0x00:
                print("✅ Write Status OK (spec value)")
                return True, f"OK_STATUS_{status:02X}"
            else:
                print(f"❌ Write error status: 0x{status:02X}")
                return False, f"ERROR_STATUS_{status:02X}"
        
        return False, "INVALID_RESPONSE"

    def test_single_register(self, reg_name):
        """Test a single REG_TEST register"""
        address = self.REG_TEST_ADDRESSES[reg_name]
        expected_initial = self.EXPECTED_INITIAL_VALUES[reg_name]
        test_pattern = self.TEST_PATTERNS[reg_name]
        
        print(f"\n📍 Testing {reg_name} (Address: 0x{address:08X})")
        print("-" * 60)
        
        # Step 1: Read initial value
        print("1️⃣ Reading initial value...")
        initial_value, status = self.read_register(address)
        if initial_value is not None:
            print(f"   Initial value: 0x{initial_value:08X}")
            if initial_value == expected_initial:
                print(f"   ✅ Matches expected initial value (0x{expected_initial:08X})")
            else:
                print(f"   ⚠️  Expected 0x{expected_initial:08X}, got 0x{initial_value:08X}")
                # Check if it's test pattern generator
                if (initial_value & 0xFFFFFF00) == 0xF0202200:
                    print(f"   🚨 Test pattern generator detected (0xF02022XX)")
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
        readback_value, status = self.read_register(address)
        if readback_value is not None:
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
        print("🎯 REG_TEST Register Working Protocol Test")
        print("=" * 80)
        print("Using: Verified working protocol from test_registers_updated.py")
        print("Protocol: SOF(0xA5) + CMD + ADDR + [DATA] + CRC")
        print("Read Response: 8 bytes (SOF + STATUS + CMD + DATA[4] + CRC)")
        print("Write Response: 4 bytes (SOF + STATUS + CMD + CRC)")
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
            print("\n🎉 ALL REGISTERS WORKING! FPGA implementation is correct!")
        elif successful_registers > 0:
            print(f"\n⚠️  PARTIAL SUCCESS: {successful_registers} registers working")
        else:
            print("\n🚨 ALL REGISTERS FAILED: Check FPGA implementation")
        
        return results

def main():
    """Main execution function"""
    print("Starting REG_TEST Register Working Protocol Test...")
    print("Using verified working protocol implementation")
    print()
    
    tester = REGTestWorkingProtocol()
    
    if not tester.connect():
        return
    
    try:
        results = tester.run_comprehensive_test()
        
        # Save results to file
        timestamp = time.strftime("%Y%m%d_%H%M%S")
        results_file = f"reg_test_working_protocol_results_{timestamp}.txt"
        
        with open(results_file, 'w') as f:
            f.write("REG_TEST Register Working Protocol Test Results\n")
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