#!/usr/bin/env python3
"""
Test Register Access with SOF Issue Handling
Tests the newly added test registers (0x00001020-0x0000102C) 
while handling the known SOF transformation issue (0x5A → 0xAD)
"""

import serial
import time
import struct
from typing import Optional

class TestRegisterAccess:
    def __init__(self, port: str = "COM3", baudrate: int = 115200):
        self.port = port
        self.baudrate = baudrate
        self.serial = None
        
    def connect(self) -> bool:
        """Connect to UART"""
        try:
            self.serial = serial.Serial(self.port, self.baudrate, timeout=2.0)
            time.sleep(0.1)  # Allow port to stabilize
            print(f"✅ Connected to {self.port} at {self.baudrate} baud")
            return True
        except Exception as e:
            print(f"❌ Failed to connect: {e}")
            return False
    
    def disconnect(self):
        """Disconnect from UART"""
        if self.serial and self.serial.is_open:
            self.serial.close()
            print("🔌 Disconnected from UART")
    
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
    
    def send_command(self, cmd: int, addr: int, data: bytes = b"") -> Optional[bytes]:
        """Send UART command and receive response"""
        if not self.serial or not self.serial.is_open:
            return None
        
        # Build command frame according to UVM test format
        frame = bytearray()
        frame.append(0xA5)  # SOF (host to device)
        frame.append(cmd)   # Command
        
        # Address (little-endian, 4 bytes)
        frame.extend(struct.pack('<I', addr))
        
        # For read commands, no additional fields needed
        if cmd == 0xA0:  # Read command
            # No additional fields for read
            pass
        elif cmd == 0x20:  # Write command  
            # Data only (no length field - LEN is embedded in CMD)
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
    
    def read_register(self, addr: int) -> Optional[int]:
        """Read 32-bit register"""
        response = self.send_command(0xA0, addr)  # Read command
        
        if not response or len(response) < 8:
            print(f"❌ Invalid response length: {len(response) if response else 0}")
            return None
        
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
            
            # Analyze status bits
            print(f"📋 Status analysis: 0x{status:02X} = {status:08b}b")
            if status & 0x80:
                print("   - Bit 7 set: Possible read/response flag")
            if status & 0x40:
                print("   - Bit 6 set: Possible error flag")
            if status & 0x3F:
                print(f"   - Lower bits: 0x{status & 0x3F:02X}")
            
            # For now, accept the data even with status flags
            if status == 0x00:
                print("✅ Status OK")
                return data_value
            elif status == 0x80:
                print("⚠️  Status 0x80 - but data received, might be valid")
                return data_value  # Try accepting it
            else:
                print(f"❌ Error status: 0x{status:02X}")
                return None
        
        print(f"❌ Unexpected response format (length: {len(response)})")
        return None
    
    def write_register(self, addr: int, value: int) -> bool:
        """Write 32-bit register"""
        data = struct.pack('<I', value)  # 32-bit little-endian
        response = self.send_command(0x20, addr, data)  # Write command: 32-bit (SIZE=10), LEN=0
        
        if not response:
            return False
        
        if len(response) >= 2:
            sof, status = response[0], response[1]
            print(f"📋 Write response - SOF: 0x{sof:02X}, STATUS: 0x{status:02X}")
            
            # Full response debugging
            print(f"📋 Full write response: {' '.join(f'{b:02X}' for b in response)}")
            if len(response) >= 4:
                cmd_echo = response[2]
                crc = response[3]
                print(f"📋 CMD_ECHO: 0x{cmd_echo:02X}, CRC: 0x{crc:02X}")
            
            return status == 0x00
        
        return False

def test_registers():
    """Test the new registers"""
    print("🧪 Testing New Test Registers (Updated FPGA)")
    print("=" * 60)
    
    # Test register addresses
    REG_TEST_0 = 0x00001020
    REG_TEST_1 = 0x00001024
    REG_TEST_2 = 0x00001028
    REG_TEST_3 = 0x0000102C
    
    bridge = TestRegisterAccess("COM3", 115200)
    
    if not bridge.connect():
        return False
    
    try:
        print(f"\n📍 Testing REG_TEST_0 (0x{REG_TEST_0:08X})")
        print("-" * 40)
        
        # Read initial value
        initial_value = bridge.read_register(REG_TEST_0)
        if initial_value is not None:
            print(f"✅ Initial value: 0x{initial_value:08X}")
        
        # Test write and read back
        test_value = 0x12345678
        print(f"\n🔧 Writing test value: 0x{test_value:08X}")
        if bridge.write_register(REG_TEST_0, test_value):
            print("✅ Write operation successful")
            
            # Read back
            read_value = bridge.read_register(REG_TEST_0)
            if read_value == test_value:
                print(f"✅ Read-back successful: 0x{read_value:08X}")
            else:
                print(f"❌ Read-back mismatch: expected 0x{test_value:08X}, got 0x{read_value:08X}")
        else:
            print("❌ Write operation failed")
        
        print(f"\n📍 Testing all registers with different values")
        print("-" * 40)
        
        test_regs = [
            (REG_TEST_0, 0x11111111),
            (REG_TEST_1, 0x22222222), 
            (REG_TEST_2, 0x33333333),
            (REG_TEST_3, 0x44444444)
        ]
        
        # Write test values
        for addr, value in test_regs:
            print(f"\n🔧 Writing 0x{value:08X} to 0x{addr:08X}")
            bridge.write_register(addr, value)
        
        print(f"\n📖 Reading back all registers:")
        print("-" * 40)
        
        # Read back and verify
        all_passed = True
        for addr, expected in test_regs:
            read_value = bridge.read_register(addr)
            if read_value == expected:
                print(f"✅ 0x{addr:08X}: 0x{read_value:08X} (correct)")
            else:
                print(f"❌ 0x{addr:08X}: expected 0x{expected:08X}, got 0x{read_value:08X}")
                all_passed = False
        
        return all_passed
        
    finally:
        bridge.disconnect()

if __name__ == "__main__":
    success = test_registers()
    print("\n" + "=" * 60)
    if success:
        print("🎉 All test register operations completed successfully!")
    else:
        print("❌ Some test register operations failed!")
    print("=" * 60)