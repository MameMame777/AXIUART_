#!/usr/bin/env python3
"""
FPGA REG_TEST Write-Read Test
REG_TESTレジスタの書き込み・読み戻しテストを実行
"""

import serial
import time
import struct

class FPGARegWriteReadTest:
    def __init__(self, port: str = "COM3", baudrate: int = 115200):
        self.port = port
        self.baudrate = baudrate
        self.serial = None
        
    def connect(self) -> bool:
        try:
            self.serial = serial.Serial(self.port, self.baudrate, timeout=2.0)
            time.sleep(0.1)
            print(f"✅ Connected to {self.port}")
            return True
        except Exception as e:
            print(f"❌ Failed to connect: {e}")
            return False
    
    def disconnect(self):
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
                    crc = (crc << 1)
        return crc & 0xFF
    
    def send_command(self, cmd: int, addr: int, data: bytes = None) -> bytes:
        """Send command and return response"""
        frame = bytearray()
        frame.append(0xA5)  # SOF
        frame.append(cmd)   # Command
        frame.extend(addr.to_bytes(4, 'little'))  # Address
        
        if data:
            frame.extend(data)  # Data for write commands
        
        crc = self.crc8_calculate(frame[1:])
        frame.append(crc)
        
        print(f"📤 TX: {frame.hex(' ').upper()}")
        
        self.serial.reset_input_buffer()
        self.serial.write(frame)
        self.serial.flush()
        time.sleep(0.1)
        
        response = self.serial.read(20)
        print(f"📥 RX: {response.hex(' ').upper()}")
        
        return response
    
    def read_register(self, addr: int) -> int:
        """Read register and return 32-bit value"""
        response = self.send_command(0xA0, addr)
        if len(response) >= 8:
            data_bytes = response[3:7]
            return int.from_bytes(data_bytes, 'little')
        return 0
    
    def write_register(self, addr: int, value: int) -> bool:
        """Write register and return success status"""
        data = value.to_bytes(4, 'little')
        response = self.send_command(0x20, addr, data)
        return len(response) >= 4 and response[1] == 0x80  # Check status
    
    def run_test(self):
        """Run comprehensive write-read test"""
        if not self.connect():
            return
        
        print("\n🧪 FPGA REG_TEST Write-Read Verification")
        print("=" * 50)
        
        test_registers = [
            ("REG_TEST_0", 0x00001020),
            ("REG_TEST_1", 0x00001024),
            ("REG_TEST_2", 0x00001028),
            ("REG_TEST_3", 0x0000102C),
        ]
        
        test_values = [0x11111111, 0x22222222, 0x33333333, 0x44444444]
        
        for (name, addr), test_value in zip(test_registers, test_values):
            print(f"\n📍 Testing {name} (0x{addr:08X})")
            print("-" * 40)
            
            # 1. Read initial value
            print("1️⃣ Reading initial value...")
            initial_value = self.read_register(addr)
            print(f"   Initial: 0x{initial_value:08X}")
            
            # 2. Write test value
            print(f"2️⃣ Writing test value: 0x{test_value:08X}...")
            write_success = self.write_register(addr, test_value)
            if write_success:
                print("   ✅ Write successful")
            else:
                print("   ❌ Write failed")
                continue
            
            # 3. Read back value
            print("3️⃣ Reading back value...")
            readback_value = self.read_register(addr)
            print(f"   Readback: 0x{readback_value:08X}")
            
            # 4. Verify
            if readback_value == test_value:
                print("   ✅ PASS: Values match!")
            else:
                print(f"   ❌ FAIL: Expected 0x{test_value:08X}, got 0x{readback_value:08X}")
        
        print("\n" + "=" * 50)
        print("Test completed")
        self.disconnect()

if __name__ == "__main__":
    test = FPGARegWriteReadTest()
    test.run_test()