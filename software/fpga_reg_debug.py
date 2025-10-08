#!/usr/bin/env python3
"""
FPGA Register Debug Tool
既知のレジスタの値を確認してFPGAの実装状態を調査
"""

import serial
import time

class FPGARegDebug:
    def __init__(self, port: str = "COM3", baudrate: int = 115200):
        self.port = port
        self.baudrate = baudrate
        self.serial = None
        
    def connect(self) -> bool:
        """Connect to UART"""
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
    
    def read_register(self, address: int) -> bytes:
        """Read a register and return raw response"""
        # test_registers_updated.pyと完全に同じパケット形式
        frame = bytearray()
        frame.append(0xA5)  # SOF
        frame.append(0xA0)  # Read command
        
        # Address (little-endian, 4 bytes)
        frame.extend(address.to_bytes(4, 'little'))
        
        # Calculate and append CRC (exclude SOF)
        crc = self.crc8_calculate(frame[1:])
        frame.append(crc)
        
        print(f"📤 TX: {frame.hex(' ').upper()}")
        
        self.serial.write(frame)
        time.sleep(0.1)
        
        response = self.serial.read(20)  # Read up to 20 bytes
        print(f"📥 RX: {response.hex(' ').upper()}")
        
        return response
    
    def run_debug(self):
        """Run comprehensive register debug"""
        if not self.connect():
            return
        
        print("\n🔍 FPGA Register Debug")
        print("=" * 50)
        
        # 成功実績のあるアドレス形式を使用 (test_registers_updated.pyから)
        registers = {
            "CONTROL":   0x00001000,
            "STATUS":    0x00001004, 
            "CONFIG":    0x00001008,
            "DEBUG":     0x0000100C,
            "TX_COUNT":  0x00001010,
            "RX_COUNT":  0x00001014,
            "FIFO_STAT": 0x00001018,
            "VERSION":   0x0000101C,
            "REG_TEST_0": 0x00001020,
            "REG_TEST_1": 0x00001024,
            "REG_TEST_2": 0x00001028,
            "REG_TEST_3": 0x0000102C,
        }
        
        for name, addr in registers.items():
            print(f"\n📍 {name} (0x{addr:08X})")
            print("-" * 30)
            response = self.read_register(addr)
            
            if len(response) >= 8:
                sof = response[0]
                status = response[1]
                cmd = response[2]
                data_bytes = response[3:7]
                crc = response[7]
                data_value = int.from_bytes(data_bytes, 'little')
                
                print(f"   SOF: 0x{sof:02X}")
                print(f"   STATUS: 0x{status:02X}")
                print(f"   CMD: 0x{cmd:02X}")
                print(f"   DATA: 0x{data_value:08X}")
                print(f"   CRC: 0x{crc:02X}")
            else:
                print(f"   ⚠️  Short response: {len(response)} bytes")
            
            time.sleep(0.1)
        
        self.disconnect()

if __name__ == "__main__":
    debug = FPGARegDebug()
    debug.run_debug()