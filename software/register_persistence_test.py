#!/usr/bin/env python3
"""
レジスタ持続性テスト - FPGAでレジスタ値が実際に保存されるかを確認
"""

import serial
import time
import struct
from typing import Optional, List

# Protocol constants (updated for current FPGA behavior)
SOF_HOST_TO_DEVICE = 0xA5
SOF_DEVICE_TO_HOST_SPEC = 0x5A
SOF_DEVICE_TO_HOST_ACTUAL = 0xAD  # Current FPGA implementation
CMD_READ = 0xA0
CMD_WRITE = 0x20
STATUS_OK_SPEC = 0x00
STATUS_OK_ACTUAL = 0x80  # Current FPGA implementation

def calculate_crc8(data: bytes) -> int:
    """Calculate CRC8 with polynomial 0x07"""
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

class UARTTester:
    def __init__(self, port: str = "COM3", baudrate: int = 115200):
        self.serial = None
        self.port = port
        self.baudrate = baudrate
    
    def connect(self) -> bool:
        """Connect to UART"""
        try:
            self.serial = serial.Serial(self.port, self.baudrate, timeout=1)
            time.sleep(0.1)
            return True
        except Exception as e:
            print(f"❌ Connection failed: {e}")
            return False
    
    def disconnect(self):
        """Disconnect from UART"""
        if self.serial and self.serial.is_open:
            self.serial.close()
    
    def send_command(self, cmd: int, addr: int, data: Optional[int] = None) -> Optional[bytes]:
        """Send UART command and receive response"""
        if not self.serial or not self.serial.is_open:
            return None
        
        # Build command frame
        frame = bytearray()
        frame.append(SOF_HOST_TO_DEVICE)
        frame.append(cmd)
        frame.extend(struct.pack('<I', addr))  # Address (little-endian)
        
        if data is not None:  # Write command
            frame.extend(struct.pack('<I', data))  # Data (little-endian)
        
        # Calculate and append CRC
        crc = calculate_crc8(frame[1:])  # Exclude SOF
        frame.append(crc)
        
        # Send frame
        print(f"📤 送信: {' '.join([f'{b:02X}' for b in frame])}")
        self.serial.write(frame)
        time.sleep(0.1)
        
        # Receive response
        response = bytearray()
        for _ in range(20):  # Wait up to 2 seconds
            if self.serial.in_waiting > 0:
                response.extend(self.serial.read(self.serial.in_waiting))
                if cmd == CMD_READ and len(response) >= 8:
                    break
                elif cmd == CMD_WRITE and len(response) >= 4:
                    break
            time.sleep(0.1)
        
        if response:
            print(f"📥 受信: {' '.join([f'{b:02X}' for b in response])}")
            return bytes(response)
        else:
            print("   ❌ 応答なし")
            return None
    
    def write_register(self, addr: int, value: int) -> bool:
        """Write to register"""
        response = self.send_command(CMD_WRITE, addr, value)
        if response and len(response) >= 4:
            if response[0] == SOF_DEVICE_TO_HOST_ACTUAL and response[1] == STATUS_OK_ACTUAL:
                print(f"✅ 書き込み成功: 0x{addr:08X} = 0x{value:08X}")
                return True
        print(f"❌ 書き込み失敗: 0x{addr:08X} = 0x{value:08X}")
        return False
    
    def read_register(self, addr: int) -> Optional[int]:
        """Read from register"""
        response = self.send_command(CMD_READ, addr)
        if response and len(response) >= 8:
            if response[0] == SOF_DEVICE_TO_HOST_ACTUAL and response[1] == STATUS_OK_ACTUAL:
                # Extract data from response (bytes 3-6 in little-endian)
                data_bytes = response[3:7]
                value = struct.unpack('<I', data_bytes)[0]
                print(f"✅ 読み出し成功: 0x{addr:08X} = 0x{value:08X}")
                return value
        print(f"❌ 読み出し失敗: 0x{addr:08X}")
        return None

def main():
    """レジスタ持続性テストのメイン関数"""
    print("🧪 レジスタ持続性テスト")
    print("=" * 60)
    
    tester = UARTTester()
    if not tester.connect():
        return
    
    print("✅ COM3に接続しました\n")
    
    # Test addresses and unique values
    test_cases = [
        (0x00001020, 0xDEADBEEF),
        (0x00001024, 0xCAFEBABE),
        (0x00001028, 0x12345678),
        (0x0000102C, 0x87654321),
    ]
    
    print("📋 Phase 1: 異なる値を各レジスタに書き込み")
    print("-" * 50)
    write_success = 0
    for addr, value in test_cases:
        if tester.write_register(addr, value):
            write_success += 1
        time.sleep(0.2)
    
    print(f"\n📊 書き込み結果: {write_success}/{len(test_cases)} 成功\n")
    
    print("📋 Phase 2: 各レジスタから読み出して持続性確認")
    print("-" * 50)
    read_success = 0
    persistence_success = 0
    
    for addr, expected in test_cases:
        actual = tester.read_register(addr)
        if actual is not None:
            read_success += 1
            if actual == expected:
                print(f"🎯 持続性OK: 0x{addr:08X} 期待=0x{expected:08X} 実際=0x{actual:08X}")
                persistence_success += 1
            else:
                print(f"💥 持続性NG: 0x{addr:08X} 期待=0x{expected:08X} 実際=0x{actual:08X}")
        time.sleep(0.2)
    
    print(f"\n📊 読み出し結果: {read_success}/{len(test_cases)} 成功")
    print(f"📊 持続性結果: {persistence_success}/{len(test_cases)} 成功")
    
    if persistence_success == len(test_cases):
        print("\n🎉 全レジスタの持続性テスト成功！")
    elif persistence_success > 0:
        print(f"\n⚠️  部分的な持続性問題 ({persistence_success}/{len(test_cases)})")
    else:
        print("\n❌ レジスタ持続性の重大な問題を検出")
    
    print("\n📋 Phase 3: 読み出しパターン分析")
    print("-" * 50)
    values = []
    for addr, _ in test_cases:
        actual = tester.read_register(addr)
        if actual is not None:
            values.append(actual)
    
    if len(values) > 1:
        if all(v == values[0] for v in values):
            print(f"🔍 全レジスタが同じ値を返しています: 0x{values[0]:08X}")
        elif all(abs(values[i+1] - values[i]) == 1 for i in range(len(values)-1)):
            print("🔍 連続カウンタパターンを検出しました")
        else:
            print("🔍 不規則なパターンです")
    
    tester.disconnect()
    print("\n🔌 UART接続を終了しました")

if __name__ == "__main__":
    main()