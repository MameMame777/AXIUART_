#!/usr/bin/env python3
"""
FPGA実機でのREG_TEST_0〜3レジスタ基本検証スクリプト（簡易版）
UVMテストで確認された基本動作をFPGA実機で検証
"""

import serial
import time
import struct
from typing import Optional

# プロトコル定数
PROTOCOL_SOF_REQUEST = 0xA5       # Host→Device SOF
PROTOCOL_SOF_RESPONSE = 0x5A      # Device→Host SOF (UVM実測値)
PROTOCOL_STATUS_OK = 0x00         # Success status
PROTOCOL_CMD_READ = 0xA0          # Read command
PROTOCOL_CMD_WRITE = 0x20         # Write command

# REG_TEST レジスタアドレス
REG_TEST_0 = 0x00001020
REG_TEST_1 = 0x00001024
REG_TEST_2 = 0x00001028
REG_TEST_3 = 0x0000102C

class SimpleFPGATester:
    def __init__(self, port: str = "COM3", baudrate: int = 115200):
        self.port = port
        self.baudrate = baudrate
        self.serial = None
        
    def connect(self) -> bool:
        """UART接続"""
        try:
            self.serial = serial.Serial(self.port, self.baudrate, timeout=2.0)
            time.sleep(0.1)
            print(f"✅ Connected to {self.port}")
            return True
        except Exception as e:
            print(f"❌ Connection failed: {e}")
            return False
    
    def disconnect(self):
        """UART切断"""
        if self.serial and self.serial.is_open:
            self.serial.close()
            print("🔌 Disconnected")
    
    def crc8_calculate(self, data: bytes) -> int:
        """CRC8計算"""
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
        """UARTコマンド送信"""
        if not self.serial:
            return None
        
        frame = bytearray()
        frame.append(PROTOCOL_SOF_REQUEST)
        frame.append(cmd)
        frame.extend(struct.pack('<I', addr))
        
        if cmd == PROTOCOL_CMD_WRITE:
            frame.extend(data)
        
        crc = self.crc8_calculate(frame[1:])
        frame.append(crc)
        
        print(f"📤 TX: {' '.join(f'{b:02X}' for b in frame)}")
        
        self.serial.reset_input_buffer()
        self.serial.write(frame)
        self.serial.flush()
        time.sleep(0.05)
        
        response = self.serial.read(100)
        if response:
            print(f"📥 RX: {' '.join(f'{b:02X}' for b in response)}")
            return response
        return None
    
    def read_register(self, addr: int) -> Optional[int]:
        """レジスタ読み出し"""
        response = self.send_command(PROTOCOL_CMD_READ, addr)
        
        if not response or len(response) < 8:
            return None
        
        if len(response) == 8:
            sof, status = response[0], response[1]
            data_bytes = response[3:7]
            
            if status == PROTOCOL_STATUS_OK:
                return struct.unpack('<I', data_bytes)[0]
        
        return None
    
    def write_register(self, addr: int, value: int) -> bool:
        """レジスタ書き込み"""
        data = struct.pack('<I', value)
        response = self.send_command(PROTOCOL_CMD_WRITE, addr, data)
        
        if not response or len(response) < 4:
            return False
        
        sof, status = response[0], response[1]
        return status == PROTOCOL_STATUS_OK
    
    def test_basic_operations(self) -> bool:
        """基本的な読み書きテスト"""
        print("🧪 REG_TEST_0〜3 基本動作テスト")
        print("=" * 50)
        
        registers = [
            (REG_TEST_0, "REG_TEST_0"),
            (REG_TEST_1, "REG_TEST_1"),
            (REG_TEST_2, "REG_TEST_2"),
            (REG_TEST_3, "REG_TEST_3")
        ]
        
        all_passed = True
        
        for addr, name in registers:
            print(f"\n📍 Testing {name} (0x{addr:08X})")
            print("-" * 30)
            
            # 初期値読み出し
            initial = self.read_register(addr)
            if initial is not None:
                print(f"  Initial value: 0x{initial:08X}")
            else:
                print(f"  ❌ Failed to read initial value")
                all_passed = False
                continue
            
            # テスト値書き込み
            test_value = 0x12345678
            print(f"  Writing: 0x{test_value:08X}")
            if self.write_register(addr, test_value):
                print(f"  ✅ Write successful")
                
                # 読み戻し
                read_back = self.read_register(addr)
                if read_back == test_value:
                    print(f"  ✅ Read-back OK: 0x{read_back:08X}")
                else:
                    print(f"  ❌ Read-back failed: expected 0x{test_value:08X}, got 0x{read_back:08X}")
                    all_passed = False
            else:
                print(f"  ❌ Write failed")
                all_passed = False
            
            # 別の値でテスト
            test_value2 = 0xDEADBEEF
            print(f"  Writing: 0x{test_value2:08X}")
            if self.write_register(addr, test_value2):
                read_back2 = self.read_register(addr)
                if read_back2 == test_value2:
                    print(f"  ✅ Second test OK: 0x{read_back2:08X}")
                else:
                    print(f"  ❌ Second test failed")
                    all_passed = False
        
        return all_passed

def main():
    """メイン関数"""
    print("🔬 FPGA REG_TEST Simple Verification")
    print("🎯 Basic read/write functionality test")
    print("=" * 50)
    
    tester = SimpleFPGATester("COM3", 115200)
    
    if not tester.connect():
        return False
    
    try:
        success = tester.test_basic_operations()
        
        print("\n" + "=" * 50)
        if success:
            print("🎉 All basic tests PASSED!")
            print("✅ REG_TEST_0〜3 registers are working correctly")
        else:
            print("❌ Some tests FAILED!")
            print("⚠️  Please check FPGA configuration")
        print("=" * 50)
        
        return success
        
    except Exception as e:
        print(f"\n❌ Test error: {e}")
        return False
    finally:
        tester.disconnect()

if __name__ == "__main__":
    success = main()
    exit(0 if success else 1)