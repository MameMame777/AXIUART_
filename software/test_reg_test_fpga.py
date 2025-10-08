#!/usr/bin/env python3
"""
FPGA実機でのREG_TEST_0〜3レジスタ完全検証スクリプト
UVMテストで実行した13パターンの検証をFPGA実機で実行
Based on successful UVM verification results (76/76 transactions passed)
"""

import serial
import time
import struct
from typing import Optional, Union
import random

# プロトコル定数 (UVMテスト結果ベース)
PROTOCOL_SOF_REQUEST = 0xA5       # Host→Device SOF
PROTOCOL_SOF_RESPONSE = 0x5A      # Device→Host SOF (UVM実測値)
PROTOCOL_STATUS_OK = 0x00         # Success status (UVM実測値)
PROTOCOL_CMD_READ = 0xA0          # Read command
PROTOCOL_CMD_WRITE = 0x20         # Write command

# REG_TEST レジスタアドレス (BASE_ADDR=0x1000)
REG_TEST_0 = 0x00001020  # Test register 0 (pure read/write test)
REG_TEST_1 = 0x00001024  # Test register 1 (pattern test)
REG_TEST_2 = 0x00001028  # Test register 2 (increment test)
REG_TEST_3 = 0x0000102C  # Test register 3 (mirror test)

# UVMテストで設定された初期値
INITIAL_VALUES = {
    REG_TEST_0: 0xDEADBEEF,
    REG_TEST_1: 0x12345678,
    REG_TEST_2: 0xABCDEF00,
    REG_TEST_3: 0x00000000
}

class FPGARegisterTester:
    def __init__(self, port: str = "COM3", baudrate: int = 115200):
        self.port = port
        self.baudrate = baudrate
        self.serial = None
        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0
        
    def connect(self) -> bool:
        """UART接続"""
        try:
            self.serial = serial.Serial(self.port, self.baudrate, timeout=2.0)
            time.sleep(0.1)
            print(f"✅ Connected to {self.port} at {self.baudrate} baud")
            return True
        except Exception as e:
            print(f"❌ Failed to connect: {e}")
            return False
    
    def disconnect(self):
        """UART切断"""
        if self.serial and self.serial.is_open:
            self.serial.close()
            print("🔌 Disconnected from UART")
    
    def crc8_calculate(self, data: bytes) -> int:
        """CRC8計算 (polynomial 0x07)"""
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
        if not self.serial or not self.serial.is_open:
            return None
        
        # UVMテスト形式のフレーム構築
        frame = bytearray()
        frame.append(PROTOCOL_SOF_REQUEST)  # SOF
        frame.append(cmd)                   # Command
        frame.extend(struct.pack('<I', addr))  # Address (little-endian)
        
        if cmd == PROTOCOL_CMD_WRITE:
            frame.extend(data)  # Write data
        
        # CRC計算・追加 (SOF除く)
        crc = self.crc8_calculate(frame[1:])
        frame.append(crc)
        
        print(f"📤 TX: {' '.join(f'{b:02X}' for b in frame)}")
        
        # 送信
        self.serial.reset_input_buffer()
        self.serial.write(frame)
        self.serial.flush()
        time.sleep(0.05)  # 応答待機
        
        # 応答受信
        response = self.serial.read(100)
        if response:
            print(f"📥 RX: {' '.join(f'{b:02X}' for b in response)}")
            return response
        else:
            print("❌ No response received")
            return None
    
    def read_register(self, addr: int) -> Optional[int]:
        """32bitレジスタ読み出し"""
        response = self.send_command(PROTOCOL_CMD_READ, addr)
        
        if not response or len(response) < 8:
            print(f"❌ Invalid response length: {len(response) if response else 0}")
            return None
        
        # 応答解析 (8バイト期待: SOF[1] + STATUS[1] + CMD[1] + DATA[4] + CRC[1])
        if len(response) == 8:
            sof, status, cmd = response[0], response[1], response[2]
            data_bytes = response[3:7]
            crc = response[7]
            
            # データ値抽出 (little-endian)
            data_value = struct.unpack('<I', data_bytes)[0]
            
            # 応答検証
            if status == PROTOCOL_STATUS_OK and sof == PROTOCOL_SOF_RESPONSE:
                return data_value
            else:
                print(f"❌ Error - SOF: 0x{sof:02X}, STATUS: 0x{status:02X}")
                return None
        
        print(f"❌ Unexpected response format")
        return None
    
    def write_register(self, addr: int, value: int) -> bool:
        """32bitレジスタ書き込み"""
        data = struct.pack('<I', value)
        response = self.send_command(PROTOCOL_CMD_WRITE, addr, data)
        
        if not response or len(response) < 4:
            return False
        
        # 書き込み応答解析 (4バイト期待: SOF[1] + STATUS[1] + CMD[1] + CRC[1])
        if len(response) >= 4:
            sof, status = response[0], response[1]
            if status == PROTOCOL_STATUS_OK and sof == PROTOCOL_SOF_RESPONSE:
                return True
            else:
                print(f"❌ Write Error - SOF: 0x{sof:02X}, STATUS: 0x{status:02X}")
        
        return False
    
    def test_register_operation(self, test_name: str, addr: int, write_value: int, expected_read: Optional[int] = None) -> bool:
        """個別レジスタテスト実行"""
        if expected_read is None:
            expected_read = write_value
            
        self.test_count += 1
        print(f"\n🧪 Test {self.test_count}: {test_name}")
        print(f"   Address: 0x{addr:08X}, Write: 0x{write_value:08X}, Expected: 0x{expected_read:08X}")
        
        # 書き込み
        if not self.write_register(addr, write_value):
            print(f"❌ Write failed")
            self.fail_count += 1
            return False
        
        time.sleep(0.01)  # 安定化待機
        
        # 読み出し
        read_value = self.read_register(addr)
        if read_value is None:
            print(f"❌ Read failed")
            self.fail_count += 1
            return False
        
        # 検証
        if read_value == expected_read:
            print(f"✅ PASS - Read: 0x{read_value:08X}")
            self.pass_count += 1
            return True
        else:
            print(f"❌ FAIL - Expected: 0x{expected_read:08X}, Got: 0x{read_value:08X}")
            self.fail_count += 1
            return False
    
    def run_comprehensive_tests(self) -> bool:
        """UVMテストと同等の包括的テスト実行"""
        print("🚀 REG_TEST_0〜3 包括的検証開始 (UVMテスト準拠)")
        print("=" * 70)
        
        all_passed = True
        registers = [REG_TEST_0, REG_TEST_1, REG_TEST_2, REG_TEST_3]
        reg_names = ["REG_TEST_0", "REG_TEST_1", "REG_TEST_2", "REG_TEST_3"]
        
        # Test 1: 初期値確認
        print(f"\n📋 Phase 1: 初期値確認")
        print("-" * 50)
        for addr, name in zip(registers, reg_names):
            print(f"\n🔍 {name} 初期値読み出し")
            initial_value = self.read_register(addr)
            if initial_value is not None:
                expected = INITIAL_VALUES[addr]
                if initial_value == expected:
                    print(f"✅ {name}: 0x{initial_value:08X} (期待値と一致)")
                else:
                    print(f"⚠️  {name}: 0x{initial_value:08X} (期待値: 0x{expected:08X})")
            else:
                print(f"❌ {name}: 読み出し失敗")
                all_passed = False
        
        # Test 2: 全ビット書き込みテスト
        print(f"\n📋 Phase 2: 全ビット書き込みテスト")
        print("-" * 50)
        for addr, name in zip(registers, reg_names):
            if not self.test_register_operation(f"{name} All 1s Test", addr, 0xFFFFFFFF):
                all_passed = False
        
        # Test 3: ウォーキング1ビットテスト
        print(f"\n📋 Phase 3: ウォーキング1ビットテスト")
        print("-" * 50)
        for bit in range(32):
            walking_1_value = 1 << bit
            for addr, name in zip(registers, reg_names):
                if not self.test_register_operation(f"{name} Walking 1 Bit {bit}", addr, walking_1_value):
                    all_passed = False
        
        # Test 4: ウォーキング0ビットテスト
        print(f"\n📋 Phase 4: ウォーキング0ビットテスト")
        print("-" * 50)
        for bit in range(32):
            walking_0_value = 0xFFFFFFFF ^ (1 << bit)
            for addr, name in zip(registers, reg_names):
                if not self.test_register_operation(f"{name} Walking 0 Bit {bit}", addr, walking_0_value):
                    all_passed = False
        
        # Test 5: 境界値テスト
        print(f"\n📋 Phase 5: 境界値テスト")
        print("-" * 50)
        boundary_values = [0x00000000, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF]
        for value in boundary_values:
            for addr, name in zip(registers, reg_names):
                if not self.test_register_operation(f"{name} Boundary 0x{value:08X}", addr, value):
                    all_passed = False
        
        # Test 6: ランダムパターンテスト
        print(f"\n📋 Phase 6: ランダムパターンテスト")
        print("-" * 50)
        random.seed(42)  # 再現可能性のため
        for test_num in range(10):
            random_value = random.randint(0, 0xFFFFFFFF)
            for addr, name in zip(registers, reg_names):
                if not self.test_register_operation(f"{name} Random Test {test_num+1}", addr, random_value):
                    all_passed = False
        
        # Test 7: 最終状態確認
        print(f"\n📋 Phase 7: 最終状態確認")
        print("-" * 50)
        final_values = [0xDEADBEEF, 0x12345678, 0xABCDEF00, 0x55AA55AA]
        for addr, name, value in zip(registers, reg_names, final_values):
            if not self.test_register_operation(f"{name} Final State", addr, value):
                all_passed = False
        
        return all_passed
    
    def print_test_summary(self):
        """テスト結果サマリー表示"""
        print("\n" + "=" * 70)
        print("📊 TEST SUMMARY")
        print("=" * 70)
        print(f"Total Tests:  {self.test_count}")
        print(f"Passed:       {self.pass_count} ✅")
        print(f"Failed:       {self.fail_count} ❌")
        print(f"Success Rate: {(self.pass_count/self.test_count*100):.1f}%" if self.test_count > 0 else "N/A")
        
        if self.fail_count == 0:
            print("\n🎉 ALL TESTS PASSED! REG_TEST_0〜3 registers are fully functional!")
            print("🔧 FPGA実機でのレジスタ機能が完全に検証されました")
        else:
            print(f"\n⚠️  {self.fail_count} tests failed. Please check FPGA configuration.")
        
        print("=" * 70)

def main():
    """メイン実行関数"""
    print("🔬 FPGA REG_TEST_0〜3 Register Comprehensive Verification")
    print("🎯 Based on successful UVM test results (76/76 transactions)")
    print("=" * 70)
    
    tester = FPGARegisterTester("COM3", 115200)
    
    if not tester.connect():
        print("❌ UART接続に失敗しました")
        return False
    
    try:
        # 包括的テスト実行
        success = tester.run_comprehensive_tests()
        
        # 結果表示
        tester.print_test_summary()
        
        return success
        
    except KeyboardInterrupt:
        print("\n⚠️  テストが中断されました")
        return False
    except Exception as e:
        print(f"\n❌ テスト実行中にエラーが発生しました: {e}")
        return False
    finally:
        tester.disconnect()

if __name__ == "__main__":
    success = main()
    exit(0 if success else 1)