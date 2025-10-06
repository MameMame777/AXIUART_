#!/usr/bin/env python3
"""
FPGA リセット直後の初期値確認テスト
"""

import serial
import time
import struct

# Protocol constants (updated for current FPGA behavior)
SOF_HOST_TO_DEVICE = 0xA5
SOF_DEVICE_TO_HOST_ACTUAL = 0xAD  # Current FPGA implementation
CMD_READ = 0xA0
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

def read_register(ser: serial.Serial, addr: int) -> int:
    """Read from register and return value"""
    # Build command frame
    frame = bytearray()
    frame.append(SOF_HOST_TO_DEVICE)
    frame.append(CMD_READ)
    frame.extend(struct.pack('<I', addr))  # Address (little-endian)
    
    # Calculate and append CRC
    crc = calculate_crc8(frame[1:])  # Exclude SOF
    frame.append(crc)
    
    # Send frame
    print(f"📤 読み出しリクエスト (0x{addr:08X}): {' '.join([f'{b:02X}' for b in frame])}")
    ser.write(frame)
    time.sleep(0.1)
    
    # Receive response
    response = bytearray()
    for _ in range(20):  # Wait up to 2 seconds
        if ser.in_waiting > 0:
            response.extend(ser.read(ser.in_waiting))
            if len(response) >= 8:
                break
        time.sleep(0.1)
    
    if response and len(response) >= 8:
        print(f"📥 応答: {' '.join([f'{b:02X}' for b in response])}")
        if response[0] == SOF_DEVICE_TO_HOST_ACTUAL and response[1] == STATUS_OK_ACTUAL:
            # Extract data from response (bytes 3-6 in little-endian)
            data_bytes = response[3:7]
            value = struct.unpack('<I', data_bytes)[0]
            print(f"✅ 読み出し成功: 0x{addr:08X} = 0x{value:08X}")
            return value
        else:
            print(f"❌ 応答エラー: SOF=0x{response[0]:02X}, STATUS=0x{response[1]:02X}")
    else:
        print("❌ 応答なし")
    return None

def main():
    """FPGA初期値テストのメイン関数"""
    print("🔍 FPGA リセット直後の初期値確認テスト")
    print("=" * 60)
    print("⚠️ このテストはFPGAがリセット直後であることを前提としています")
    print("   (システムリセット後、書き込み操作を実行していない状態)")
    print()
    
    try:
        ser = serial.Serial("COM3", 115200, timeout=1)
        time.sleep(0.1)
        print("✅ COM3に接続しました\n")
        
        # Test addresses
        test_addresses = [
            0x00001020,  # REG_TEST_0
            0x00001024,  # REG_TEST_1 
            0x00001028,  # REG_TEST_2
            0x0000102C,  # REG_TEST_3
        ]
        
        # 期待される初期値 (RTLコードから)
        expected_values = [
            0xDEADBEEF,  # test_reg_0
            0x12345678,  # test_reg_1
            0xABCDEF00,  # test_reg_2
            0x00000000,  # test_reg_3
        ]
        
        print("📋 レジスタ初期値確認:")
        print("-" * 50)
        
        actual_values = []
        for addr, expected in zip(test_addresses, expected_values):
            actual = read_register(ser, addr)
            actual_values.append(actual)
            
            if actual is not None:
                if actual == expected:
                    print(f"🎯 一致: 0x{addr:08X} = 0x{actual:08X} (RTL仕様通り)")
                else:
                    print(f"⚠️  不一致: 0x{addr:08X} = 0x{actual:08X} (期待: 0x{expected:08X})")
            print()
            time.sleep(0.2)
        
        print("📊 分析結果:")
        print("-" * 30)
        
        # パターン分析
        if all(v is not None for v in actual_values):
            print("🔍 読み出された値のパターン分析:")
            for i, (addr, value) in enumerate(zip(test_addresses, actual_values)):
                print(f"  0x{addr:08X}: 0x{value:08X}")
                
                # バイト分解
                bytes_le = [(value >> (8*j)) & 0xFF for j in range(4)]
                print(f"    バイト分解 (LE): {' '.join([f'{b:02X}' for b in bytes_le])}")
                
                # 固定部分の確認
                if i == 0:
                    base_pattern = value & 0xFFFFFF00  # 下位8ビット除く
                    print(f"    固定部分: 0x{base_pattern:08X}")
                else:
                    current_base = value & 0xFFFFFF00
                    if current_base == base_pattern:
                        print(f"    固定部分一致: 0x{current_base:08X}")
                    else:
                        print(f"    固定部分不一致: 0x{current_base:08X}")
                
                print(f"    カウンタ部分: 0x{value & 0xFF:02X}")
                print()
                
            # RTL初期値との比較
            matches_rtl = sum(1 for a, e in zip(actual_values, expected_values) if a == e)
            print(f"📈 RTL仕様との一致率: {matches_rtl}/{len(expected_values)} ({100*matches_rtl/len(expected_values):.1f}%)")
            
            if matches_rtl == 0:
                print("🚨 現在のFPGAにはRTLコードと異なるバージョンが実装されている可能性があります")
            elif matches_rtl < len(expected_values):
                print("⚠️  部分的に異なる実装またはテストパターンが混入している可能性があります")
            else:
                print("✅ RTL仕様通りの実装です")
        
        ser.close()
        print("\n🔌 UART接続を終了しました")
        
    except Exception as e:
        print(f"❌ エラー: {e}")

if __name__ == "__main__":
    main()