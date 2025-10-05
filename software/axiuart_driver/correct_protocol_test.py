#!/usr/bin/env python3
"""
正確なCRC-8プロトコルフレーム送信テスト
UART–AXI4-Lite Bridge Protocol v0.1 完全準拠
"""

import serial
import time
from datetime import datetime

def calculate_crc8(data):
    """
    CRC-8計算 (標準的なCRC-8-CCITT)
    Polynomial: 0x07 (x^8 + x^2 + x + 1)
    """
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

def build_read_frame(address):
    """READフレーム構築 (CRC付き)"""
    # Protocol: SOF + CMD + ADDR(4bytes) + CRC
    sof = 0xA5  # Host to Device
    cmd = 0xA0  # Read, SIZE=2 (32-bit), LEN=1
    
    addr_bytes = [
        (address >> 24) & 0xFF,  # MSB first
        (address >> 16) & 0xFF,
        (address >> 8) & 0xFF,
        address & 0xFF           # LSB
    ]
    
    # CRC計算対象: CMD + ADDR
    frame_without_crc = [cmd] + addr_bytes
    crc = calculate_crc8(frame_without_crc)
    
    # 完全フレーム
    frame = [sof] + frame_without_crc + [crc]
    return frame

def build_write_frame(address, data_value):
    """WRITEフレーム構築 (CRC付き)"""
    # Protocol: SOF + CMD + ADDR(4bytes) + DATA(4bytes) + CRC
    sof = 0xA5  # Host to Device
    cmd = 0x20  # Write, SIZE=2 (32-bit), LEN=1
    
    addr_bytes = [
        (address >> 24) & 0xFF,
        (address >> 16) & 0xFF,
        (address >> 8) & 0xFF,
        address & 0xFF
    ]
    
    data_bytes = [
        (data_value >> 24) & 0xFF,
        (data_value >> 16) & 0xFF,
        (data_value >> 8) & 0xFF,
        data_value & 0xFF
    ]
    
    # CRC計算対象: CMD + ADDR + DATA
    frame_without_crc = [cmd] + addr_bytes + data_bytes
    crc = calculate_crc8(frame_without_crc)
    
    # 完全フレーム
    frame = [sof] + frame_without_crc + [crc]
    return frame

def test_correct_protocol():
    """正確なプロトコルフレームでのテスト"""
    
    print("🔬 正確なCRC-8プロトコルフレームテスト")
    print("=" * 60)
    print(f"実行時刻: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    
    # RTLレジスタアドレス定義
    BASE_ADDR = 0x00001000
    registers = {
        "REG_CONTROL": BASE_ADDR + 0x000,
        "REG_STATUS": BASE_ADDR + 0x004,
        "REG_CONFIG": BASE_ADDR + 0x008,
        "REG_VERSION": BASE_ADDR + 0x01C,
        "REG_TX_COUNT": BASE_ADDR + 0x010,
    }
    
    try:
        with serial.Serial('COM3', 115200, timeout=2) as ser:
            print("✅ COM3接続成功")
            time.sleep(0.1)
            
            # 各レジスタの読み込みテスト
            for reg_name, reg_addr in registers.items():
                print(f"\n📤 {reg_name} Read (0x{reg_addr:08X})")
                
                # 正確なCRC付きフレーム構築
                frame = build_read_frame(reg_addr)
                frame_hex = ' '.join(f'{b:02X}' for b in frame)
                print(f"   送信フレーム: {frame_hex}")
                print(f"   CRC-8: 0x{frame[-1]:02X}")
                
                # フレーム送信
                ser.write(bytes(frame))
                time.sleep(0.1)
                
                # 応答受信
                response = ser.read(16)
                if response:
                    response_hex = ' '.join(f'{b:02X}' for b in response)
                    print(f"📥 受信データ: {response_hex}")
                    
                    if len(response) >= 1:
                        sof_received = response[0]
                        print(f"   SOF: 0x{sof_received:02X} (期待値: 0x5A)")
                        
                        if sof_received == 0x5A:
                            print("   ✅ SOF正常")
                        else:
                            print(f"   ❌ SOF異常 (0x{sof_received:02X})")
                            
                    analyze_response_structure(response)
                else:
                    print("   ❌ 応答なし")
                
                time.sleep(0.3)
            
            # 書き込みテスト
            print(f"\n📤 REG_CONTROL Write Test")
            write_frame = build_write_frame(registers["REG_CONTROL"], 0x00000001)
            frame_hex = ' '.join(f'{b:02X}' for b in write_frame)
            print(f"   送信フレーム: {frame_hex}")
            print(f"   CRC-8: 0x{write_frame[-1]:02X}")
            
            ser.write(bytes(write_frame))
            time.sleep(0.1)
            
            response = ser.read(8)
            if response:
                response_hex = ' '.join(f'{b:02X}' for b in response)
                print(f"📥 受信データ: {response_hex}")
                analyze_response_structure(response)
            else:
                print("   ❌ 応答なし")
                
    except Exception as e:
        print(f"❌ エラー: {e}")

def analyze_response_structure(response):
    """応答フレーム構造解析"""
    if len(response) < 3:
        print("   ⚠️  短いフレーム")
        return
        
    print(f"   📊 フレーム解析:")
    print(f"     データ長: {len(response)} bytes")
    print(f"     SOF: 0x{response[0]:02X}")
    
    if len(response) >= 2:
        print(f"     STATUS: 0x{response[1]:02X}")
        
    if len(response) >= 3:
        print(f"     CMD_ECHO: 0x{response[2]:02X}")
        
    if len(response) >= 4:
        remaining = response[3:]
        print(f"     残りデータ: {' '.join(f'{b:02X}' for b in remaining)}")

def manual_crc_test():
    """手動CRC計算確認"""
    print("\n🧮 CRC-8計算確認")
    print("=" * 30)
    
    # REG_VERSION読み込みフレームの手動計算
    cmd = 0xA0
    addr = 0x0000101C
    addr_bytes = [0x00, 0x00, 0x10, 0x1C]
    
    data_for_crc = [cmd] + addr_bytes
    crc = calculate_crc8(data_for_crc)
    
    print(f"データ: {' '.join(f'{b:02X}' for b in data_for_crc)}")
    print(f"CRC-8: 0x{crc:02X}")
    
    full_frame = [0xA5] + data_for_crc + [crc]
    print(f"完全フレーム: {' '.join(f'{b:02X}' for b in full_frame)}")

if __name__ == "__main__":
    manual_crc_test()
    test_correct_protocol()
    print("\n✨ プロトコルテスト完了")