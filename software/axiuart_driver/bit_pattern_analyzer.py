#!/usr/bin/env python3
"""
FPGA ビットパターン解析ツール
0x5A → 0xAD 変換の詳細解析
"""

import serial
import time
import sys
from datetime import datetime

def analyze_bit_patterns():
    """複数のビットパターンを送信して変換を解析"""
    
    print("🔬 FPGA ビットパターン解析ツール")
    print("=" * 60)
    print(f"実行時刻: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    
    # テストパターン定義
    test_patterns = [
        0x5A,  # 01011010 → 期待される応答: 0xAD
        0x00,  # 00000000 → 予想: 0x00
        0xFF,  # 11111111 → 予想: 0xFF  
        0xAA,  # 10101010 → 予想: 0x55
        0x55,  # 01010101 → 予想: 0xAA
        0x0F,  # 00001111 → 予想: 0xF0
        0xF0,  # 11110000 → 予想: 0x0F
    ]
    
    try:
        with serial.Serial('COM3', 115200, timeout=2) as ser:
            print("✅ COM3接続成功")
            time.sleep(0.1)
            
            print("\n🧪 ビットパターン解析:")
            print("=" * 50)
            
            for pattern in test_patterns:
                # CRC-8計算 (簡易版)
                crc = calculate_simple_crc8([0xA5, 0xA0, 0x00, 0x10, 0x00, 0x00])
                
                # REG_VERSION読み込みフレーム (0x101C)
                frame = [0xA5, 0xA0, 0x1C, 0x10, 0x00, 0x00, crc]
                
                print(f"\n📤 Test Pattern: 0x{pattern:02X} (0b{pattern:08b})")
                print(f"   送信フレーム: {' '.join(f'{b:02X}' for b in frame)}")
                
                # 送信
                ser.write(bytes(frame))
                time.sleep(0.1)
                
                # 受信
                response = ser.read(16)
                if response:
                    print(f"📥 受信データ: {' '.join(f'{b:02X}' for b in response)}")
                    if response:
                        sof_received = response[0]
                        print(f"   SOF変換: 0x{pattern:02X} → 0x{sof_received:02X}")
                        print(f"   ビット比較:")
                        print(f"     送信: 0x{pattern:02X} = {pattern:08b}")
                        print(f"     受信: 0x{sof_received:02X} = {sof_received:08b}")
                        
                        # ビット変換解析
                        analyze_bit_transformation(pattern, sof_received)
                else:
                    print("   ❌ 応答なし")
                
                time.sleep(0.2)
                
    except Exception as e:
        print(f"❌ エラー: {e}")

def analyze_bit_transformation(sent, received):
    """ビット変換パターンを解析"""
    
    # 各種変換パターンをテスト
    transforms = {
        "ビット反転": ~sent & 0xFF,
        "ビット順序逆転": int(f'{sent:08b}'[::-1], 2),
        "ビット反転+順序逆転": ~int(f'{sent:08b}'[::-1], 2) & 0xFF,
        "左1ビットシフト": (sent << 1) & 0xFF,
        "右1ビットシフト": sent >> 1,
        "XOR 0xFF": sent ^ 0xFF,
    }
    
    print(f"   🔍 変換パターン解析:")
    for name, result in transforms.items():
        match = "✅" if result == received else "❌"
        print(f"     {match} {name}: 0x{result:02X} ({result:08b})")

def calculate_simple_crc8(data):
    """簡易CRC-8計算"""
    crc = 0
    for byte in data:
        crc ^= byte
        for _ in range(8):
            if crc & 0x80:
                crc = (crc << 1) ^ 0x07
            else:
                crc <<= 1
            crc &= 0xFF
    return crc

def test_uart_bit_order():
    """UART送信でのビット順序テスト"""
    
    print("\n🔍 UART ビット順序テスト")
    print("=" * 40)
    
    # 単純な1バイト送信でのテスト
    test_bytes = [0x5A, 0xAD, 0xAA, 0x55]
    
    try:
        with serial.Serial('COM3', 115200, timeout=1) as ser:
            for test_byte in test_bytes:
                print(f"\n📤 Raw送信: 0x{test_byte:02X} ({test_byte:08b})")
                
                # 生バイト送信（プロトコルフレームなし）
                ser.write(bytes([test_byte]))
                time.sleep(0.1)
                
                # エコー確認（もし存在すれば）
                response = ser.read(4)
                if response:
                    print(f"📥 エコー: {' '.join(f'{b:02X}' for b in response)}")
                else:
                    print("   エコーなし（正常）")
                    
    except Exception as e:
        print(f"❌ エラー: {e}")

if __name__ == "__main__":
    print("FPGA ビットパターン解析開始")
    analyze_bit_patterns()
    test_uart_bit_order()
    print("\n✨ 解析完了")