#!/usr/bin/env python3
"""
UART基本通信テスト - FPGAの最低限の応答確認
"""

import serial
import time

def basic_uart_test():
    """最低限のUART通信テスト"""
    print("🔧 基本UART通信テスト")
    print("=" * 40)
    
    try:
        with serial.Serial('COM3', 115200, timeout=1) as ser:
            print("✅ COM3接続成功")
            
            # 1. 単純なバイト送信テスト
            print("\n📤 単純バイト送信テスト")
            test_bytes = [0xA5, 0xFF, 0x00, 0x55, 0xAA]
            
            for test_byte in test_bytes:
                print(f"送信: 0x{test_byte:02X}")
                ser.write(bytes([test_byte]))
                time.sleep(0.1)
                
                response = ser.read(10)
                if response:
                    response_list = list(response)
                    print(f"受信: {' '.join(f'0x{b:02X}' for b in response_list)}")
                else:
                    print("受信: なし")
                
                time.sleep(0.2)
            
            # 2. 連続送信テスト
            print(f"\n📤 連続送信テスト")
            continuous_data = bytes([0xA5, 0x00, 0x00, 0x10, 0x00, 0x00, 0xF8])
            print(f"送信: {' '.join(f'0x{b:02X}' for b in continuous_data)}")
            
            ser.write(continuous_data)
            time.sleep(0.5)
            
            response = ser.read(50)
            if response:
                response_list = list(response)
                print(f"受信: {' '.join(f'0x{b:02X}' for b in response_list)}")
                
                # レスポンスの分析
                if len(response_list) >= 4:
                    if response_list[0] == 0xAD:
                        print("⚠️  SOF異常検出")
                    if response_list[1] == 0x82:
                        print("⚠️  STATUS異常検出") 
                        
            else:
                print("受信: なし")
            
            # 3. 異なるボーレートテスト（診断用）
            print(f"\n📤 ボーレート診断")
            print("現在のボーレート: 115200")
            
    except Exception as e:
        print(f"❌ エラー: {e}")

if __name__ == "__main__":
    basic_uart_test()