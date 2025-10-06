#!/usr/bin/env python3
"""
緊急診断: 読み取り応答フォーマット分析
実測値で期待値は修正されたが、応答フォーマットに問題がある
"""

import serial
import time

def analyze_read_response():
    """読み取り応答の詳細分析"""
    
    # シリアル接続
    ser = serial.Serial('COM3', 115200, timeout=5)
    print("🔍 読み取り応答フォーマット詳細分析")
    print("="*50)
    
    try:
        # REG_TEST_0読み取りコマンド
        read_cmd = bytes([0xA5, 0xA0, 0x20, 0x10, 0x00, 0x00, 0x9F])
        
        for attempt in range(3):
            print(f"\n📡 試行 {attempt+1}: REG_TEST_0 読み取り")
            
            # 送信
            ser.write(read_cmd)
            print(f"📤 送信: {' '.join(f'{b:02X}' for b in read_cmd)}")
            
            # 応答受信 (最大10バイト)
            time.sleep(0.1)
            response = ser.read(10)
            print(f"📥 受信: {' '.join(f'{b:02X}' for b in response)} (長さ: {len(response)})")
            
            if len(response) >= 2:
                sof = response[0]
                status = response[1]
                print(f"   SOF: 0x{sof:02X}, STATUS: 0x{status:02X}")
                
                if len(response) > 2:
                    print(f"   データ部: {' '.join(f'{b:02X}' for b in response[2:])}")
                    
                    # 期待される読み取り応答パターン分析
                    if len(response) == 7:
                        # SOF + STATUS + CMD + DATA(4) の可能性
                        if len(response) >= 7:
                            cmd = response[2]
                            data = int.from_bytes(response[3:7], byteorder='little')
                            print(f"   👀 解析: CMD=0x{cmd:02X}, DATA=0x{data:08X}")
                            
            time.sleep(0.2)
            
    except Exception as e:
        print(f"❌ エラー: {e}")
        
    finally:
        ser.close()
        print("\n🔌 切断完了")

if __name__ == "__main__":
    analyze_read_response()