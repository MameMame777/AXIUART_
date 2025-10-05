#!/usr/bin/env python3
"""
FPGA完全診断ツール - より詳細な調査
"""

import serial
import time

def comprehensive_fpga_diagnosis():
    """包括的なFPGA診断"""
    print("🔬 FPGA完全診断開始")
    print("=" * 60)
    
    try:
        with serial.Serial('COM3', 115200, timeout=3) as ser:
            print("✅ COM3接続成功")
            
            # 1. 空のバッファクリア
            print("\n🧹 バッファクリア")
            ser.reset_input_buffer()
            ser.reset_output_buffer()
            time.sleep(0.5)
            
            # 2. 基本的な単一バイト送信テスト
            print("\n📡 基本送信テスト")
            single_bytes = [0x00, 0xFF, 0xA5, 0x5A, 0xAD]
            
            for test_byte in single_bytes:
                print(f"  送信: 0x{test_byte:02X}")
                ser.write(bytes([test_byte]))
                time.sleep(0.2)
                
                response = ser.read(20)
                if response:
                    response_list = list(response)
                    print(f"  受信: {' '.join(f'0x{b:02X}' for b in response_list)}")
                else:
                    print("  受信: なし")
                
                time.sleep(0.3)
            
            # 3. プロトコルフレームテスト（複数パターン）
            print(f"\n📋 プロトコルフレーム診断")
            
            # 異なるアドレスパターンでテスト
            test_cases = [
                {"addr": 0x00000000, "desc": "ゼロアドレス"},
                {"addr": 0x00001000, "desc": "ベースアドレス"},
                {"addr": 0x00001004, "desc": "ステータスレジスタ"},
                {"addr": 0xFFFFFFFF, "desc": "最大アドレス"}
            ]
            
            for case in test_cases:
                addr = case["addr"]
                desc = case["desc"]
                
                print(f"\n  📍 {desc} (0x{addr:08X})")
                
                # フレーム構築（正確なCRC計算）
                frame_data = [0xA5, 0x00]  # SOF + CMD_READ
                frame_data.extend([(addr >> (8*i)) & 0xFF for i in range(4)])  # アドレス(リトルエンディアン)
                
                # CRC-8計算
                crc = 0x00
                for byte in frame_data:
                    crc ^= byte
                    for _ in range(8):
                        if crc & 0x80:
                            crc = (crc << 1) ^ 0x07
                        else:
                            crc = crc << 1
                        crc &= 0xFF
                
                frame_data.append(crc)
                
                print(f"    送信: {' '.join(f'0x{b:02X}' for b in frame_data)}")
                
                # バッファクリア
                ser.reset_input_buffer()
                
                # 送信
                ser.write(bytes(frame_data))
                time.sleep(0.5)  # 十分な待機時間
                
                # 応答受信
                response = ser.read(50)
                
                if response:
                    response_list = list(response)
                    print(f"    受信: {' '.join(f'0x{b:02X}' for b in response_list)}")
                    
                    # 詳細分析
                    if len(response_list) >= 2:
                        sof_rx = response_list[0]
                        status_rx = response_list[1]
                        
                        print(f"    分析:")
                        print(f"      SOF: 0x{sof_rx:02X} {'✅' if sof_rx == 0x5A else '❌'}")
                        print(f"      STATUS: 0x{status_rx:02X} {'✅' if status_rx in [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07] else '❌'}")
                        
                        # パターン分析
                        if sof_rx == 0xAD and status_rx == 0x82:
                            print(f"      ⚠️  固定パターン検出: FPGA未動作の可能性")
                        elif len(response_list) == 4 and response_list == [0xAD, 0x82, 0x40, 0xD5]:
                            print(f"      🚨 完全に同一の固定応答: プロトコル処理停止")
                
                else:
                    print(f"    受信: なし (タイムアウト)")
                
                time.sleep(1.0)
            
            # 4. バッファ状態の最終確認
            print(f"\n🔍 最終バッファ確認")
            ser.reset_input_buffer()
            time.sleep(0.1)
            remaining = ser.read(100)
            if remaining:
                print(f"バッファ残存データ: {' '.join(f'0x{b:02X}' for b in remaining)}")
            else:
                print("バッファクリア")
            
    except Exception as e:
        print(f"❌ 診断エラー: {e}")
    
    print("\n" + "=" * 60)
    print("🔬 完全診断終了")

if __name__ == "__main__":
    comprehensive_fpga_diagnosis()