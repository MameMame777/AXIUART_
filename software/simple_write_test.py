#!/usr/bin/env python3
"""
シンプルなレジスタ書き込みテスト
問題の根本原因を特定
"""

import serial
import time

def simple_write_test():
    """一つのレジスタに対するシンプルな書き込みテスト"""
    
    print("🧪 シンプルなレジスタ書き込みテスト")
    print("="*40)
    
    ser = serial.Serial('COM3', 115200, timeout=5)
    
    try:
        # テスト対象: REG_TEST_0 (0x00001020)
        test_addr = 0x00001020
        
        print(f"📍 テスト対象: REG_TEST_0 (0x{test_addr:08X})")
        
        # Step 1: 初期値読み取り
        print("\n🔍 Step 1: 初期値読み取り")
        read_cmd = bytes([0xA5, 0xA0, 0x20, 0x10, 0x00, 0x00, 0x9F])
        ser.write(read_cmd)
        print(f"📤 送信: {' '.join(f'{b:02X}' for b in read_cmd)}")
        
        time.sleep(0.1)
        response = ser.read(10)
        print(f"📥 受信: {' '.join(f'{b:02X}' for b in response)}")
        
        if len(response) >= 7:
            initial_value = int.from_bytes(response[3:7], byteorder='little')
            print(f"📊 初期値: 0x{initial_value:08X}")
        else:
            print("❌ 初期値読み取り失敗")
            return
            
        # Step 2: テスト値書き込み
        print("\n✏️  Step 2: テスト値書き込み")
        test_value = 0xAAAABBBB
        write_cmd = [0xA5, 0x20, 0x20, 0x10, 0x00, 0x00,
                     test_value & 0xFF, (test_value >> 8) & 0xFF,
                     (test_value >> 16) & 0xFF, (test_value >> 24) & 0xFF]
        
        # CRC計算
        crc = sum(write_cmd) & 0xFF
        write_cmd.append(crc)
        
        ser.write(bytes(write_cmd))
        print(f"📤 送信: {' '.join(f'{b:02X}' for b in write_cmd)}")
        print(f"💾 書き込み値: 0x{test_value:08X}")
        
        time.sleep(0.1)
        write_response = ser.read(10)
        print(f"📥 書き込み応答: {' '.join(f'{b:02X}' for b in write_response)}")
        
        # 書き込み成功かチェック
        if len(write_response) >= 3:
            sof, status = write_response[0], write_response[1]
            if sof == 0x2D and status == 0x6C:
                print("✅ 書き込み応答OK")
            else:
                print(f"❌ 書き込み応答異常: SOF=0x{sof:02X}, STATUS=0x{status:02X}")
        
        # Step 3: 書き込み後読み取り
        print("\n📖 Step 3: 書き込み後読み取り")
        time.sleep(0.1)
        ser.write(read_cmd)
        print(f"📤 送信: {' '.join(f'{b:02X}' for b in read_cmd)}")
        
        time.sleep(0.1)
        response = ser.read(10)
        print(f"📥 受信: {' '.join(f'{b:02X}' for b in response)}")
        
        if len(response) >= 7:
            read_back_value = int.from_bytes(response[3:7], byteorder='little')
            print(f"📊 読み戻し値: 0x{read_back_value:08X}")
            
            # 比較
            print(f"\n📋 結果比較:")
            print(f"   初期値:     0x{initial_value:08X}")
            print(f"   書き込み値: 0x{test_value:08X}")
            print(f"   読み戻し値: 0x{read_back_value:08X}")
            
            if read_back_value == test_value:
                print("✅ 書き込み成功 - 値が正確に反映")
            elif read_back_value == initial_value:
                print("❌ 書き込み失敗 - 初期値のまま変更なし")
            else:
                print("⚠️  予期しない値 - 部分的書き込みまたは別の問題")
                
                # ビット差分解析
                diff = read_back_value ^ test_value
                print(f"   XOR差分: 0x{diff:08X}")
        else:
            print("❌ 読み戻し失敗")
            
    except Exception as e:
        print(f"❌ エラー: {e}")
        
    finally:
        ser.close()
        print("\n🔌 切断完了")

if __name__ == "__main__":
    simple_write_test()