#!/usr/bin/env python3
"""
書き込みフロー詳細デバッグ
各段階でのレスポンス分析
"""

import serial
import time

def debug_write_flow():
    """書き込みフローの詳細デバッグ"""
    
    print("🔍 書き込みフロー詳細デバッグ")
    print("="*50)
    
    ser = serial.Serial('COM3', 115200, timeout=5)
    
    try:
        # Step 1: 初期状態確認
        print("\n📍 Step 1: 初期状態確認")
        read_cmd = bytes([0xA5, 0xA0, 0x20, 0x10, 0x00, 0x00, 0x9F])
        ser.write(read_cmd)
        time.sleep(0.1)
        response = ser.read(10)
        
        if len(response) >= 7:
            initial_value = int.from_bytes(response[3:7], byteorder='little')
            print(f"✅ 初期値: 0x{initial_value:08X}")
        else:
            print("❌ 初期値読み取り失敗")
            return
            
        # Step 2: 書き込み実行と詳細応答解析
        print("\n✏️  Step 2: 書き込み実行と詳細応答解析")
        test_value = 0x12345678
        write_cmd = [0xA5, 0x20, 0x20, 0x10, 0x00, 0x00,
                     test_value & 0xFF, (test_value >> 8) & 0xFF,
                     (test_value >> 16) & 0xFF, (test_value >> 24) & 0xFF]
        
        crc = sum(write_cmd) & 0xFF
        write_cmd.append(crc)
        
        # バッファクリア
        ser.reset_input_buffer()
        
        # 書き込み実行
        ser.write(bytes(write_cmd))
        print(f"📤 書き込みコマンド: {' '.join(f'{b:02X}' for b in write_cmd)}")
        print(f"💾 書き込み値: 0x{test_value:08X}")
        
        # 応答解析 (長時間待機)
        time.sleep(0.2)
        write_response = ser.read(20)  # より多くのバイトを読み取り
        print(f"📥 書き込み応答: {' '.join(f'{b:02X}' for b in write_response)} (長さ: {len(write_response)})")
        
        if len(write_response) >= 3:
            sof = write_response[0]
            status = write_response[1] 
            cmd_echo = write_response[2]
            
            print(f"   SOF: 0x{sof:02X} ({'OK' if sof == 0x2D else 'ERROR'})")
            print(f"   STATUS: 0x{status:02X} ({'OK' if status == 0x6C else 'ERROR'})")
            print(f"   CMD_ECHO: 0x{cmd_echo:02X}")
            
            # 書き込み応答コマンドの確認
            expected_cmd_echo = 0x20 ^ 0x19  # CMD correction mask
            print(f"   期待CMD_ECHO: 0x{expected_cmd_echo:02X}")
            
        # Step 3: 即座読み戻し
        print("\n📖 Step 3: 即座読み戻し")
        time.sleep(0.1)
        ser.write(read_cmd)
        time.sleep(0.1)
        read_response = ser.read(10)
        
        if len(read_response) >= 7:
            read_value = int.from_bytes(read_response[3:7], byteorder='little')
            print(f"📊 即座読み戻し値: 0x{read_value:08X}")
            
            if read_value == test_value:
                print("✅ 書き込み成功!")
            elif read_value == initial_value:
                print("❌ 書き込み失敗 - 初期値のまま")
            else:
                print("⚠️  部分的変更または別の問題")
                
        # Step 4: 再度読み戻し (遅延確認)
        print("\n📖 Step 4: 遅延後読み戻し")
        time.sleep(0.5)
        ser.write(read_cmd)
        time.sleep(0.1)
        read_response2 = ser.read(10)
        
        if len(read_response2) >= 7:
            read_value2 = int.from_bytes(read_response2[3:7], byteorder='little')
            print(f"📊 遅延後読み戻し値: 0x{read_value2:08X}")
            
            if read_value != read_value2:
                print("⚠️  値が時間で変化している")
            else:
                print("✅ 値は安定")
                
    except Exception as e:
        print(f"❌ エラー: {e}")
        
    finally:
        ser.close()
        print("\n🔌 切断完了")

if __name__ == "__main__":
    debug_write_flow()