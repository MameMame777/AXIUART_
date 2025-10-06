#!/usr/bin/env python3
"""
シリアル通信リセット & 通信状態復旧
"""

import serial
import time

def reset_communication():
    """シリアル通信のリセットと状態確認"""
    
    print("🔄 シリアル通信リセット & 復旧")
    print("="*40)
    
    try:
        # 接続をリセット
        print("📡 シリアル接続をリセット中...")
        ser = serial.Serial('COM3', 115200, timeout=5)
        
        # DTR/RTSリセット
        ser.setDTR(False)
        ser.setRTS(False)
        time.sleep(0.1)
        ser.setDTR(True)
        ser.setRTS(True)
        time.sleep(0.1)
        
        # バッファクリア
        ser.reset_input_buffer()
        ser.reset_output_buffer()
        time.sleep(0.2)
        
        print("✅ シリアル接続リセット完了")
        
        # 通信テスト (簡単なコマンド)
        print("\n🧪 通信状態確認テスト")
        
        for attempt in range(3):
            print(f"\n📡 テスト {attempt+1}: REG_TEST_0 読み取り")
            
            # REG_TEST_0読み取りコマンド
            read_cmd = bytes([0xA5, 0xA0, 0x20, 0x10, 0x00, 0x00, 0x9F])
            
            # 送信
            ser.write(read_cmd)
            print(f"📤 送信: {' '.join(f'{b:02X}' for b in read_cmd)}")
            
            # 応答受信
            time.sleep(0.1)
            response = ser.read(10)
            print(f"📥 受信: {' '.join(f'{b:02X}' for b in response)} (長さ: {len(response)})")
            
            if len(response) >= 2:
                sof = response[0]
                status = response[1]
                print(f"   SOF: 0x{sof:02X}, STATUS: 0x{status:02X}")
                
                # 正常なSOFかチェック
                if sof == 0x2D:
                    print("   ✅ SOF正常 (0x2D)")
                else:
                    print(f"   ❌ SOF異常 (期待: 0x2D, 実際: 0x{sof:02X})")
                    
                # 正常なSTATUSかチェック
                if status == 0x6C:
                    print("   ✅ STATUS正常 (0x6C)")
                else:
                    print(f"   ⚠️  STATUS: 0x{status:02X}")
                    
                # 両方正常なら成功
                if sof == 0x2D and status == 0x6C:
                    print("   🎉 通信正常復旧！")
                    break
            
            time.sleep(0.5)
        else:
            print("   ❌ 通信復旧失敗")
            
    except Exception as e:
        print(f"❌ エラー: {e}")
        
    finally:
        try:
            ser.close()
            print("\n🔌 切断完了")
        except:
            pass

if __name__ == "__main__":
    reset_communication()