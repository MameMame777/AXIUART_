#!/usr/bin/env python3
"""
補正マスク削除前のベースライン測定
プロトコル仕様値(SOF=0x5A, STATUS=0x00)でテストスクリプトを更新
"""

import serial
import time

def baseline_before_fix():
    """修正前のベースライン測定"""
    
    print("📊 補正マスク削除前のベースライン測定")
    print("="*50)
    
    ser = serial.Serial('COM3', 115200, timeout=5)
    
    try:
        # 現在の実測値確認
        print("\n🔍 現在の実測値 (補正マスクあり)")
        read_cmd = bytes([0xA5, 0xA0, 0x20, 0x10, 0x00, 0x00, 0x9F])
        ser.write(read_cmd)
        time.sleep(0.1)
        response = ser.read(10)
        
        if len(response) >= 2:
            sof = response[0]
            status = response[1]
            print(f"   SOF: 0x{sof:02X}")
            print(f"   STATUS: 0x{status:02X}")
            
            # プロトコル仕様との比較
            print(f"\n📋 プロトコル仕様との比較:")
            print(f"   プロトコル仕様: SOF=0x5A, STATUS=0x00")
            print(f"   現在の実測値:   SOF=0x{sof:02X}, STATUS=0x{status:02X}")
            
            if sof == 0x5A:
                print("   ✅ SOF: プロトコル仕様と一致")
            else:
                print("   ❌ SOF: プロトコル仕様と不一致")
                
            if status == 0x00:
                print("   ✅ STATUS: プロトコル仕様と一致") 
            else:
                print("   ❌ STATUS: プロトコル仕様と不一致")
                
        print(f"\n💡 修正後の期待値:")
        print(f"   Frame_Builder修正により:")
        print(f"   SOF: 0x{sof:02X} → 0x5A (プロトコル仕様値)")
        print(f"   STATUS: 0x{status:02X} → 0x00 (プロトコル仕様値)")
        
    except Exception as e:
        print(f"❌ エラー: {e}")
        
    finally:
        ser.close()
        print("\n🔌 切断完了")

if __name__ == "__main__":
    baseline_before_fix()