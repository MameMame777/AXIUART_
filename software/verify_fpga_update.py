#!/usr/bin/env python3
"""
FPGA更新後の実測値確認
プロトコル仕様値(SOF=0x5A, STATUS=0x00)になっているかチェック
"""

import serial
import time

def verify_fpga_update():
    """FPGA更新後の実測値確認"""
    
    print("🔍 FPGA更新後の実測値確認")
    print("="*50)
    
    ser = serial.Serial('COM3', 115200, timeout=5)
    
    try:
        print("\n📡 修正後の実測値確認")
        
        # 複数回測定で安定性確認
        for attempt in range(3):
            print(f"\n🧪 測定 {attempt+1}/3:")
            
            # REG_TEST_0読み取りコマンド
            read_cmd = bytes([0xA5, 0xA0, 0x20, 0x10, 0x00, 0x00, 0x9F])
            ser.write(read_cmd)
            print(f"📤 送信: {' '.join(f'{b:02X}' for b in read_cmd)}")
            
            time.sleep(0.1)
            response = ser.read(10)
            print(f"📥 受信: {' '.join(f'{b:02X}' for b in response)} (長さ: {len(response)})")
            
            if len(response) >= 2:
                sof = response[0]
                status = response[1]
                
                print(f"   SOF: 0x{sof:02X}")
                print(f"   STATUS: 0x{status:02X}")
                
                # プロトコル仕様との比較
                print(f"   📋 プロトコル仕様比較:")
                
                if sof == 0x5A:
                    print(f"   ✅ SOF: 0x{sof:02X} = プロトコル仕様値 (0x5A)")
                elif sof == 0x2D:
                    print(f"   ❌ SOF: 0x{sof:02X} = 旧実測値 (まだ更新されていない)")
                else:
                    print(f"   ⚠️  SOF: 0x{sof:02X} = 予期しない値")
                    
                if status == 0x00:
                    print(f"   ✅ STATUS: 0x{status:02X} = プロトコル仕様値 (0x00)")
                elif status == 0x6C:
                    print(f"   ❌ STATUS: 0x{status:02X} = 旧実測値 (まだ更新されていない)")
                else:
                    print(f"   ⚠️  STATUS: 0x{status:02X} = 予期しない値")
                    
                # 修正成功判定
                if sof == 0x5A and status == 0x00:
                    print(f"   🎉 修正成功！プロトコル仕様完全準拠")
                    return True
                elif sof == 0x2D and status == 0x6C:
                    print(f"   ⏳ まだ旧値 - FPGA更新の反映待ち")
                else:
                    print(f"   ❓ 予期しない状態")
                    
            time.sleep(0.2)
            
        return False
        
    except Exception as e:
        print(f"❌ エラー: {e}")
        return False
        
    finally:
        ser.close()
        print("\n🔌 切断完了")

if __name__ == "__main__":
    success = verify_fpga_update()
    if success:
        print("\n🎊 FPGA更新成功！プロトコル仕様準拠確認完了")
    else:
        print("\n⏳ FPGA更新の完全な反映を待機中、または追加の確認が必要")