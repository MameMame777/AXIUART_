#!/usr/bin/env python3
"""
FPGA通信リセット後の再確認
ハードウェアリセット・再接続で状態をクリア
"""

import serial
import time

def reset_and_recheck():
    """FPGA通信リセット後の再確認"""
    
    print("🔄 FPGA通信リセット後の再確認")
    print("="*50)
    
    print("\n⏳ 通信リセット実行中...")
    
    try:
        # 長めの待機でFPGAの状態を安定化
        time.sleep(1.0)
        
        ser = serial.Serial('COM3', 115200, timeout=5)
        
        # DTR/RTS制御でハードウェアリセット
        ser.setDTR(False)
        ser.setRTS(False)
        time.sleep(0.2)
        ser.setDTR(True) 
        ser.setRTS(True)
        time.sleep(0.5)
        
        # バッファクリア
        ser.reset_input_buffer()
        ser.reset_output_buffer()
        time.sleep(0.3)
        
        print("✅ 通信リセット完了")
        
        # リセット後の測定
        print("\n🔍 リセット後の実測値確認")
        
        for attempt in range(2):
            print(f"\n📡 測定 {attempt+1}/2:")
            
            read_cmd = bytes([0xA5, 0xA0, 0x20, 0x10, 0x00, 0x00, 0x9F])
            ser.write(read_cmd)
            print(f"📤 送信: {' '.join(f'{b:02X}' for b in read_cmd)}")
            
            time.sleep(0.15)
            response = ser.read(10)
            print(f"📥 受信: {' '.join(f'{b:02X}' for b in response)}")
            
            if len(response) >= 2:
                sof = response[0]
                status = response[1]
                
                print(f"   SOF: 0x{sof:02X}, STATUS: 0x{status:02X}")
                
                if sof == 0x5A and status == 0x00:
                    print("   🎉 修正成功！プロトコル仕様値確認")
                    return True
                elif sof == 0x2D and status == 0x6C:
                    print("   ⚠️  まだ旧値")
                else:
                    print(f"   ❓ 予期しない値: SOF=0x{sof:02X}, STATUS=0x{status:02X}")
                    
            time.sleep(0.3)
            
        return False
        
    except Exception as e:
        print(f"❌ エラー: {e}")
        return False
        
    finally:
        try:
            ser.close()
        except:
            pass
        print("\n🔌 切断完了")

if __name__ == "__main__":
    success = reset_and_recheck()
    if success:
        print("\n🎊 FPGA更新・リセット成功！")
    else:
        print("\n🤔 追加の調査が必要です")