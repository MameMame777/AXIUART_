#!/usr/bin/env python3
"""
実測値確認スクリプト - AXIUART_ プロトコル値の詳細測定
2025-10-06 緊急解析用
"""

import serial
import time
import struct

def detailed_measurement():
    """実際の送信値の詳細測定"""
    print("🔍 AXIUART_ 実測値詳細解析")
    print("=" * 50)
    
    try:
        ser = serial.Serial("COM3", 115200, timeout=2.0)
        time.sleep(0.1)
        print("✅ UART接続成功")
        
        # 単純なレジスタ読み取りコマンド
        # READ command: SOF(0xA5) + CMD(0xA0) + ADDR(0x00001020) + CRC
        cmd_bytes = bytes([0xA5, 0xA0, 0x20, 0x10, 0x00, 0x00, 0x9F])
        
        print(f"📤 送信: {' '.join(f'{b:02X}' for b in cmd_bytes)}")
        
        ser.write(cmd_bytes)
        time.sleep(0.2)
        
        response = ser.read(20)  # 十分なバッファ
        print(f"📥 受信: {' '.join(f'{b:02X}' for b in response)}")
        print(f"📏 受信長: {len(response)} bytes")
        
        if len(response) >= 2:
            sof, status = response[0], response[1]
            
            print("\n🎯 実測プロトコル値:")
            print(f"  SOF:    0x{sof:02X}")
            print(f"  STATUS: 0x{status:02X}")
            
            print("\n🔄 Phase 1-2 予想値との比較:")
            print(f"  SOF:    実測 0x{sof:02X} vs 予想 0x6B")
            print(f"  STATUS: 実測 0x{status:02X} vs 予想 0x60")
            
            print("\n📊 作業指示書「期待値」との比較:")
            print(f"  SOF:    実測 0x{sof:02X} vs 期待 0x2D → {'✅一致' if sof == 0x2D else '❌不一致'}")
            print(f"  STATUS: 実測 0x{status:02X} vs 期待 0x6C → {'✅一致' if status == 0x6C else '❌不一致'}")
            
            # 複数回測定
            print("\n🔄 連続測定（統計確認）:")
            sof_values = [sof]
            status_values = [status]
            
            for i in range(4):
                ser.write(cmd_bytes)
                time.sleep(0.1)
                resp = ser.read(10)
                if len(resp) >= 2:
                    sof_values.append(resp[0])
                    status_values.append(resp[1])
                    print(f"  測定{i+2}: SOF=0x{resp[0]:02X}, STATUS=0x{resp[1]:02X}")
            
            print(f"\n📊 統計結果:")
            print(f"  SOF統計:    {set(sof_values)}")
            print(f"  STATUS統計: {set(status_values)}")
            print(f"  SOF一貫性:  {'✅' if len(set(sof_values)) == 1 else '❌'}")
            print(f"  STATUS一貫性: {'✅' if len(set(status_values)) == 1 else '❌'}")
        
        ser.close()
        print("\n🔌 UART接続終了")
        
    except Exception as e:
        print(f"❌ エラー: {e}")

if __name__ == "__main__":
    detailed_measurement()