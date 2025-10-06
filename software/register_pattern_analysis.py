#!/usr/bin/env python3
"""
レジスタ書き込み問題の詳細分析
初期値と実測値の関係を調査
"""

import serial
import time

def analyze_register_pattern():
    """レジスタ値パターンの詳細分析"""
    
    ser = serial.Serial('COM3', 115200, timeout=5)
    print("🔍 レジスタ書き込み問題の詳細分析")
    print("="*50)
    
    # RTL初期値 (Register_Block.svより)
    rtl_initial_values = {
        0x1020: 0xDEADBEEF,  # test_reg_0
        0x1024: 0x12345678,  # test_reg_1  
        0x1028: 0xABCDEF00,  # test_reg_2
        0x102C: 0x00000000,  # test_reg_3
    }
    
    try:
        print("\n📊 各レジスタの期待値 vs 実測値")
        
        for addr in [0x1020, 0x1024, 0x1028, 0x102C]:
            # 読み取りコマンド作成
            read_cmd = [0xA5, 0xA0, addr & 0xFF, (addr >> 8) & 0xFF, 
                       (addr >> 16) & 0xFF, (addr >> 24) & 0xFF]
            
            # CRC計算 (簡単なチェックサム)
            crc = sum(read_cmd) & 0xFF
            read_cmd.append(crc)
            
            print(f"\n📍 アドレス 0x{addr:08X}")
            print(f"   RTL初期値: 0x{rtl_initial_values[addr]:08X}")
            
            # 送信
            ser.write(bytes(read_cmd))
            print(f"   📤 送信: {' '.join(f'{b:02X}' for b in read_cmd)}")
            
            # 応答受信
            time.sleep(0.1)
            response = ser.read(10)
            print(f"   📥 受信: {' '.join(f'{b:02X}' for b in response)}")
            
            if len(response) >= 7:
                # データ部抽出
                data_bytes = response[3:7]
                data_value = int.from_bytes(data_bytes, byteorder='little')
                print(f"   実測値: 0x{data_value:08X}")
                
                # 差分分析
                expected = rtl_initial_values[addr]
                if data_value == expected:
                    print("   ✅ RTL初期値と一致")
                else:
                    print(f"   ❌ RTL初期値と不一致")
                    # ビット別比較
                    diff = data_value ^ expected
                    print(f"   XOR差分: 0x{diff:08X}")
                    
                    # バイト別比較
                    for i in range(4):
                        exp_byte = (expected >> (i*8)) & 0xFF
                        act_byte = (data_value >> (i*8)) & 0xFF
                        if exp_byte != act_byte:
                            print(f"   バイト{i}: 期待 0x{exp_byte:02X} → 実測 0x{act_byte:02X}")
            
            time.sleep(0.2)
            
    except Exception as e:
        print(f"❌ エラー: {e}")
        
    finally:
        ser.close()
        print("\n🔌 切断完了")

if __name__ == "__main__":
    analyze_register_pattern()