#!/usr/bin/env python3
"""
Simple Echo Test Tool
シンプルなエコーテストでFPGAとの基本通信を確認
"""

import serial
import time

def test_echo_patterns(port_name="COM3"):
    """シンプルなエコーパターンテスト"""
    print(f"🔄 Echo Test - {port_name}")
    print("=" * 40)
    
    try:
        ser = serial.Serial(
            port=port_name,
            baudrate=115200,
            timeout=1.0,
            rtscts=False,
            dsrdtr=False
        )
        
        print("✅ ポート開放成功")
        
        # シンプルなパターンテスト
        test_patterns = [
            b'\x00',           # NULL
            b'\xFF',           # All 1s
            b'\xAA',           # 10101010
            b'\x55',           # 01010101
            b'\x01\x02\x03',  # Sequential
            b'Hello',          # ASCII
            b'\xA5\x5A',      # SOF patterns
        ]
        
        for i, pattern in enumerate(test_patterns):
            print(f"\n🧪 テスト {i+1}: {pattern.hex().upper()}")
            
            # バッファクリア
            ser.reset_input_buffer()
            ser.reset_output_buffer()
            
            # 送信
            ser.write(pattern)
            ser.flush()
            print(f"   送信: {pattern.hex().upper()}")
            
            # 受信待機
            time.sleep(0.1)  # 100ms待機
            
            if ser.in_waiting > 0:
                received = ser.read(ser.in_waiting)
                print(f"   受信: {received.hex().upper()}")
                
                if received == pattern:
                    print("   ✅ エコー一致")
                else:
                    print("   ⚠️  エコー不一致")
            else:
                print("   ❌ 応答なし")
            
            time.sleep(0.2)  # 次のテストまで200ms待機
        
        ser.close()
        print("\n✅ テスト完了")
        
    except Exception as e:
        print(f"❌ エラー: {e}")

def test_different_baudrates(port_name="COM3"):
    """異なるボーレートでテスト"""
    print(f"\n📡 ボーレートテスト - {port_name}")
    print("=" * 40)
    
    baudrates = [9600, 19200, 38400, 57600, 115200, 230400]
    test_data = b'\xA5\x5A\x01\x02'
    
    for baudrate in baudrates:
        print(f"\n⚡ ボーレート: {baudrate}")
        
        try:
            ser = serial.Serial(
                port=port_name,
                baudrate=baudrate,
                timeout=0.5,
                rtscts=False,
                dsrdtr=False
            )
            
            # バッファクリア
            ser.reset_input_buffer()
            ser.reset_output_buffer()
            
            # 送信
            ser.write(test_data)
            ser.flush()
            
            # 受信待機
            time.sleep(0.1)
            
            if ser.in_waiting > 0:
                received = ser.read(ser.in_waiting)
                print(f"   送信: {test_data.hex().upper()}")
                print(f"   受信: {received.hex().upper()}")
                
                if received == test_data:
                    print("   ✅ エコー成功")
                else:
                    print("   ⚠️  部分受信または変化あり")
            else:
                print("   ❌ 応答なし")
            
            ser.close()
            
        except Exception as e:
            print(f"   ❌ エラー: {e}")
        
        time.sleep(0.1)

def test_loopback_simple():
    """最もシンプルなループバックテスト"""
    print(f"\n🔄 シンプルループバックテスト")
    print("=" * 40)
    
    try:
        ser = serial.Serial("COM3", 115200, timeout=2.0)
        
        # 単一バイトテスト
        for test_byte in [0x00, 0x55, 0xAA, 0xFF]:
            ser.reset_input_buffer()
            ser.reset_output_buffer()
            
            # 送信
            data = bytes([test_byte])
            ser.write(data)
            ser.flush()
            
            print(f"送信: 0x{test_byte:02X}")
            
            # 受信
            start_time = time.time()
            received_data = b""
            
            while time.time() - start_time < 1.0:
                if ser.in_waiting > 0:
                    new_data = ser.read(ser.in_waiting)
                    received_data += new_data
                    break
                time.sleep(0.01)
            
            if received_data:
                print(f"受信: {received_data.hex().upper()}")
            else:
                print("受信: なし")
            
            time.sleep(0.1)
        
        ser.close()
        
    except Exception as e:
        print(f"❌ エラー: {e}")

def main():
    """メイン関数"""
    print("🧪 FPGA基本通信デバッグツール")
    print("=" * 60)
    print(f"実行時刻: {time.strftime('%Y-%m-%d %H:%M:%S')}")
    
    # 1. シンプルなループバックテスト
    test_loopback_simple()
    
    # 2. 複数パターンのエコーテスト
    test_echo_patterns("COM3")
    
    # 3. 異なるボーレートでのテスト
    test_different_baudrates("COM3")
    
    print("\n" + "=" * 60)
    print("💡 診断のポイント:")
    print("   - 応答がない → FPGAの電源・リセット・ファームウェア確認")
    print("   - 部分応答  → ボーレート・フロー制御設定確認")
    print("   - エラー応答 → プロトコル・フレーム形式確認")
    print("   - エコー成功 → FPGA基本動作OK、プロトコル層の問題")
    
    print("\n✨ デバッグ完了")

if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\n\n⏹️  ユーザーによりテストが中断されました")
    except Exception as e:
        print(f"\n❌ 予期しないエラー: {e}")
        import traceback
        traceback.print_exc()