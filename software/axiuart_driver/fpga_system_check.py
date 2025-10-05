#!/usr/bin/env python3
"""
FPGA Bitstream and System Status Checker
FPGAのビットストリーム状態とシステムステータスを確認
"""

import serial
import time

def test_led_status():
    """LED状態確認（視覚的確認のガイド）"""
    print("🔍 LED状態確認ガイド")
    print("=" * 40)
    print("💡 Zybo Z7-20 の以下のLEDを確認してください：")
    print("   LD9  (POWER): 電源LED - 常時点灯していることを確認")
    print("   LD10 (DONE):  設定完了LED - ビットストリーム書き込み後に点灯")
    print("   LD11-14:      ユーザーLED - RTLで制御される場合点滅")
    print()
    
    response = input("❓ DONE LED (LD10) は点灯していますか？ (y/n): ")
    if response.lower() == 'y':
        print("✅ ビットストリーム書き込み正常")
        return True
    else:
        print("❌ ビットストリーム未書き込み、または書き込み失敗")
        print("   → Vivado Hardware Managerでプログラミングを再実行してください")
        return False

def test_basic_uart_patterns():
    """基本UART通信パターンテスト"""
    print("\n🔧 基本UART通信パターンテスト")
    print("=" * 50)
    
    port_name = "COM3"
    
    try:
        ser = serial.Serial(port_name, 115200, timeout=2.0)
        
        print("📤 様々なテストパターンを送信します...")
        
        # パターン1: シンプルなバイト
        test_patterns = [
            b'\x00',           # NULL
            b'\xFF',           # 全ビット1
            b'\x55',           # 01010101 (ビットパターン)
            b'\xAA',           # 10101010 (逆ビットパターン)
            b'\xA5',           # SOF マーカー (0xA5)
            b'\x5A',           # SOF マーカー (0x5A)
        ]
        
        for i, pattern in enumerate(test_patterns, 1):
            print(f"   パターン{i}: {pattern.hex().upper()}")
            ser.write(pattern)
            ser.flush()
            time.sleep(0.5)
            
            # 応答チェック
            if ser.in_waiting > 0:
                received = ser.read(ser.in_waiting)
                print(f"      → 応答: {received.hex().upper()}")
            else:
                print(f"      → 応答: なし")
        
        # パターン2: より長いシーケンス
        print("\n📡 長いシーケンステスト:")
        long_pattern = b'\xA5\x01\x02\x03\x04\x53\x5A'  # SOF + データ + CRC + SOF
        print(f"   送信: {long_pattern.hex().upper()}")
        ser.write(long_pattern)
        ser.flush()
        time.sleep(1.0)
        
        if ser.in_waiting > 0:
            received = ser.read(ser.in_waiting)
            print(f"   受信: {received.hex().upper()}")
        else:
            print(f"   受信: なし")
            
        ser.close()
        
    except Exception as e:
        print(f"❌ エラー: {e}")

def check_system_reset():
    """システムリセット確認"""
    print("\n🔄 システムリセット確認")
    print("=" * 40)
    print("📋 確認項目:")
    print("   1. リセットボタン（BTN0）が押されていないこと")
    print("   2. 制約ファイルでリセット信号が正しく定義されていること")
    print("   3. RTLでリセットが適切に処理されていること")
    
    response = input("❓ リセットボタンは解除状態ですか？ (y/n): ")
    if response.lower() == 'y':
        print("✅ リセット状態正常")
        return True
    else:
        print("❌ リセットボタンを確認してください")
        return False

def main():
    """メイン診断フロー"""
    print("🏥 FPGA システム診断ツール")
    print("=" * 60)
    print(f"実行時刻: {time.strftime('%Y-%m-%d %H:%M:%S')}")
    print()
    
    # Step 1: LED状態確認
    led_ok = test_led_status()
    
    # Step 2: リセット確認
    reset_ok = check_system_reset()
    
    # Step 3: 基本UART通信テスト
    if led_ok and reset_ok:
        test_basic_uart_patterns()
    else:
        print("\n⚠️  基本的な問題が解決されるまでUARTテストをスキップします")
    
    # 診断結果サマリー
    print("\n" + "=" * 60)
    print("📋 診断結果サマリー:")
    print(f"   ビットストリーム: {'✅ OK' if led_ok else '❌ NG'}")
    print(f"   リセット状態:     {'✅ OK' if reset_ok else '❌ NG'}")
    
    if led_ok and reset_ok:
        print("   UART通信:         上記テスト結果を参照")
        print("\n💡 次のステップ:")
        print("   - 応答がある場合: プロトコル層の問題")
        print("   - 応答がない場合: RTL内部の問題（クロック、初期化など）")
    else:
        print("\n🔧 推奨アクション:")
        if not led_ok:
            print("   1. Vivado Hardware Managerでビットストリームを再書き込み")
        if not reset_ok:
            print("   2. リセットボタン（BTN0）を確認")

if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\n\n⏹️  診断が中断されました")
    except Exception as e:
        print(f"\n❌ 予期しないエラー: {e}")
        import traceback
        traceback.print_exc()