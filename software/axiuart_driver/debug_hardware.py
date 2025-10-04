#!/usr/bin/env python3
"""
Hardware Level Debug Tool
ハードウェアレベルでの信号状態とシリアル通信を詳細デバッグ
"""

import serial
import time

def test_hardware_signals(port_name="COM3"):
    """ハードウェア信号レベルテスト"""
    print(f"📡 ハードウェア信号テスト - {port_name}")
    print("=" * 50)
    
    try:
        ser = serial.Serial(port_name, 115200, timeout=1.0)
        
        print("✅ ポート開放成功")
        
        # 初期信号状態
        print("\n📋 初期信号状態:")
        print(f"   CTS (Clear To Send): {ser.cts}")
        print(f"   DSR (Data Set Ready): {ser.dsr}")
        print(f"   RI (Ring Indicator): {ser.ri}")
        print(f"   CD (Carrier Detect): {ser.cd}")
        
        # DTRとRTSを操作してみる
        print("\n🔧 制御信号操作テスト:")
        
        # DTR操作
        print("   DTR = False")
        ser.dtr = False
        time.sleep(0.1)
        print(f"      DSR: {ser.dsr}, CTS: {ser.cts}")
        
        print("   DTR = True")
        ser.dtr = True
        time.sleep(0.1)
        print(f"      DSR: {ser.dsr}, CTS: {ser.cts}")
        
        # RTS操作
        print("   RTS = False")
        ser.rts = False
        time.sleep(0.1)
        print(f"      DSR: {ser.dsr}, CTS: {ser.cts}")
        
        print("   RTS = True")
        ser.rts = True
        time.sleep(0.1)
        print(f"      DSR: {ser.dsr}, CTS: {ser.cts}")
        
        # フロー制御有効でテスト
        print("\n🔄 フロー制御有効テスト:")
        ser.close()
        
        ser = serial.Serial(
            port=port_name,
            baudrate=115200,
            timeout=1.0,
            rtscts=True,  # フロー制御有効
            dsrdtr=False
        )
        
        print("   RTS/CTS フロー制御有効で再接続")
        print(f"   CTS: {ser.cts}, DSR: {ser.dsr}")
        
        # テストデータ送信
        test_data = b'\x01\x02\x03\x04'
        print(f"   テストデータ送信: {test_data.hex().upper()}")
        ser.write(test_data)
        ser.flush()
        
        time.sleep(0.1)
        if ser.in_waiting > 0:
            received = ser.read(ser.in_waiting)
            print(f"   受信データ: {received.hex().upper()}")
        else:
            print("   受信データ: なし")
        
        ser.close()
        
    except Exception as e:
        print(f"❌ エラー: {e}")

def test_break_signal(port_name="COM3"):
    """ブレーク信号テスト"""
    print(f"\n⚡ ブレーク信号テスト - {port_name}")
    print("=" * 40)
    
    try:
        ser = serial.Serial(port_name, 115200, timeout=1.0)
        
        print("📤 ブレーク信号送信前")
        print(f"   受信バッファ: {ser.in_waiting} bytes")
        
        # ブレーク信号送信
        print("⚡ ブレーク信号送信中...")
        ser.send_break(duration=0.1)  # 100ms
        
        time.sleep(0.2)
        print("📥 ブレーク信号送信後")
        print(f"   受信バッファ: {ser.in_waiting} bytes")
        
        if ser.in_waiting > 0:
            received = ser.read(ser.in_waiting)
            print(f"   受信データ: {received.hex().upper()}")
        
        ser.close()
        
    except Exception as e:
        print(f"❌ エラー: {e}")

def test_continuous_monitoring(port_name="COM3", duration=5):
    """継続監視テスト"""
    print(f"\n👁️  継続監視テスト - {port_name} ({duration}秒)")
    print("=" * 50)
    
    try:
        ser = serial.Serial(port_name, 115200, timeout=0.1)
        
        print("🔍 監視開始...")
        print("   何かデータが受信されたら表示します")
        print("   （FPGAからの自発的な送信をチェック）")
        
        start_time = time.time()
        last_signal_check = start_time
        
        while time.time() - start_time < duration:
            # データ受信チェック
            if ser.in_waiting > 0:
                received = ser.read(ser.in_waiting)
                timestamp = time.strftime('%H:%M:%S')
                print(f"   [{timestamp}] 受信: {received.hex().upper()}")
            
            # 1秒ごとに信号状態チェック
            if time.time() - last_signal_check >= 1.0:
                print(f"   [{time.strftime('%H:%M:%S')}] 信号: CTS={ser.cts}, DSR={ser.dsr}")
                last_signal_check = time.time()
            
            time.sleep(0.01)  # 10ms間隔
        
        print("✅ 監視完了")
        ser.close()
        
    except Exception as e:
        print(f"❌ エラー: {e}")

def test_port_properties(port_name="COM3"):
    """ポート詳細プロパティテスト"""
    print(f"\n🔧 ポート詳細プロパティ - {port_name}")
    print("=" * 40)
    
    try:
        ser = serial.Serial(port_name, 115200, timeout=1.0)
        
        print("📋 ポート設定:")
        print(f"   ポート名: {ser.name}")
        print(f"   ボーレート: {ser.baudrate}")
        print(f"   データビット: {ser.bytesize}")
        print(f"   パリティ: {ser.parity}")
        print(f"   ストップビット: {ser.stopbits}")
        print(f"   タイムアウト: {ser.timeout}")
        print(f"   RTS/CTS: {ser.rtscts}")
        print(f"   XON/XOFF: {ser.xonxoff}")
        print(f"   DSR/DTR: {ser.dsrdtr}")
        
        print("\n📡 現在の信号状態:")
        print(f"   RTS: {ser.rts}")
        print(f"   DTR: {ser.dtr}")
        print(f"   CTS: {ser.cts}")
        print(f"   DSR: {ser.dsr}")
        print(f"   RI: {ser.ri}")
        print(f"   CD: {ser.cd}")
        
        print(f"\n📊 バッファ状態:")
        print(f"   受信バッファ: {ser.in_waiting} bytes")
        print(f"   送信バッファ: {ser.out_waiting} bytes")
        
        ser.close()
        
    except Exception as e:
        print(f"❌ エラー: {e}")

def main():
    """メイン関数"""
    print("🔬 FPGA ハードウェアレベルデバッグツール")
    print("=" * 70)
    print(f"実行時刻: {time.strftime('%Y-%m-%d %H:%M:%S')}")
    print()
    print("💡 目的: FPGAが全く応答しない原因を特定")
    print("   - ハードウェア信号レベルの確認")
    print("   - 制御信号の動作確認")
    print("   - 自発的な送信データの監視")
    
    # 1. ポート詳細プロパティ確認
    test_port_properties("COM3")
    
    # 2. ハードウェア信号テスト
    test_hardware_signals("COM3")
    
    # 3. ブレーク信号テスト
    test_break_signal("COM3")
    
    # 4. 継続監視テスト（5秒間）
    test_continuous_monitoring("COM3", 5)
    
    print("\n" + "=" * 70)
    print("🎯 診断結果の解釈:")
    print("   📶 信号変化あり → ハードウェア接続OK、FPGA未応答")
    print("   📡 自発送信あり → FPGA動作中、プロトコル不一致")
    print("   🔇 完全無応答  → FPGA停止、電源・クロック・リセット確認")
    print("   ⚡ ブレーク応答 → UART機能有効、プロトコル層問題")
    
    print("\n✨ ハードウェアデバッグ完了")

if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\n\n⏹️  ユーザーによりテストが中断されました")
    except Exception as e:
        print(f"\n❌ 予期しないエラー: {e}")
        import traceback
        traceback.print_exc()