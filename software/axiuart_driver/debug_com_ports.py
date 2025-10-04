#!/usr/bin/env python3
"""
COM Port Debug Tool
利用可能なCOMポートの詳細情報を表示し、接続問題をデバッグするツール
"""

import serial
import serial.tools.list_ports
import sys
import time

def scan_all_ports():
    """全COMポートをスキャンして詳細情報を表示"""
    print("🔍 COMポートスキャン")
    print("=" * 50)
    
    ports = serial.tools.list_ports.comports()
    
    if not ports:
        print("❌ COMポートが見つかりません")
        return []
    
    available_ports = []
    
    for port in ports:
        print(f"\n📡 ポート: {port.device}")
        print(f"   説明: {port.description}")
        print(f"   ハードウェアID: {port.hwid}")
        print(f"   製造者: {port.manufacturer}")
        print(f"   製品ID: {port.pid}")
        print(f"   ベンダーID: {port.vid}")
        print(f"   シリアル番号: {port.serial_number}")
        
        # 接続テスト
        try:
            ser = serial.Serial(port.device, baudrate=115200, timeout=0.5)
            ser.close()
            print(f"   ステータス: ✅ 利用可能")
            available_ports.append(port.device)
        except serial.SerialException as e:
            print(f"   ステータス: ❌ 使用中またはエラー ({e})")
        except Exception as e:
            print(f"   ステータス: ❌ 不明なエラー ({e})")
    
    return available_ports

def test_specific_port(port_name):
    """特定のポートの詳細テスト"""
    print(f"\n🔧 詳細テスト: {port_name}")
    print("-" * 30)
    
    try:
        # 基本接続テスト
        print("1. 基本接続テスト...")
        ser = serial.Serial()
        ser.port = port_name
        ser.baudrate = 115200
        ser.timeout = 1
        ser.rtscts = False
        ser.dsrdtr = False
        
        ser.open()
        print(f"   ✅ ポート開放成功")
        print(f"   ポート名: {ser.name}")
        print(f"   ボーレート: {ser.baudrate}")
        print(f"   タイムアウト: {ser.timeout}")
        
        # 信号状態確認
        print("\n2. 信号状態確認...")
        print(f"   CTS: {ser.cts}")
        print(f"   DSR: {ser.dsr}")
        print(f"   RI: {ser.ri}")
        print(f"   CD: {ser.cd}")
        
        # バッファ状態
        print(f"   受信バッファ: {ser.in_waiting} bytes")
        print(f"   送信バッファ: {ser.out_waiting} bytes")
        
        # 簡単な送信テスト
        print("\n3. 送信テスト...")
        test_data = b'\x01\x02\x03'
        sent = ser.write(test_data)
        ser.flush()
        print(f"   送信バイト数: {sent}")
        
        # 短時間の受信待機
        print("\n4. 受信テスト...")
        time.sleep(0.1)
        if ser.in_waiting > 0:
            received = ser.read(ser.in_waiting)
            print(f"   受信データ: {received.hex()}")
        else:
            print("   受信データなし")
        
        ser.close()
        print("   ✅ テスト完了")
        return True
        
    except Exception as e:
        print(f"   ❌ エラー: {e}")
        return False

def main():
    """メイン関数"""
    print("🛠️  AXIUART COMポートデバッグツール")
    print("=" * 60)
    print(f"実行時刻: {time.strftime('%Y-%m-%d %H:%M:%S')}")
    
    # 全ポートスキャン
    available_ports = scan_all_ports()
    
    print(f"\n📋 スキャン結果サマリー")
    print("-" * 30)
    print(f"利用可能ポート: {available_ports}")
    
    # COM3が利用可能かチェック
    if "COM3" in available_ports:
        print("\n✅ COM3が利用可能です")
        test_specific_port("COM3")
    else:
        print("\n❌ COM3が利用できません")
        
        # 代替ポートの提案
        if available_ports:
            print(f"💡 利用可能な代替ポート: {available_ports}")
            
            # 最初の利用可能ポートをテスト
            if len(available_ports) > 0:
                print(f"\n🧪 代替ポート {available_ports[0]} をテストします...")
                test_specific_port(available_ports[0])
    
    print("\n✨ デバッグ完了")

if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\n\n⏹️  ユーザーによりデバッグが中断されました")
    except Exception as e:
        print(f"\n❌ 予期しないエラー: {e}")
        import traceback
        traceback.print_exc()