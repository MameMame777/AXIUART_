"""
AXIUART Driver - SOFタイムアウト デバッグツール

SOF (Start of Frame) タイムアウトエラーの原因分析とデバッグ
"""

import sys
import os
import time
import threading

# Add current directory to path for module imports
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from core import COMManager, UARTProtocol, RegisterMap


def analyze_sof_timeout():
    """SOFタイムアウトエラーの詳細分析"""
    print("🔍 SOFタイムアウト エラー分析")
    print("=" * 50)
    
    # 1. 考えられる原因
    print("🚨 SOFタイムアウトの考えられる原因:")
    print("1. FPGA側UARTモジュールが動作していない")
    print("2. ボーレート不一致 (PC: 115200 vs FPGA: 別の値)")
    print("3. FPGA側がコマンドを認識していない")
    print("4. フロー制御(RTS/CTS)の問題")
    print("5. UARTプロトコルのフレーム形式不一致")
    print("6. FPGAクロックやリセット問題")
    print()


def test_raw_uart_communication():
    """ローレベルUART通信テスト"""
    print("📡 ローレベル UART通信テスト")
    print("-" * 30)
    
    try:
        com_manager = COMManager()
        
        # 異なるボーレートでの接続テスト
        baudrates = [115200, 57600, 38400, 19200, 9600]
        
        for baudrate in baudrates:
            print(f"\n🔄 ボーレート {baudrate} での接続テスト...")
            
            try:
                # 接続
                success = com_manager.connect("COM3", baudrate, timeout=1.0, flow_control=False)
                if not success:
                    print(f"   ❌ {baudrate} bps: 接続失敗")
                    continue
                
                print(f"   ✅ {baudrate} bps: 接続成功")
                
                # 生データ送信テスト
                test_data = b'\x7E\x01\x00\x10\x00\x04\x00\x00\x00\x32\x7F'  # VERSION読み取りコマンド例
                print(f"   📤 送信: {test_data.hex().upper()}")
                
                bytes_sent = com_manager.write_data(test_data)
                print(f"   📊 送信バイト数: {bytes_sent}")
                
                # 応答待機
                time.sleep(0.5)  # 500ms待機
                
                received_data = com_manager.read_data(1024, timeout=0.5)
                if received_data:
                    print(f"   📥 受信: {received_data.hex().upper()}")
                    print(f"   📊 受信バイト数: {len(received_data)}")
                else:
                    print("   ⚠️  応答なし (タイムアウト)")
                
                com_manager.disconnect()
                
            except Exception as e:
                print(f"   ❌ {baudrate} bps: エラー - {e}")
                try:
                    com_manager.disconnect()
                except:
                    pass
    
    except Exception as e:
        print(f"❌ ローレベルテストエラー: {e}")


def test_uart_loopback():
    """UARTループバックテスト（可能な場合）"""
    print("\n🔄 UARTループバックテスト")
    print("-" * 30)
    
    try:
        com_manager = COMManager()
        
        # 接続
        if not com_manager.connect("COM3", 115200, timeout=0.5):
            print("❌ 接続失敗")
            return
        
        # シンプルなバイト送信
        test_bytes = [0x55, 0xAA, 0xFF, 0x00]  # テストパターン
        
        for test_byte in test_bytes:
            print(f"\n📤 送信: 0x{test_byte:02X}")
            
            # 1バイト送信
            com_manager.write_data(bytes([test_byte]))
            
            # 短時間待機
            time.sleep(0.1)
            
            # 受信確認
            received = com_manager.read_data(10, timeout=0.2)
            if received:
                print(f"📥 受信: {received.hex().upper()}")
            else:
                print("⚠️  応答なし")
        
        com_manager.disconnect()
        
    except Exception as e:
        print(f"❌ ループバックテストエラー: {e}")


def test_different_timeouts():
    """異なるタイムアウト値でのテスト"""
    print("\n⏱️  タイムアウト値調整テスト")
    print("-" * 30)
    
    timeouts = [0.1, 0.5, 1.0, 2.0, 5.0]  # 100ms - 5秒
    
    for timeout in timeouts:
        print(f"\n🕐 タイムアウト: {timeout}秒")
        
        try:
            com_manager = COMManager()
            
            # 長めのタイムアウトで接続
            if not com_manager.connect("COM3", 115200, timeout=timeout):
                print("   ❌ 接続失敗")
                continue
            
            # UARTプロトコルでVERSION読み取り試行
            uart_protocol = UARTProtocol(com_manager)
            
            start_time = time.time()
            try:
                version = uart_protocol.register_read(RegisterMap.VERSION)
                end_time = time.time()
                response_time = (end_time - start_time) * 1000
                
                print(f"   ✅ 成功: VERSION = 0x{version:08X}")
                print(f"   ⏱️  応答時間: {response_time:.1f}ms")
                
            except Exception as e:
                end_time = time.time()
                response_time = (end_time - start_time) * 1000
                print(f"   ❌ 失敗: {e}")
                print(f"   ⏱️  経過時間: {response_time:.1f}ms")
            
            com_manager.disconnect()
            
        except Exception as e:
            print(f"   ❌ エラー: {e}")


def check_protocol_frame_format():
    """プロトコルフレーム形式の確認"""
    print("\n📋 UARTプロトコル フレーム形式確認")
    print("-" * 30)
    
    # VERSION読み取りコマンドの構築例
    try:
        com_manager = COMManager()
        uart_protocol = UARTProtocol(com_manager)
        
        # フレーム形式の理論値を表示
        print("期待されるフレーム形式:")
        print("SOF(1) + CMD(1) + ADDR(4) + LEN(2) + DATA(N) + CRC(1) + EOF(1)")
        print()
        print("VERSION読み取りコマンド例:")
        print("SOF: 0x7E")
        print("CMD: 0x01 (READ)")
        print("ADDR: 0x00 0x00 0x10 0x1C (VERSION = 0x101C, リトルエンディアン)")
        print("LEN: 0x00 0x04 (4バイト読み取り)")
        print("DATA: なし")
        print("CRC: 計算値")
        print("EOF: 0x7F")
        
    except Exception as e:
        print(f"❌ フレーム形式確認エラー: {e}")


def suggest_debugging_steps():
    """デバッグ手順の提案"""
    print("\n💡 推奨デバッグ手順")
    print("-" * 30)
    
    steps = [
        "1. FPGA電源とクロック供給の確認",
        "2. FPGA内UARTモジュールのリセット解除確認", 
        "3. ボーレート設定の再確認 (FPGA側クロック分周比)",
        "4. RTS/CTS信号線の物理接続確認",
        "5. オシロスコープでUART信号波形確認",
        "6. FPGA側でのUART受信割り込み動作確認",
        "7. シンプルなエコーバック機能でのテスト",
        "8. UARTプロトコルスタックの段階的デバッグ"
    ]
    
    for step in steps:
        print(f"   {step}")
    
    print("\n🔧 すぐに試せる対策:")
    print("   • ボーレートを38400や57600に下げる")
    print("   • フロー制御を無効にする")  
    print("   • タイムアウト値を5秒に増やす")
    print("   • FPGA側の電源リセット")


def main():
    """メインデバッグ実行"""
    print("🚨 AXIUART Driver - SOFタイムアウト デバッグ")
    print("=" * 60)
    print(f"実行時刻: {time.strftime('%Y-%m-%d %H:%M:%S')}")
    print()
    
    # エラー分析
    analyze_sof_timeout()
    
    # 各種テスト実行
    test_raw_uart_communication()
    test_uart_loopback()
    test_different_timeouts()
    check_protocol_frame_format()
    
    # デバッグ手順提案
    suggest_debugging_steps()
    
    print("\n📊 分析完了")
    print("上記の結果を参考に、FPGA側の設定や接続を確認してください。")


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\n\n⏹️  デバッグが中断されました。")
    except Exception as e:
        print(f"\n❌ 予期しないエラー: {e}")
        import traceback
        traceback.print_exc()