"""
AXIUART Driver - FPGA実機テスト用CLIツール

COM3接続のFPGA実機との通信テスト用コマンドラインツール
"""

import sys
import os
import time

# Add current directory to path for module imports
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from core import COMManager, UARTProtocol, RegisterMap


def test_fpga_connection():
    """FPGA実機接続テスト"""
    print("🔌 FPGA実機接続テスト開始")
    print("=" * 50)
    
    try:
        # COM manager初期化
        com_manager = COMManager()
        
        # 利用可能ポート確認
        ports = com_manager.scan_ports()
        print(f"利用可能なCOMポート: {ports}")
        
        if "COM3" not in ports:
            print("❌ COM3が見つかりません。FPGAが接続されていることを確認してください。")
            return False
        
        # COM3に接続
        print("\n📡 COM3への接続を試行中...")
        success = com_manager.connect("COM3", 115200, flow_control=True)
        
        if not success:
            print("❌ COM3への接続に失敗しました。")
            return False
        
        print("✅ COM3への接続に成功しました！")
        
        # プロトコル初期化
        uart_protocol = UARTProtocol(com_manager)
        
        return com_manager, uart_protocol
        
    except Exception as e:
        print(f"❌ 接続エラー: {e}")
        return False


def test_register_access(uart_protocol):
    """レジスタアクセステスト"""
    print("\n📋 レジスタアクセステスト")
    print("-" * 30)
    
    test_results = []
    
    # テスト対象レジスタ
    test_registers = [
        ("VERSION", RegisterMap.VERSION, "バージョン情報"),
        ("STATUS", RegisterMap.STATUS, "ステータス"),
        ("CONTROL", RegisterMap.CONTROL, "制御レジスタ"),
        ("CONFIG", RegisterMap.CONFIG, "設定レジスタ")
    ]
    
    for name, address, description in test_registers:
        try:
            print(f"\n🔍 {name} レジスタ (0x{address:04X}) - {description}")
            
            # レジスタ読み取り
            start_time = time.time()
            value = uart_protocol.register_read(address)
            end_time = time.time()
            
            response_time = (end_time - start_time) * 1000  # ms
            
            print(f"   値: 0x{value:08X}")
            print(f"   応答時間: {response_time:.1f}ms")
            
            test_results.append((name, address, value, response_time, True))
            
        except Exception as e:
            print(f"   ❌ エラー: {e}")
            test_results.append((name, address, None, 0, False))
    
    return test_results


def test_bridge_control(uart_protocol):
    """ブリッジ制御テスト"""
    print("\n🌉 ブリッジ制御テスト")
    print("-" * 30)
    
    try:
        # 初期ステータス確認
        print("1. 初期ステータス確認...")
        initial_status = uart_protocol.register_read(RegisterMap.STATUS)
        print(f"   初期STATUS: 0x{initial_status:08X}")
        
        # ブリッジ有効化
        print("\n2. ブリッジ有効化...")
        uart_protocol.register_write(RegisterMap.CONTROL, RegisterMap.CONTROL_BRIDGE_ENABLE)
        print("   CONTROL書き込み完了")
        
        # ステータス再確認
        time.sleep(0.1)  # 少し待機
        print("\n3. ステータス再確認...")
        new_status = uart_protocol.register_read(RegisterMap.STATUS)
        print(f"   新STATUS: 0x{new_status:08X}")
        
        # 変化確認
        if new_status != initial_status:
            print("   ✅ ステータス変化を確認！")
            print(f"   変化: 0x{initial_status:08X} → 0x{new_status:08X}")
        else:
            print("   ⚠️  ステータス変化なし")
        
        return True
        
    except Exception as e:
        print(f"   ❌ ブリッジ制御エラー: {e}")
        return False


def test_memory_access(uart_protocol):
    """任意メモリアクセステスト"""
    print("\n💾 任意メモリアクセステスト")
    print("-" * 30)
    
    # テストパターン
    test_addresses = [0x1000, 0x1004, 0x1008, 0x100C, 0x2000]
    
    for addr in test_addresses:
        try:
            print(f"\n📍 アドレス 0x{addr:04X} の読み取り...")
            value = uart_protocol.register_read(addr)
            print(f"   値: 0x{value:08X}")
            
        except Exception as e:
            print(f"   ❌ エラー: {e}")
    
    # 書き込みテスト (0x2000番台)
    test_addr = 0x2000
    test_data = 0x12345678
    
    try:
        print(f"\n✏️  書き込みテスト (0x{test_addr:04X})")
        print(f"   書き込みデータ: 0x{test_data:08X}")
        
        # 書き込み
        uart_protocol.register_write(test_addr, test_data)
        print("   書き込み完了")
        
        # 読み返し
        read_value = uart_protocol.register_read(test_addr)
        print(f"   読み返し値: 0x{read_value:08X}")
        
        if read_value == test_data:
            print("   ✅ 書き込み検証成功！")
        else:
            print("   ❌ 書き込み検証失敗")
            
    except Exception as e:
        print(f"   ❌ 書き込みテストエラー: {e}")


def main():
    """メインテスト実行"""
    print("🚀 AXIUART Driver - FPGA実機テスト")
    print("=" * 60)
    print("対象: COM3接続のFPGA")
    print(f"実行時刻: {time.strftime('%Y-%m-%d %H:%M:%S')}")
    print()
    
    # 接続テスト
    connection_result = test_fpga_connection()
    if not connection_result:
        print("\n❌ 接続テストに失敗しました。テストを中止します。")
        return False
    
    com_manager, uart_protocol = connection_result
    
    try:
        # レジスタアクセステスト
        register_results = test_register_access(uart_protocol)
        
        # ブリッジ制御テスト
        bridge_result = test_bridge_control(uart_protocol)
        
        # メモリアクセステスト
        test_memory_access(uart_protocol)
        
        # 統計情報表示
        print("\n📊 通信統計情報")
        print("-" * 30)
        stats = uart_protocol.get_statistics()
        for key, value in stats.items():
            print(f"   {key}: {value}")
        
        # 結果サマリー
        print("\n📋 テスト結果サマリー")
        print("-" * 30)
        successful_reads = len([r for r in register_results if r[4]])
        total_reads = len(register_results)
        
        print(f"   レジスタ読み取り: {successful_reads}/{total_reads} 成功")
        print(f"   ブリッジ制御: {'✅ 成功' if bridge_result else '❌ 失敗'}")
        
        if successful_reads == total_reads and bridge_result:
            print("\n🎉 全テストが成功しました！FPGA通信が正常に動作しています。")
        else:
            print("\n⚠️  一部のテストで問題が発生しました。詳細を確認してください。")
        
    except Exception as e:
        print(f"\n❌ テスト実行中にエラーが発生しました: {e}")
    
    finally:
        # 接続クローズ
        try:
            com_manager.disconnect()
            print("\n🔌 COM3接続をクローズしました。")
        except:
            pass
    
    print("\n✨ テスト完了")
    return True


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\n\n⏹️  ユーザーによりテストが中断されました。")
    except Exception as e:
        print(f"\n❌ 予期しないエラーが発生しました: {e}")
        import traceback
        traceback.print_exc()