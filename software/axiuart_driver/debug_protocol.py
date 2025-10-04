#!/usr/bin/env python3
"""
AXIUART Protocol Debug Tool
AXIUARTプロトコルでFPGAとの通信をデバッグするツール
"""

import serial
import time
import sys
import os

# CRC-8計算
def calculate_crc8(data):
    """CRC-8計算 (多項式0x07)"""
    crc = 0x00
    for byte in data:
        crc ^= byte
        for _ in range(8):
            if crc & 0x80:
                crc = (crc << 1) ^ 0x07
            else:
                crc <<= 1
            crc &= 0xFF
    return crc

def create_read_frame(address):
    """読み取りフレーム作成"""
    frame = bytearray()
    frame.append(0xA5)  # SOF
    frame.append(0x80)  # CMD (READ, 32bit)
    frame.extend(address.to_bytes(4, 'little'))  # Address (little endian)
    
    # CRC計算 (SOF除く)
    crc = calculate_crc8(frame[1:])
    frame.append(crc)
    
    return bytes(frame)

def parse_response_frame(data):
    """応答フレーム解析"""
    if len(data) < 2:
        return None, "データが短すぎます"
    
    if data[0] != 0x5A:
        return None, f"不正なSOF: 0x{data[0]:02X}"
    
    status = data[1]
    
    if len(data) < 7:  # SOF + STATUS + DATA(4) + CRC
        return None, "データフレームが短すぎます"
    
    data_bytes = data[2:6]
    received_crc = data[6]
    
    # CRC検証
    calc_crc = calculate_crc8(data[1:6])
    if calc_crc != received_crc:
        return None, f"CRCエラー: 計算値=0x{calc_crc:02X}, 受信値=0x{received_crc:02X}"
    
    value = int.from_bytes(data_bytes, 'little')
    return {"status": status, "value": value}, None

def test_fpga_protocol(port_name="COM3", timeout=2.0):
    """FPGAプロトコルテスト"""
    print(f"🔌 FPGA プロトコルテスト - {port_name}")
    print("=" * 50)
    
    try:
        # ポート開放
        ser = serial.Serial(
            port=port_name,
            baudrate=115200,
            bytesize=8,
            parity='N',
            stopbits=1,
            timeout=timeout,
            rtscts=False,
            dsrdtr=False
        )
        
        print(f"✅ ポート開放成功")
        print(f"   タイムアウト: {timeout}秒")
        
        # バッファクリア
        ser.reset_input_buffer()
        ser.reset_output_buffer()
        
        # テスト対象レジスタ
        test_registers = [
            (0x1000, "VERSION"),
            (0x1004, "STATUS"),
            (0x1008, "CONTROL"),
            (0x100C, "CONFIG")
        ]
        
        results = []
        
        for address, name in test_registers:
            print(f"\n📋 {name} レジスタテスト (0x{address:04X})")
            print("-" * 30)
            
            # フレーム作成
            frame = create_read_frame(address)
            print(f"送信フレーム: {frame.hex().upper()}")
            
            # 送信
            start_time = time.time()
            ser.write(frame)
            ser.flush()
            print("✅ フレーム送信完了")
            
            # 応答待機
            print("⏳ 応答待機中...")
            response_data = bytearray()
            
            # タイムアウトまで受信
            while True:
                if ser.in_waiting > 0:
                    new_data = ser.read(ser.in_waiting)
                    response_data.extend(new_data)
                    print(f"📥 受信データ追加: {new_data.hex().upper()}")
                
                # 完全なフレームかチェック
                if len(response_data) >= 7:
                    break
                
                # タイムアウトチェック
                if time.time() - start_time > timeout:
                    print("⏰ タイムアウト")
                    break
                
                time.sleep(0.01)  # 10ms待機
            
            end_time = time.time()
            response_time = (end_time - start_time) * 1000
            
            print(f"📥 受信データ合計: {response_data.hex().upper()}")
            print(f"⏱️  応答時間: {response_time:.1f}ms")
            
            # 応答解析
            if len(response_data) > 0:
                result, error = parse_response_frame(response_data)
                if result:
                    print(f"✅ 解析成功")
                    print(f"   ステータス: 0x{result['status']:02X}")
                    print(f"   値: 0x{result['value']:08X}")
                    results.append((name, address, result['value'], response_time, True))
                else:
                    print(f"❌ 解析エラー: {error}")
                    results.append((name, address, None, response_time, False))
            else:
                print("❌ 応答なし")
                results.append((name, address, None, response_time, False))
            
            time.sleep(0.1)  # 次のテストまで100ms待機
        
        ser.close()
        
        # 結果サマリー
        print(f"\n📊 テスト結果サマリー")
        print("=" * 50)
        successful = 0
        for name, addr, value, resp_time, success in results:
            status = "✅" if success else "❌"
            if success:
                print(f"{status} {name:8} (0x{addr:04X}): 0x{value:08X} ({resp_time:.1f}ms)")
                successful += 1
            else:
                print(f"{status} {name:8} (0x{addr:04X}): 失敗 ({resp_time:.1f}ms)")
        
        print(f"\n成功率: {successful}/{len(results)} ({successful/len(results)*100:.1f}%)")
        
        return results
        
    except Exception as e:
        print(f"❌ エラー: {e}")
        return []

def main():
    """メイン関数"""
    print("🚀 AXIUART Protocol Debug Tool")
    print("=" * 60)
    print(f"実行時刻: {time.strftime('%Y-%m-%d %H:%M:%S')}")
    
    # COM3でテスト実行
    results = test_fpga_protocol("COM3", timeout=3.0)
    
    if not results:
        print("\n❌ テストを実行できませんでした")
    elif any(r[4] for r in results):
        print("\n🎉 一部またはすべてのテストが成功しました！")
    else:
        print("\n⚠️  すべてのテストが失敗しました。FPGA の状態を確認してください。")
    
    print("\n💡 FPGAが応答しない場合のチェックポイント:")
    print("   1. FPGA の電源とリセット状態")
    print("   2. UART 接続とボーレート設定")
    print("   3. FPGA 内の AXIUART モジュールの動作")
    print("   4. クロック供給とタイミング")
    
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