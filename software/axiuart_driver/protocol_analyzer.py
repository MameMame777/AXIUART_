#!/usr/bin/env python3
"""
FPGA Protocol Analysis Tool
実機FPGAとのプロトコル通信解析・デバッグツール
プロトコル仕様 v0.1 準拠
"""

import serial
import time
import sys

def crc8_calculate(data):
    """CRC8計算（polynomial 0x07, init 0x00）"""
    crc = 0x00
    for byte in data:
        crc ^= byte
        for i in range(8):
            if crc & 0x80:
                crc = ((crc << 1) ^ 0x07) & 0xFF
            else:
                crc = (crc << 1) & 0xFF
    return crc

def build_read_frame(addr, size=2, length=1, auto_inc=False):
    """読み込みフレーム構築（プロトコル仕様準拠）"""
    # CMD構築: RW=1, INC, SIZE, LEN
    cmd = 0x80  # RW=1 (読み込み)
    if auto_inc:
        cmd |= 0x40  # INC=1
    cmd |= (size << 4)  # SIZE: 0=8bit, 1=16bit, 2=32bit
    cmd |= (length - 1)  # LEN-1 (0-based)
    
    # フレーム構築
    frame = bytearray()
    frame.append(0xA5)  # SOF (Host→Device)
    frame.append(cmd)   # CMD
    
    # ADDR (little-endian)
    frame.append((addr >>  0) & 0xFF)
    frame.append((addr >>  8) & 0xFF)
    frame.append((addr >> 16) & 0xFF)
    frame.append((addr >> 24) & 0xFF)
    
    # CRC8 (CMD through ADDR)
    crc_data = frame[1:6]  # CMD + ADDR
    crc = crc8_calculate(crc_data)
    frame.append(crc)
    
    return bytes(frame)

def build_write_frame(addr, data, size=2, auto_inc=False):
    """書き込みフレーム構築（プロトコル仕様準拠）"""
    length = len(data) // (1 << size)
    
    # CMD構築: RW=0, INC, SIZE, LEN
    cmd = 0x00  # RW=0 (書き込み)
    if auto_inc:
        cmd |= 0x40  # INC=1
    cmd |= (size << 4)  # SIZE
    cmd |= (length - 1)  # LEN-1
    
    # フレーム構築
    frame = bytearray()
    frame.append(0xA5)  # SOF
    frame.append(cmd)   # CMD
    
    # ADDR (little-endian)
    frame.append((addr >>  0) & 0xFF)
    frame.append((addr >>  8) & 0xFF)
    frame.append((addr >> 16) & 0xFF)
    frame.append((addr >> 24) & 0xFF)
    
    # DATA
    frame.extend(data)
    
    # CRC8 (CMD through DATA)
    crc_data = frame[1:]  # CMD + ADDR + DATA
    crc = crc8_calculate(crc_data)
    frame.append(crc)
    
    return bytes(frame)

def analyze_response_pattern(data):
    """受信データパターンの解析（RTLレジスタマップ対応）"""
    print(f"📊 受信データ解析: {data.hex().upper()}")
    
    if len(data) == 0:
        print("   ❌ データなし")
        return
    
    # SOF確認
    if len(data) >= 1:
        sof = data[0]
        if sof == 0x5A:
            print("   ✅ SOF正常 (0x5A - Device→Host)")
        else:
            print(f"   ❌ SOF異常 (0x{sof:02X} ≠ 0x5A)")
            print(f"      ビット比較: 0x5A={0x5A:08b}, 受信={sof:08b}")
    
    # フレーム長による分類と詳細解析
    if len(data) == 4:
        print("   📏 4バイト応答 → エラー応答")
        if len(data) >= 3 and data[0] == 0x5A:
            status, cmd = data[1], data[2]
            print(f"   📋 STATUS: 0x{status:02X}, CMD echo: 0x{cmd:02X}")
            
            # STATUS コード解釈
            status_map = {
                0x00: "OK (成功)",
                0x01: "CRC_ERR (CRC不一致)", 
                0x02: "CMD_INV (無効コマンド)",
                0x03: "ADDR_ALIGN (アドレス不整合)",
                0x04: "TIMEOUT (タイムアウト)",
                0x05: "AXI_SLVERR (AXIスレーブエラー)",
                0x06: "BUSY (ビジー状態)",
                0x07: "LEN_RANGE (長さ範囲外)",
                0x08: "PARAM (パラメータエラー)"
            }
            status_desc = status_map.get(status, f"未知エラー(0x{status:02X})")
            print(f"   � STATUS詳細: {status_desc}")
            
    elif len(data) >= 7:
        print("   📏 長フレーム → 成功応答")
        if len(data) >= 3 and data[0] == 0x5A:
            status, cmd = data[1], data[2]
            print(f"   📋 STATUS: 0x{status:02X}, CMD echo: 0x{cmd:02X}")
            
            # CMD解析
            rw = (cmd >> 7) & 1
            inc = (cmd >> 6) & 1
            size = (cmd >> 4) & 3
            length = (cmd & 0xF) + 1
            print(f"   🔍 CMD詳細: RW={'Read' if rw else 'Write'}, INC={inc}, SIZE={size}, LEN={length}")
            
            # 読み込み応答の場合、データ部分を解析
            if rw == 1 and status == 0x00 and len(data) >= 12:  # 成功読み込み応答
                addr = int.from_bytes(data[3:7], 'little')
                read_data = int.from_bytes(data[7:11], 'little')
                print(f"   📍 ADDR: 0x{addr:08X}")
                print(f"   📄 DATA: 0x{read_data:08X}")
                
                # レジスタ別期待値チェック
                if addr == 0x0000101C:  # REG_VERSION
                    expected = 0x00010000
                    if read_data == expected:
                        print(f"   ✅ VERSION正常 (期待値: 0x{expected:08X})")
                    else:
                        print(f"   ❌ VERSION異常 (期待値: 0x{expected:08X}, 実際: 0x{read_data:08X})")
                elif addr == 0x00001000:  # REG_CONTROL
                    bridge_enable = read_data & 1
                    print(f"   🔧 CONTROL解析: bridge_enable={bridge_enable}")
                elif addr == 0x00001004:  # REG_STATUS
                    bridge_busy = read_data & 1
                    error_code = (read_data >> 1) & 0xFF
                    print(f"   📊 STATUS解析: bridge_busy={bridge_busy}, error_code=0x{error_code:02X}")
    
    # CRC検証（仕様準拠）
    if len(data) >= 4 and data[0] == 0x5A:
        expected_crc = crc8_calculate(data[1:-1])  # STATUS〜最後の前まで
        actual_crc = data[-1]
        if expected_crc == actual_crc:
            print(f"   ✅ CRC正常 (0x{actual_crc:02X})")
        else:
            print(f"   ❌ CRC異常 (期待:0x{expected_crc:02X}, 実際:0x{actual_crc:02X})")
    
    print(f"   📏 データ長: {len(data)} bytes")
    if len(data) <= 16:
        print(f"   🔢 バイト詳細: {' '.join(f'{b:02X}' for b in data)}")

def test_protocol_compliance(port):
    """プロトコル仕様準拠テスト（RTLレジスタマップ対応）"""
    print("🎯 プロトコル仕様準拠テスト")
    print("=" * 50)
    
    # RTL Register_Block.sv のアドレスマップに基づく
    # BASE_ADDR = 0x00001000
    base_addr = 0x00001000
    
    test_cases = [
        {
            "name": "REG_CONTROL Read (0x1000)",
            "frame": build_read_frame(base_addr + 0x000, size=2, length=1),  # 32-bit read
            "description": "制御レジスタ読み込み（bridge_enable等）"
        },
        {
            "name": "REG_STATUS Read (0x1004)", 
            "frame": build_read_frame(base_addr + 0x004, size=2, length=1),  # 32-bit read
            "description": "ステータスレジスタ読み込み（bridge_busy, error_code）"
        },
        {
            "name": "REG_CONFIG Read (0x1008)",
            "frame": build_read_frame(base_addr + 0x008, size=2, length=1),  # 32-bit read  
            "description": "設定レジスタ読み込み（baud_div, timeout_config）"
        },
        {
            "name": "REG_VERSION Read (0x101C)",
            "frame": build_read_frame(base_addr + 0x01C, size=2, length=1),  # 32-bit read
            "description": "バージョンレジスタ読み込み（期待値: 0x00010000）"
        },
        {
            "name": "REG_CONTROL Write (0x1000)",
            "frame": build_write_frame(base_addr + 0x000, b'\x01\x00\x00\x00', size=2),  # bridge_enable=1
            "description": "制御レジスタ書き込み（bridge_enable=1）"
        },
        {
            "name": "REG_TX_COUNT Read (0x1010)",
            "frame": build_read_frame(base_addr + 0x010, size=2, length=1),  # 32-bit read
            "description": "TX カウンタ読み込み（読み取り専用）"
        },
        {
            "name": "Invalid Address Test (0x2000)",
            "frame": build_read_frame(0x00002000, size=2, length=1),  # 範囲外アドレス
            "description": "無効アドレステスト（AXI_SLVERRが期待される）"
        }
    ]
    
    results = {}
    
    for test_case in test_cases:
        print(f"\n📤 {test_case['name']}")
        print(f"   説明: {test_case['description']}")
        
        frame = test_case['frame']
        print(f"   送信データ: {frame.hex().upper()}")
        
        # フレーム詳細解析
        if len(frame) >= 7:
            sof, cmd = frame[0], frame[1]
            addr = int.from_bytes(frame[2:6], 'little')
            print(f"   SOF: 0x{sof:02X}, CMD: 0x{cmd:02X}, ADDR: 0x{addr:08X}")
            
            # CMD解析
            rw = (cmd >> 7) & 1
            inc = (cmd >> 6) & 1  
            size = (cmd >> 4) & 3
            length = (cmd & 0xF) + 1
            print(f"   CMD詳細: {'Read' if rw else 'Write'}, SIZE={size}, LEN={length}")
            
            # 期待値表示
            if 'VERSION' in test_case['name']:
                print(f"   期待値: SOF=0x5A, STATUS=0x00, DATA=0x00010000")
            elif 'Invalid' in test_case['name']:
                print(f"   期待値: SOF=0x5A, STATUS=0x05 (AXI_SLVERR)")
            else:
                print(f"   期待値: SOF=0x5A, STATUS=0x00")
        
        port.write(frame)
        port.flush()
        time.sleep(1.0)  # 応答待機
        
        if port.in_waiting > 0:
            response = port.read(port.in_waiting)
            print(f"   📥 受信データ: {response.hex().upper()}")
            analyze_response_pattern(response)
            results[test_case['name']] = response
        else:
            print(f"   📥 受信データ: なし")
            results[test_case['name']] = None
    
    return results

def test_continuous_monitoring(port, duration=10):
    """継続監視テスト"""
    print(f"\n🔍 継続監視テスト ({duration}秒)")
    print("=" * 50)
    
    print("📡 自発的な送信データを監視中...")
    start_time = time.time()
    all_data = b''
    packet_count = 0
    
    while time.time() - start_time < duration:
        if port.in_waiting > 0:
            chunk = port.read(port.in_waiting)
            all_data += chunk
            packet_count += 1
            timestamp = time.strftime('%H:%M:%S')
            print(f"   [{timestamp}] パケット{packet_count}: {chunk.hex().upper()}")
        
        time.sleep(0.1)
    
    print(f"\n📊 監視結果:")
    print(f"   総受信: {len(all_data)} bytes, {packet_count} パケット")
    if all_data:
        print(f"   全データ: {all_data.hex().upper()}")
    else:
        print("   自発送信なし")
    
    return all_data

def main():
    """メイン解析フロー（プロトコル仕様準拠）"""
    print("🔬 FPGA プロトコル解析ツール v2.0")
    print("=" * 70)
    print(f"実行時刻: {time.strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"対象ポート: COM3 (115200 baud)")
    print("📋 プロトコル仕様: UART–AXI4-Lite Bridge Protocol v0.1")
    print("💡 注記: プロトコル準拠フレームのみテスト（単純バイト送信は無効）")
    
    try:
        # ポート接続
        print("\n🔌 COM3ポートに接続中...")
        port = serial.Serial('COM3', 115200, timeout=2.0)
        print("✅ 接続成功")
        
        # プロトコル準拠テスト実行
        compliance_results = test_protocol_compliance(port)
        
        # 継続監視（自発送信確認）
        monitoring_data = test_continuous_monitoring(port, 5)
        
        # 結果サマリー
        print("\n" + "=" * 70)
        print("📋 プロトコル準拠テスト結果サマリー")
        print("=" * 70)
        
        for test_name, result in compliance_results.items():
            status = "✅ 応答あり" if result else "❌ 応答なし"
            print(f"   {test_name}: {status}")
            if result:
                # SOF確認
                if len(result) >= 1:
                    sof_status = "✅ 正常" if result[0] == 0x5A else f"❌ 異常(0x{result[0]:02X})"
                    print(f"      SOF: {sof_status}")
                print(f"      → {result.hex().upper()}")
        
        print(f"\n🔍 継続監視結果:")
        if monitoring_data:
            print(f"   自発送信: {len(monitoring_data)} bytes")
        else:
            print(f"   自発送信: なし")
        
        # 診断結果とCRC検証
        print("\n💡 診断結果:")
        valid_responses = [r for r in compliance_results.values() if r and len(r) >= 1]
        
        if valid_responses:
            print("   ✅ FPGA応答確認 - プロトコル層は動作中")
            
            sof_correct = sum(1 for r in valid_responses if r[0] == 0x5A)
            if sof_correct == 0:
                print("   ⚠️  SOFマーカーが全て異常 - UART信号極性または実装問題")
                print("   🔧 推奨: Frame_Builderの送信部分確認")
            elif sof_correct < len(valid_responses):
                print("   ⚠️  SOFマーカーが部分的に異常")
            else:
                print("   ✅ SOFマーカー正常")
                
            # フレーム長分析
            frame_lengths = [len(r) for r in valid_responses if r]
            if all(l == 4 for l in frame_lengths):
                print("   � 全て4バイト応答 → 全てエラー応答の可能性")
            elif any(l >= 7 for l in frame_lengths):
                print("   � 長フレーム検出 → 成功応答あり")
        else:
            print("   ❌ FPGA無応答 - ハードウェア・RTL確認必要")
        
        port.close()
        
    except serial.SerialException as e:
        print(f"❌ シリアルポートエラー: {e}")
        return 1
    except KeyboardInterrupt:
        print(f"\n\n⏹️  ユーザーによりテストが中断されました")
        return 0
    except Exception as e:
        print(f"❌ 予期しないエラー: {e}")
        import traceback
        traceback.print_exc()
        return 1
    
    print("\n✨ プロトコル解析完了")
    return 0

if __name__ == "__main__":
    sys.exit(main())