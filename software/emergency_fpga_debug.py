#!/usr/bin/env python3
"""
FPGA実機問題の緊急調査ツール
STATUS 0x80とSOF 0xADの根本原因を特定
"""

import serial
import time
import struct

# プロトコル定数
SOF_HOST_TO_DEVICE = 0xA5
SOF_DEVICE_TO_HOST_EXPECTED = 0x5A
CMD_READ = 0x00
CMD_WRITE = 0x01

# CRC-8計算（RTLと同じ多項式）
def calculate_crc8(data):
    """CRC-8計算 (polynomial: 0x07)"""
    crc = 0x00
    for byte in data:
        crc ^= byte
        for _ in range(8):
            if crc & 0x80:
                crc = (crc << 1) ^ 0x07
            else:
                crc = crc << 1
            crc &= 0xFF
    return crc

def build_read_frame(address):
    """読み取りフレーム構築"""
    addr_bytes = list(struct.pack('<I', address))[:4]
    frame_data = [SOF_HOST_TO_DEVICE, CMD_READ] + addr_bytes
    crc = calculate_crc8(frame_data)
    return frame_data + [crc]

def analyze_response(response_data):
    """応答を詳細分析"""
    if len(response_data) < 3:
        return f"応答が短すぎます: {len(response_data)} bytes"
    
    # SOF分析
    sof = response_data[0]
    status = response_data[1]
    
    analysis = []
    analysis.append(f"SOF: 0x{sof:02X}")
    
    if sof == SOF_DEVICE_TO_HOST_EXPECTED:
        analysis.append("  ✅ SOF正常")
    elif sof == 0xAD:
        analysis.append("  ❌ SOF異常 (0xAD) - 期待値: 0x5A")
        # ビット分析
        expected_bits = f"{SOF_DEVICE_TO_HOST_EXPECTED:08b}"
        actual_bits = f"{sof:08b}"
        xor_result = SOF_DEVICE_TO_HOST_EXPECTED ^ sof
        analysis.append(f"    期待: 0x5A = {expected_bits}")
        analysis.append(f"    実際: 0x{sof:02X} = {actual_bits}")
        analysis.append(f"    XOR:  0x{xor_result:02X} = {xor_result:08b}")
    else:
        analysis.append(f"  ❌ SOF未知 (0x{sof:02X})")
    
    # STATUS分析
    analysis.append(f"STATUS: 0x{status:02X}")
    
    status_map = {
        0x00: "OK",
        0x01: "CRC_ERR", 
        0x02: "CMD_INV",
        0x03: "ADDR_ALIGN",
        0x04: "TIMEOUT",
        0x05: "AXI_SLVERR",
        0x06: "BUSY",
        0x07: "LEN_RANGE"
    }
    
    if status in status_map:
        analysis.append(f"  ✅ STATUS認識: {status_map[status]}")
    elif status == 0x80:
        analysis.append("  ❌ STATUS未定義 (0x80)")
        analysis.append("    0x80 = 10000000 (MSB=1)")
        analysis.append("    これは初期化されていない可能性")
    else:
        analysis.append(f"  ❌ STATUS未知 (0x{status:02X})")
    
    # データ分析
    if len(response_data) > 2:
        data_bytes = response_data[2:]
        analysis.append(f"データ: {' '.join(f'0x{b:02X}' for b in data_bytes)}")
        
        if len(data_bytes) >= 4:
            data_value = struct.unpack('<I', bytes(data_bytes[:4]))[0]
            analysis.append(f"  32bit値: 0x{data_value:08X}")
    
    return "\n".join(analysis)

def emergency_fpga_debug():
    """緊急FPGA調査"""
    print("🚨 FPGA緊急調査開始")
    print("=" * 50)
    
    try:
        with serial.Serial('COM3', 115200, timeout=2) as ser:
            print("✅ COM3接続成功")
            
            # テスト対象アドレス
            test_addresses = [
                0x00001000,  # BASE_ADDR + REG_CONTROL
                0x00001004,  # BASE_ADDR + REG_STATUS  
                0x0000101C,  # BASE_ADDR + REG_VERSION
            ]
            
            for i, addr in enumerate(test_addresses):
                print(f"\n📍 テスト {i+1}: アドレス 0x{addr:08X}")
                print("-" * 30)
                
                # フレーム送信
                frame = build_read_frame(addr)
                frame_bytes = bytes(frame)
                
                print(f"送信: {' '.join(f'0x{b:02X}' for b in frame)}")
                
                ser.write(frame_bytes)
                time.sleep(0.1)
                
                # 応答受信
                response = ser.read(100)
                
                if response:
                    response_list = list(response)
                    print(f"受信: {' '.join(f'0x{b:02X}' for b in response_list)}")
                    print("\n🔍 詳細分析:")
                    print(analyze_response(response_list))
                    
                    # 特定パターンの検出
                    if len(response_list) >= 2:
                        sof, status = response_list[0], response_list[1]
                        
                        # 重要パターンの検出
                        if sof == 0xAD and status == 0x80:
                            print("\n🎯 パターン検出: SOF=0xAD + STATUS=0x80")
                            print("   これは一貫したパターンです")
                            
                            # さらなる分析
                            print("\n🧮 バイナリ分析:")
                            print(f"   SOF 0xAD  = {0xAD:08b}")
                            print(f"   STATUS 0x80 = {0x80:08b}")
                            
                            # 可能性の分析
                            print("\n💡 考えられる原因:")
                            print("   1. UART信号の極性反転")
                            print("   2. 初期化値の問題")
                            print("   3. タイミング同期の問題")
                
                else:
                    print("❌ 応答なし")
                
                time.sleep(0.5)
            
            print("\n" + "=" * 50)
            print("🔍 調査完了")
            
    except serial.SerialException as e:
        print(f"❌ シリアル通信エラー: {e}")
    except Exception as e:
        print(f"❌ 予期しないエラー: {e}")

if __name__ == "__main__":
    emergency_fpga_debug()