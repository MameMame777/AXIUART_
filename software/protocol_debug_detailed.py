#!/usr/bin/env python3
"""
詳細プロトコル分析スクリプト
Frame_Builder修正後の読み出し応答を詳細に分析
"""

import serial
import time
import sys
from typing import List, Tuple, Optional

# CRC-8 polynomial 0x07 implementation
def calculate_crc8(data: List[int], polynomial: int = 0x07) -> int:
    """Calculate CRC-8 with polynomial 0x07"""
    crc = 0x00
    for byte in data:
        crc ^= byte
        for _ in range(8):
            if crc & 0x80:
                crc = (crc << 1) ^ polynomial
            else:
                crc = crc << 1
            crc &= 0xFF
    return crc

def analyze_response(response: List[int], request_addr: int, request_cmd: int) -> None:
    """詳細な応答分析"""
    print(f"📊 詳細応答分析")
    print(f"   応答長: {len(response)} bytes")
    print(f"   生データ: {' '.join([f'{b:02X}' for b in response])}")
    
    if len(response) < 4:
        print("   ❌ 応答が短すぎます")
        return
    
    print(f"   SOF: 0x{response[0]:02X} ({'✅ 正常' if response[0] == 0xAD else '❌ 異常'})")
    print(f"   STATUS: 0x{response[1]:02X} ({'✅ 成功' if response[1] == 0x80 else '❌ エラー'})")
    
    if len(response) >= 8:
        print(f"   CMD_ECHO: 0x{response[2]:02X} (期待値: 0x{request_cmd:02X} {'✅' if response[2] == request_cmd else '❌'})")
        print(f"   データ部: {' '.join([f'{response[i]:02X}' for i in range(3, len(response)-1)])}")
        print(f"   CRC: 0x{response[-1]:02X}")
        
        # CRC検証
        crc_data = response[1:-1]  # STATUS から CRC前まで
        calculated_crc = calculate_crc8(crc_data)
        print(f"   CRC検証: 計算値=0x{calculated_crc:02X}, 受信値=0x{response[-1]:02X} {'✅' if calculated_crc == response[-1] else '❌'}")
        
        # ADDR_ECHO分析（期待される位置）
        if len(response) >= 8:
            addr_echo_bytes = response[3:7] if len(response) >= 7 else response[3:]
            print(f"   ADDR_ECHO候補: {' '.join([f'{b:02X}' for b in addr_echo_bytes])}")
            if len(addr_echo_bytes) >= 4:
                addr_echo_value = (addr_echo_bytes[3] << 24) | (addr_echo_bytes[2] << 16) | (addr_echo_bytes[1] << 8) | addr_echo_bytes[0]
                print(f"   ADDR_ECHO値: 0x{addr_echo_value:08X} (期待値: 0x{request_addr:08X} {'✅' if addr_echo_value == request_addr else '❌'})")

def send_read_request(ser: serial.Serial, addr: int) -> Optional[List[int]]:
    """読み出しリクエストを送信して応答を受信"""
    # 読み出しコマンド構築（プロトコル仕様準拠）
    cmd = 0xA0  # 読み出し (RW=1, INC=0, SIZE=10=32bit, LEN=0=1beat)
    frame = [0xA5, cmd]  # SOF + CMD
    frame.extend([(addr >> (8*i)) & 0xFF for i in range(4)])  # ADDR (little-endian)
    # No LENGTH field in read request per protocol spec
    
    # CRC計算
    crc = calculate_crc8(frame[1:])  # SOF除く（CMD+ADDR[3:0]）
    frame.append(crc)
    
    print(f"📤 読み出しリクエスト (ADDR=0x{addr:08X})")
    print(f"   送信: {' '.join([f'{b:02X}' for b in frame])}")
    
    # 送信
    ser.write(bytes(frame))
    time.sleep(0.1)  # 応答待機
    
    # 応答受信
    response = []
    start_time = time.time()
    while time.time() - start_time < 1.0:  # 1秒タイムアウト
        if ser.in_waiting > 0:
            response.extend(ser.read(ser.in_waiting))
            if len(response) >= 8:  # 期待される最小応答長
                break
        time.sleep(0.01)
    
    if response:
        print(f"📥 応答受信: {' '.join([f'{b:02X}' for b in response])}")
        analyze_response(response, addr, cmd)
        return response
    else:
        print("   ❌ 応答なし")
        return None

def main():
    """メイン関数"""
    print("🔍 Frame_Builder 読み出しプロトコル詳細分析")
    print("=" * 60)
    
    try:
        # UART接続
        ser = serial.Serial('COM3', 115200, timeout=1)
        print(f"✅ COM3に接続しました")
        time.sleep(0.1)
        
        # 複数のアドレスをテスト
        test_addresses = [
            0x00001020,  # TEST_0
            0x00001024,  # TEST_1  
            0x00001028,  # TEST_2
            0x0000102C,  # TEST_3
            0x0000101C,  # VERSION
        ]
        
        for addr in test_addresses:
            print(f"\n📍 テストアドレス: 0x{addr:08X}")
            print("-" * 40)
            response = send_read_request(ser, addr)
            time.sleep(0.2)  # 間隔調整
        
        ser.close()
        print(f"\n🔌 UART接続を終了しました")
        
    except serial.SerialException as e:
        print(f"❌ UART接続エラー: {e}")
        sys.exit(1)
    except Exception as e:
        print(f"❌ エラー: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()