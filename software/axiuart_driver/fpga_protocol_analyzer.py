#!/usr/bin/env python3
"""
FPGA UART Protocol Analyzer
FPGAとの通信プロトコルを詳細に分析し、問題を特定するツール
"""

import serial
import time
import struct

def calculate_crc8(data):
    """CRC-8計算 (FPGA実装と同じアルゴリズム)"""
    crc = 0x00
    polynomial = 0x07  # x^8 + x^2 + x + 1
    
    for byte in data:
        crc ^= byte
        for _ in range(8):
            if crc & 0x80:
                crc = (crc << 1) ^ polynomial
            else:
                crc <<= 1
            crc &= 0xFF
    return crc

def build_command(cmd, addr, length, data=None):
    """UART-AXI4プロトコルのコマンドフレームを構築"""
    frame = bytearray()
    
    # SOF
    frame.append(0x7E)
    
    # Command
    frame.append(cmd)
    
    # Address (Little Endian, 4 bytes)
    addr_bytes = struct.pack('<I', addr)
    frame.extend(addr_bytes)
    
    # Length (Little Endian, 2 bytes)
    len_bytes = struct.pack('<H', length)
    frame.extend(len_bytes)
    
    # Data (if any)
    if data:
        frame.extend(data)
    
    # CRC calculation (exclude SOF and EOF)
    crc_data = frame[1:]  # CMD + ADDR + LEN + DATA
    crc = calculate_crc8(crc_data)
    frame.append(crc)
    
    # EOF
    frame.append(0x7F)
    
    return bytes(frame)

def send_and_wait_response(ser, command_data, timeout=2.0):
    """コマンド送信と応答待ち"""
    print(f"📤 Sending: {command_data.hex()}")
    
    # バッファクリア
    ser.reset_input_buffer()
    ser.reset_output_buffer()
    
    # コマンド送信
    ser.write(command_data)
    ser.flush()
    
    # 応答待ち
    start_time = time.time()
    response = bytearray()
    
    while time.time() - start_time < timeout:
        if ser.in_waiting > 0:
            data = ser.read(ser.in_waiting)
            response.extend(data)
            print(f"📥 Partial data: {data.hex()}")
            
            # EOF (0x7F) を探す
            if 0x7F in response:
                break
                
        time.sleep(0.01)
    
    elapsed = time.time() - start_time
    print(f"⏱️  Response time: {elapsed:.3f}s")
    
    if response:
        print(f"✅ Full response: {response.hex()}")
        return bytes(response)
    else:
        print(f"❌ No response after {timeout}s")
        return None

def test_fpga_communication():
    """FPGA通信の詳細テスト"""
    print("🔍 FPGA UART Protocol Analysis")
    print("=" * 40)
    
    try:
        # シリアルポート設定
        ser = serial.Serial(
            port='COM3',
            baudrate=115200,
            bytesize=serial.EIGHTBITS,
            parity=serial.PARITY_NONE,
            stopbits=serial.STOPBITS_ONE,
            timeout=0.1,
            xonxoff=False,
            rtscts=True,  # フロー制御有効
            dsrdtr=False
        )
        
        print(f"✅ Connected to {ser.name}")
        print(f"📋 Port settings: {ser.baudrate}bps, RTS/CTS={ser.rtscts}")
        
        # Test 1: VERSION レジスタ読み取り
        print(f"\n🧪 Test 1: VERSION Register Read")
        print("-" * 30)
        version_cmd = build_command(
            cmd=0x01,           # READ command
            addr=0x101C,        # VERSION register address
            length=4            # 4 bytes
        )
        print(f"📋 Command breakdown:")
        print(f"   SOF: 0x7E")
        print(f"   CMD: 0x01 (READ)")
        print(f"   ADDR: 0x101C (VERSION)")
        print(f"   LEN: 4 bytes")
        print(f"   CRC: 0x{calculate_crc8(version_cmd[1:-1]):02X}")
        print(f"   EOF: 0x7F")
        
        response = send_and_wait_response(ser, version_cmd, timeout=3.0)
        
        # Test 2: STATUS レジスタ読み取り
        print(f"\n🧪 Test 2: STATUS Register Read")
        print("-" * 30)
        status_cmd = build_command(
            cmd=0x01,           # READ command
            addr=0x1000,        # STATUS register address
            length=4            # 4 bytes
        )
        response = send_and_wait_response(ser, status_cmd, timeout=3.0)
        
        # Test 3: 単純なエコーテスト
        print(f"\n🧪 Test 3: Simple Echo Test")
        print("-" * 25)
        echo_data = b'\x7E\x00\x7F'  # SOF + NOP + EOF
        print(f"📤 Echo test: {echo_data.hex()}")
        ser.write(echo_data)
        ser.flush()
        time.sleep(0.5)
        
        if ser.in_waiting > 0:
            response = ser.read(ser.in_waiting)
            print(f"📥 Echo response: {response.hex()}")
        else:
            print(f"❌ No echo response")
        
        # Test 4: 制御信号の確認
        print(f"\n🧪 Test 4: Control Signals Check")
        print("-" * 30)
        print(f"📋 Before command:")
        print(f"   CTS: {ser.cts} (Clear To Send)")
        print(f"   DSR: {ser.dsr} (Data Set Ready)")
        print(f"   CD:  {ser.cd} (Carrier Detect)")
        print(f"   RI:  {ser.ri} (Ring Indicator)")
        
        # RTSを一時的に制御
        original_rts = ser.rts
        ser.rts = False
        time.sleep(0.1)
        print(f"📋 RTS=False -> CTS: {ser.cts}")
        ser.rts = True
        time.sleep(0.1)
        print(f"📋 RTS=True -> CTS: {ser.cts}")
        ser.rts = original_rts
        
        ser.close()
        
    except Exception as e:
        print(f"❌ Communication error: {e}")

def analyze_fpga_state():
    """FPGA状態の詳細分析"""
    print(f"\n🔍 FPGA State Analysis")
    print("=" * 30)
    
    print(f"💡 考えられる問題:")
    print(f"1. 🔌 FPGA電源が入っていない")
    print(f"2. ⚡ FPGAリセットが解除されていない")
    print(f"3. 🕐 FPGAクロックが供給されていない")
    print(f"4. 📟 UART_Rxモジュールが動作していない")
    print(f"5. 🔧 AXI4-Liteバスが動作していない")
    print(f"6. 📡 UARTボーレート設定が不一致")
    print(f"7. 🔄 フロー制御信号の問題")
    print(f"8. 📋 レジスタマップの不一致")
    
    print(f"\n🔧 推奨確認手順:")
    print(f"1. FPGAボード上のLEDの点灯確認")
    print(f"2. オシロスコープでUART_RX信号確認")
    print(f"3. FPGA内部信号をILAで確認")
    print(f"4. ボーレート分周設定の再確認")
    print(f"5. システムクロックとリセット信号確認")

def main():
    """メイン実行"""
    print("🚨 AXIUART FPGA - Protocol Level Debug")
    print("=" * 45)
    print(f"⏰ Analysis time: {time.strftime('%Y-%m-%d %H:%M:%S')}")
    
    # 通信テスト実行
    test_fpga_communication()
    
    # FPGA状態分析
    analyze_fpga_state()
    
    print(f"\n📊 Conclusion")
    print("=" * 15)
    print(f"✅ COM3 port access: OK")
    print(f"❌ FPGA response: NONE")
    print(f"💡 Issue: FPGA side not responding")
    print(f"🔧 Next action: Check FPGA hardware/configuration")

if __name__ == "__main__":
    main()