#!/usr/bin/env python3
"""
UART-AXI Protocol Test Tool
正しいプロトコルフレームを送信してRXカウンタ動作をテスト
"""

import serial
import time
import struct

def calculate_crc8(data):
    """CRC-8計算 (polynomial 0x07, init 0x00)"""
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

def create_read_frame(addr, size=2, length=1):
    """読み取りフレーム作成"""
    # SOF
    frame = [0xA5]
    
    # CMD: [7]=1(read), [6]=0(no inc), [5:4]=size, [3:0]=length-1
    cmd = 0x80  # Read command
    cmd |= (size & 0x03) << 4  # SIZE field
    cmd |= (length - 1) & 0x0F  # LEN field
    frame.append(cmd)
    
    # ADDR (4 bytes, little-endian)
    addr_bytes = struct.pack('<I', addr)
    frame.extend(addr_bytes)
    
    # CRC (CMD + ADDR)
    crc_data = frame[1:]  # Exclude SOF
    crc = calculate_crc8(crc_data)
    frame.append(crc)
    
    return bytes(frame)

def create_write_frame(addr, data_list, size=2):
    """書き込みフレーム作成"""
    # SOF
    frame = [0xA5]
    
    # CMD: [7]=0(write), [6]=0(no inc), [5:4]=size, [3:0]=length-1
    cmd = 0x00  # Write command
    cmd |= (size & 0x03) << 4  # SIZE field
    cmd |= (len(data_list) - 1) & 0x0F  # LEN field
    frame.append(cmd)
    
    # ADDR (4 bytes, little-endian)
    addr_bytes = struct.pack('<I', addr)
    frame.extend(addr_bytes)
    
    # DATA (multiple beats)
    for data in data_list:
        if size == 0:  # 8-bit
            frame.append(data & 0xFF)
        elif size == 1:  # 16-bit
            data_bytes = struct.pack('<H', data & 0xFFFF)
            frame.extend(data_bytes)
        elif size == 2:  # 32-bit
            data_bytes = struct.pack('<I', data & 0xFFFFFFFF)
            frame.extend(data_bytes)
    
    # CRC (CMD + ADDR + DATA)
    crc_data = frame[1:]  # Exclude SOF
    crc = calculate_crc8(crc_data)
    frame.append(crc)
    
    return bytes(frame)

def test_protocol_frames(port_name="COM3"):
    """プロトコルフレームテスト"""
    print(f"📡 UART-AXIプロトコルフレームテスト - {port_name}")
    print("=" * 60)
    
    try:
        ser = serial.Serial(port_name, 115200, timeout=2.0)
        print("✅ ポート開放成功")
        
        # 1. レジスタ読み取りテスト (0x1000番地)
        print("\n📖 レジスタ読み取りテスト")
        read_frame = create_read_frame(0x1000, size=2, length=1)
        print(f"   送信フレーム: {read_frame.hex().upper()}")
        
        ser.write(read_frame)
        time.sleep(0.1)
        
        if ser.in_waiting > 0:
            response = ser.read(ser.in_waiting)
            print(f"   受信応答: {response.hex().upper()}")
        else:
            print("   応答なし")
        
        # 2. レジスタ書き込みテスト (0x1000番地に0x12345678)
        print("\n📝 レジスタ書き込みテスト")
        write_frame = create_write_frame(0x1000, [0x12345678], size=2)
        print(f"   送信フレーム: {write_frame.hex().upper()}")
        
        ser.write(write_frame)
        time.sleep(0.1)
        
        if ser.in_waiting > 0:
            response = ser.read(ser.in_waiting)
            print(f"   受信応答: {response.hex().upper()}")
        else:
            print("   応答なし")
        
        # 3. 複数回テスト
        print("\n🔄 複数回送信テスト (RXカウンタ確認)")
        for i in range(3):
            print(f"   テスト {i+1}/3")
            read_frame = create_read_frame(0x1000 + i*4, size=2, length=1)
            print(f"     送信: {read_frame.hex().upper()}")
            
            ser.write(read_frame)
            time.sleep(0.2)
            
            if ser.in_waiting > 0:
                response = ser.read(ser.in_waiting)
                print(f"     応答: {response.hex().upper()}")
            else:
                print("     応答なし")
        
        ser.close()
        print("\n✅ プロトコルテスト完了")
        
    except Exception as e:
        print(f"❌ エラー: {e}")
        import traceback
        traceback.print_exc()

def analyze_frame_format():
    """フレーム形式の解説"""
    print("\n📋 UART-AXIプロトコルフレーム形式")
    print("=" * 50)
    
    # 読み取りフレーム例
    read_frame = create_read_frame(0x1000, size=2, length=1)
    print("📖 読み取りフレーム例:")
    print(f"   バイト列: {read_frame.hex().upper()}")
    print("   構造:")
    print(f"     SOF:  {read_frame[0]:02X} (Start of Frame)")
    print(f"     CMD:  {read_frame[1]:02X} (Read, 32-bit, 1beat)")
    print(f"     ADDR: {read_frame[2]:02X}{read_frame[3]:02X}{read_frame[4]:02X}{read_frame[5]:02X} (0x1000, little-endian)")
    print(f"     CRC:  {read_frame[6]:02X} (CRC-8)")
    
    # 書き込みフレーム例
    write_frame = create_write_frame(0x1000, [0x12345678], size=2)
    print("\n📝 書き込みフレーム例:")
    print(f"   バイト列: {write_frame.hex().upper()}")
    print("   構造:")
    print(f"     SOF:  {write_frame[0]:02X} (Start of Frame)")
    print(f"     CMD:  {write_frame[1]:02X} (Write, 32-bit, 1beat)")
    print(f"     ADDR: {write_frame[2]:02X}{write_frame[3]:02X}{write_frame[4]:02X}{write_frame[5]:02X} (0x1000, little-endian)")
    print(f"     DATA: {write_frame[6]:02X}{write_frame[7]:02X}{write_frame[8]:02X}{write_frame[9]:02X} (0x12345678, little-endian)")
    print(f"     CRC:  {write_frame[10]:02X} (CRC-8)")

def main():
    """メイン関数"""
    print("🚀 UART-AXIプロトコル準拠テストツール")
    print("=" * 70)
    print(f"実行時刻: {time.strftime('%Y-%m-%d %H:%M:%S')}")
    print()
    print("💡 目的: 正しいプロトコルフレームでRXカウンタの動作確認")
    print("   - プロトコル準拠フレームの送信")
    print("   - CRC付きフレームの生成")
    print("   - 応答確認とカウンタ動作検証")
    
    # フレーム形式の解説
    analyze_frame_format()
    
    # プロトコルフレームテスト
    test_protocol_frames("COM3")
    
    print("\n" + "=" * 70)
    print("🎯 期待される結果:")
    print("   📈 RXカウンタが増加 → プロトコル解析成功")
    print("   📥 応答フレーム受信 → 双方向通信成功")
    print("   🔄 parser_frame_valid=1 → フレーム検証成功")
    print("   ✨ rx_transaction_complete=1 → トランザクション完了")
    
    print("\n✨ プロトコルテスト完了")

if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\n\n⏹️  ユーザーによりテストが中断されました")
    except Exception as e:
        print(f"\n❌ 予期しないエラー: {e}")
        import traceback
        traceback.print_exc()