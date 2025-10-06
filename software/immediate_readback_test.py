#!/usr/bin/env python3
"""
FPGA 書き込み直後の即時読み出しテスト
"""

import serial
import time
import struct

# Protocol constants (updated for current FPGA behavior)
SOF_HOST_TO_DEVICE = 0xA5
SOF_DEVICE_TO_HOST_ACTUAL = 0xAD  # Current FPGA implementation
CMD_READ = 0xA0
CMD_WRITE = 0x20
STATUS_OK_ACTUAL = 0x80  # Current FPGA implementation

def calculate_crc8(data: bytes) -> int:
    """Calculate CRC8 with polynomial 0x07"""
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

def send_command(ser: serial.Serial, cmd: int, addr: int, data: int = None) -> bytes:
    """Send UART command and receive response"""
    # Build command frame
    frame = bytearray()
    frame.append(SOF_HOST_TO_DEVICE)
    frame.append(cmd)
    frame.extend(struct.pack('<I', addr))  # Address (little-endian)
    
    if data is not None:  # Write command
        frame.extend(struct.pack('<I', data))  # Data (little-endian)
    
    # Calculate and append CRC
    crc = calculate_crc8(frame[1:])  # Exclude SOF
    frame.append(crc)
    
    # Send frame
    print(f"📤 送信: {' '.join([f'{b:02X}' for b in frame])}")
    ser.write(frame)
    time.sleep(0.05)  # Short delay
    
    # Receive response
    response = bytearray()
    for _ in range(20):  # Wait up to 2 seconds
        if ser.in_waiting > 0:
            response.extend(ser.read(ser.in_waiting))
            if cmd == CMD_READ and len(response) >= 8:
                break
            elif cmd == CMD_WRITE and len(response) >= 4:
                break
        time.sleep(0.05)
    
    print(f"📥 受信: {' '.join([f'{b:02X}' for b in response])}")
    return bytes(response)

def write_register(ser: serial.Serial, addr: int, value: int) -> bool:
    """Write to register"""
    response = send_command(ser, CMD_WRITE, addr, value)
    if response and len(response) >= 4:
        if response[0] == SOF_DEVICE_TO_HOST_ACTUAL and response[1] == STATUS_OK_ACTUAL:
            print(f"✅ 書き込み成功: 0x{addr:08X} = 0x{value:08X}")
            return True
    print(f"❌ 書き込み失敗: 0x{addr:08X} = 0x{value:08X}")
    return False

def read_register(ser: serial.Serial, addr: int) -> int:
    """Read from register"""
    response = send_command(ser, CMD_READ, addr)
    if response and len(response) >= 8:
        if response[0] == SOF_DEVICE_TO_HOST_ACTUAL and response[1] == STATUS_OK_ACTUAL:
            # Extract data from response (bytes 3-6 in little-endian)
            data_bytes = response[3:7]
            value = struct.unpack('<I', data_bytes)[0]
            print(f"✅ 読み出し成功: 0x{addr:08X} = 0x{value:08X}")
            return value
    print(f"❌ 読み出し失敗: 0x{addr:08X}")
    return None

def test_immediate_readback(ser: serial.Serial, addr: int, test_value: int):
    """Test immediate readback after write"""
    print(f"\n🔬 即時読み戻しテスト: 0x{addr:08X}")
    print("-" * 40)
    
    # Read initial value
    print("1️⃣ 書き込み前の読み出し:")
    initial = read_register(ser, addr)
    
    # Write test value
    print(f"\n2️⃣ テスト値の書き込み (0x{test_value:08X}):")
    write_success = write_register(ser, addr, test_value)
    
    # Immediate readback (no delay)
    print("\n3️⃣ 即座に読み出し (遅延なし):")
    immediate = read_register(ser, addr)
    
    # Delayed readback
    time.sleep(0.1)
    print("\n4️⃣ 遅延後の読み出し (100ms後):")
    delayed = read_register(ser, addr)
    
    # Analysis
    print("\n📊 結果分析:")
    if initial is not None and immediate is not None and delayed is not None:
        print(f"   初期値:     0x{initial:08X}")
        print(f"   即時読み出し: 0x{immediate:08X}")
        print(f"   遅延読み出し: 0x{delayed:08X}")
        
        if immediate == test_value:
            print("   ✅ 即時読み戻し成功 - 書き込み処理は正常")
        elif delayed == test_value:
            print("   ⚠️  遅延読み戻し成功 - タイミング問題の可能性")
        elif immediate == initial and delayed == initial:
            print("   ❌ 書き込み処理が実行されていない")
        else:
            print("   🔍 予期しないパターン - 詳細調査が必要")
            
        if immediate != delayed:
            print("   ⚠️  即時と遅延で異なる値 - タイミング依存の問題")
        else:
            print("   ✅ 即時と遅延で同じ値 - タイミング問題なし")

def main():
    """メイン関数"""
    print("🔬 FPGA 書き込み直後の即時読み出しテスト")
    print("=" * 60)
    
    try:
        ser = serial.Serial("COM3", 115200, timeout=1)
        time.sleep(0.1)
        print("✅ COM3に接続しました\n")
        
        # Test only one register with a unique value
        test_addr = 0x00001020
        test_value = 0xA5A5A5A5
        
        test_immediate_readback(ser, test_addr, test_value)
        
        # Additional test with different value
        test_value2 = 0x5A5A5A5A
        test_immediate_readback(ser, test_addr, test_value2)
        
        ser.close()
        print("\n🔌 UART接続を終了しました")
        
    except Exception as e:
        print(f"❌ エラー: {e}")

if __name__ == "__main__":
    main()