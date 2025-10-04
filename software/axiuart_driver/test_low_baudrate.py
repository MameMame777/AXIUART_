#!/usr/bin/env python3
"""
Low Baudrate FPGA Test
低いボーレートでのFPGA通信テスト
"""

import serial
import time

def test_low_baudrates():
    """低いボーレートでのテスト"""
    baudrates = [9600, 19200, 38400, 57600]
    
    for baud in baudrates:
        print(f"\n🔄 Testing {baud} bps...")
        try:
            ser = serial.Serial(
                port='COM3',
                baudrate=baud,
                timeout=2.0,
                rtscts=False  # フロー制御無効
            )
            
            # 簡単なSOF送信
            print(f"📤 Sending SOF (0x7E)...")
            ser.write(b'\x7E')
            ser.flush()
            time.sleep(0.5)
            
            if ser.in_waiting > 0:
                response = ser.read(ser.in_waiting)
                print(f"✅ Response at {baud}bps: {response.hex()}")
            else:
                print(f"❌ No response at {baud}bps")
                
            ser.close()
            
        except Exception as e:
            print(f"❌ Error at {baud}bps: {e}")

if __name__ == "__main__":
    print("🔍 Low Baudrate FPGA Test")
    print("=" * 30)
    test_low_baudrates()