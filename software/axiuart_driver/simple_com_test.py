#!/usr/bin/env python3
"""
Simple COM Port Connection Test
FPGAとの基本的なCOM接続を検証するためのシンプルなテストツール
"""

import serial
import time
import sys

def test_com_basic():
    """基本的なCOM接続テスト"""
    print("🔌 Basic COM3 Connection Test")
    print("=" * 40)
    
    try:
        # 最小限の設定で接続を試行
        ser = serial.Serial()
        ser.port = 'COM3'
        ser.baudrate = 115200
        ser.bytesize = serial.EIGHTBITS
        ser.parity = serial.PARITY_NONE
        ser.stopbits = serial.STOPBITS_ONE
        ser.timeout = 1
        ser.xonxoff = False
        ser.rtscts = False  # フロー制御を無効
        ser.dsrdtr = False
        
        print(f"📡 Attempting to open COM3...")
        print(f"   Baudrate: {ser.baudrate}")
        print(f"   Data bits: {ser.bytesize}")
        print(f"   Parity: {ser.parity}")
        print(f"   Stop bits: {ser.stopbits}")
        print(f"   RTS/CTS: {ser.rtscts}")
        
        ser.open()
        print("✅ Port opened successfully!")
        
        # ポート情報を表示
        print(f"📋 Port Info:")
        print(f"   Port: {ser.name}")
        print(f"   Is Open: {ser.is_open}")
        print(f"   In Waiting: {ser.in_waiting}")
        print(f"   Out Waiting: {ser.out_waiting}")
        
        # 簡単な書き込みテスト
        print(f"\n📤 Writing test data...")
        test_data = b'\x7E\x01\x00\x00\x10\x1C\x00\x04\x8B\x7F'  # VERSION読み取りコマンド
        ser.write(test_data)
        ser.flush()
        print(f"   Sent {len(test_data)} bytes: {test_data.hex()}")
        
        # 受信待ち
        print(f"\n📥 Waiting for response...")
        time.sleep(0.5)
        
        if ser.in_waiting > 0:
            response = ser.read(ser.in_waiting)
            print(f"✅ Received {len(response)} bytes: {response.hex()}")
        else:
            print("❌ No response received")
            
        ser.close()
        print("🔒 Port closed")
        return True
        
    except serial.SerialException as e:
        print(f"❌ Serial Error: {e}")
        return False
    except Exception as e:
        print(f"❌ General Error: {e}")
        return False

def test_com_with_flowcontrol():
    """フロー制御ありでの接続テスト"""
    print("\n🔌 COM3 Connection Test with Flow Control")
    print("=" * 45)
    
    try:
        ser = serial.Serial(
            port='COM3',
            baudrate=115200,
            bytesize=serial.EIGHTBITS,
            parity=serial.PARITY_NONE,
            stopbits=serial.STOPBITS_ONE,
            timeout=2,
            xonxoff=False,
            rtscts=True,  # フロー制御を有効
            dsrdtr=False
        )
        
        print(f"✅ Port opened with flow control!")
        print(f"   RTS/CTS: {ser.rtscts}")
        
        # DTR/RTSピンの状態確認
        print(f"📋 Control Lines:")
        print(f"   DTR: {ser.dtr}")
        print(f"   RTS: {ser.rts}")
        print(f"   CTS: {ser.cts}")
        print(f"   DSR: {ser.dsr}")
        
        # テストデータ送信
        test_data = b'\x7E\x01\x00\x00\x10\x1C\x00\x04\x8B\x7F'
        ser.write(test_data)
        ser.flush()
        print(f"📤 Sent: {test_data.hex()}")
        
        time.sleep(1)
        
        if ser.in_waiting > 0:
            response = ser.read(ser.in_waiting)
            print(f"📥 Received: {response.hex()}")
        else:
            print("❌ No response")
            
        ser.close()
        return True
        
    except Exception as e:
        print(f"❌ Error: {e}")
        return False

def test_different_baudrates():
    """異なるボーレートでのテスト"""
    print("\n🔌 Multi-Baudrate Connection Test")
    print("=" * 40)
    
    baudrates = [9600, 19200, 38400, 57600, 115200]
    
    for baud in baudrates:
        print(f"\n🔄 Testing {baud} bps...")
        try:
            ser = serial.Serial(
                port='COM3',
                baudrate=baud,
                timeout=0.5,
                rtscts=False
            )
            
            print(f"   ✅ Connected at {baud} bps")
            
            # 簡単なテスト
            ser.write(b'\x7E')  # SOFのみ送信
            time.sleep(0.1)
            
            if ser.in_waiting > 0:
                response = ser.read(ser.in_waiting)
                print(f"   📥 Response: {response.hex()}")
            else:
                print(f"   ❌ No response")
                
            ser.close()
            
        except Exception as e:
            print(f"   ❌ Failed: {e}")

def main():
    """メイン関数"""
    print("🚨 AXIUART FPGA - Simple COM Connection Test")
    print("=" * 50)
    print(f"⏰ Test time: {time.strftime('%Y-%m-%d %H:%M:%S')}")
    print()
    
    # 基本接続テスト
    success1 = test_com_basic()
    
    if success1:
        # フロー制御ありでテスト
        test_com_with_flowcontrol()
        
        # 異なるボーレートでテスト
        test_different_baudrates()
    
    print("\n📊 Test Summary")
    print("=" * 20)
    if success1:
        print("✅ Basic connection: SUCCESS")
        print("💡 FPGA seems to be accessible")
        print("🔧 Next step: Protocol-level debugging")
    else:
        print("❌ Basic connection: FAILED")
        print("💡 Possible issues:")
        print("   - FPGA power/reset")
        print("   - Driver issue")
        print("   - Hardware connection")
        print("   - Port permission")

if __name__ == "__main__":
    main()