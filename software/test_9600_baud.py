#!/usr/bin/env python3
"""
9600 Baud Protocol Test for 9600 baud FPGA Configuration
======================================================
"""

import serial
import time

def crc8_calculate(data):
    """Calculate CRC8 with polynomial 0x07"""
    crc = 0x00
    for byte in data:
        crc ^= byte
        for _ in range(8):
            if crc & 0x80:
                crc = ((crc << 1) ^ 0x07) & 0xFF
            else:
                crc = (crc << 1) & 0xFF
    return crc

def format_hex_bytes(data):
    """Format bytes for display"""
    return ' '.join(f'{b:02X}' for b in data)

def test_9600_baud():
    """Test protocol at 9600 baud specifically"""
    print("🎯 9600 Baud Protocol Test")
    print("=" * 50)
    
    try:
        ser = serial.Serial('COM3', 9600, timeout=5)
        time.sleep(1)  # Longer settling time
        
        print("✅ Connected to COM3 at 9600 baud")
        
        # Test write command
        cmd = 0x20  # Write, no increment, 32-bit, 1 beat
        addr = 0x00001020
        data = 0x12345678
        
        # Construct frame
        frame = bytearray()
        frame.append(0xA5)  # SOF (host→device)
        frame.append(cmd)   # CMD
        # Address (little-endian)
        frame.extend([(addr >>  0) & 0xFF,
                     (addr >>  8) & 0xFF,
                     (addr >> 16) & 0xFF,
                     (addr >> 24) & 0xFF])
        # Data (little-endian)
        frame.extend([(data >>  0) & 0xFF,
                     (data >>  8) & 0xFF,
                     (data >> 16) & 0xFF,
                     (data >> 24) & 0xFF])
        
        # Calculate CRC over CMD through DATA
        crc = crc8_calculate(frame[1:])
        frame.append(crc)
        
        print(f"📤 Sending: {format_hex_bytes(frame)}")
        
        ser.flushInput()
        ser.flushOutput()
        
        # Send byte by byte with delays
        for i, byte_val in enumerate(frame):
            ser.write(bytes([byte_val]))
            time.sleep(0.02)  # 20ms between bytes
            print(f"   Byte {i+1}: 0x{byte_val:02X}")
        
        print("⏳ Waiting for response...")
        time.sleep(2.0)
        
        response = ser.read(20)
        print(f"📥 Received: {format_hex_bytes(response)} ({len(response)} bytes)")
        
        if len(response) >= 4:
            print(f"\n📋 Detailed Analysis:")
            print(f"   SOF: 0x{response[0]:02X} (expected 0x5A)")
            print(f"   STATUS: 0x{response[1]:02X} (expected 0x00)")
            print(f"   CMD_ECHO: 0x{response[2]:02X} (expected 0x20)")
            print(f"   CRC: 0x{response[3]:02X}")
            
            # Analyze the pattern
            if response[2] == 0x40:
                print(f"\n🔍 Pattern Analysis:")
                print(f"   0x20 → 0x40: This is 0x20 << 1 (left shift by 1)")
                print(f"   Binary: 00100000 → 01000000")
                print(f"   Possible bit manipulation in RTL!")
        
        # Test read command
        print(f"\n📖 Testing Read Command:")
        cmd = 0xA0  # Read, no increment, 32-bit, 1 beat
        addr = 0x00001020
        
        frame = bytearray()
        frame.append(0xA5)  # SOF (host→device)
        frame.append(cmd)   # CMD
        # Address (little-endian)
        frame.extend([(addr >>  0) & 0xFF,
                     (addr >>  8) & 0xFF,
                     (addr >> 16) & 0xFF,
                     (addr >> 24) & 0xFF])
        
        crc = crc8_calculate(frame[1:])
        frame.append(crc)
        
        print(f"📤 Sending: {format_hex_bytes(frame)}")
        
        ser.flushInput()
        ser.flushOutput()
        
        for byte_val in frame:
            ser.write(bytes([byte_val]))
            time.sleep(0.02)
        
        time.sleep(2.0)
        
        response = ser.read(20)
        print(f"📥 Received: {format_hex_bytes(response)} ({len(response)} bytes)")
        
        if len(response) >= 3:
            print(f"\n📋 Read Response Analysis:")
            print(f"   SOF: 0x{response[0]:02X} (expected 0x5A)")
            print(f"   STATUS: 0x{response[1]:02X} (expected 0x00)")
            if len(response) >= 3:
                print(f"   CMD_ECHO: 0x{response[2]:02X} (expected 0xA0)")
                if response[2] != 0xA0:
                    print(f"   0xA0 → 0x{response[2]:02X}: Pattern analysis needed")
        
        ser.close()
        
    except Exception as e:
        print(f"❌ Error: {e}")

if __name__ == "__main__":
    test_9600_baud()