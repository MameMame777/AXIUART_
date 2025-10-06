#!/usr/bin/env python3
"""
Protocol Compliance Test for UART-AXI4-Lite Bridge
==================================================
Tests exact compliance with uart_axi4_protocol.md specification
"""

import serial
import time
import sys

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

def analyze_response(expected_sof, expected_status, response):
    """Analyze response for protocol compliance"""
    print(f"\n📋 Response Analysis:")
    print(f"   Expected SOF: 0x{expected_sof:02X}, Actual: 0x{response[0]:02X} {'✅' if response[0] == expected_sof else '❌'}")
    print(f"   Expected STATUS: 0x{expected_status:02X}, Actual: 0x{response[1]:02X} {'✅' if response[1] == expected_status else '❌'}")
    
    if len(response) >= 3:
        print(f"   CMD Echo: 0x{response[2]:02X}")
    
    if len(response) >= 4:
        actual_crc = response[-1]
        expected_crc = crc8_calculate(response[1:-1])
        print(f"   CRC: Expected 0x{expected_crc:02X}, Actual: 0x{actual_crc:02X} {'✅' if actual_crc == expected_crc else '❌'}")

def test_write_compliance():
    """Test write operation protocol compliance"""
    print("\n🔧 Protocol Compliance Test: Write Operation")
    print("=" * 60)
    
    # Write frame: A5 20 20 10 00 00 78 56 34 12 CRC
    # According to protocol: CMD=0x20 (RW=0, INC=0, SIZE=32bit, LEN=1)
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
    
    print(f"📤 Sending write frame: {format_hex_bytes(frame)}")
    print(f"   SOF: 0xA5 (host→device)")
    print(f"   CMD: 0x{cmd:02X} (Write, 32-bit, 1 beat)")
    print(f"   ADDR: 0x{addr:08X}")
    print(f"   DATA: 0x{data:08X}")
    print(f"   CRC: 0x{crc:02X}")
    
    try:
        ser = serial.Serial('COM3', 115200, timeout=2)
        time.sleep(0.1)
        
        ser.write(frame)
        time.sleep(0.1)
        
        response = ser.read(20)  # Read potential response
        print(f"📥 Received: {format_hex_bytes(response)}")
        
        if len(response) >= 4:
            # Expected: 5A 00 20 CRC (SOF=0x5A, STATUS=0x00, CMD=0x20)
            analyze_response(0x5A, 0x00, response)
        else:
            print("❌ Insufficient response data")
            
        ser.close()
        
    except Exception as e:
        print(f"❌ Communication error: {e}")

def test_read_compliance():
    """Test read operation protocol compliance"""
    print("\n📖 Protocol Compliance Test: Read Operation")
    print("=" * 60)
    
    # Read frame: A5 A0 20 10 00 00 CRC
    # According to protocol: CMD=0xA0 (RW=1, INC=0, SIZE=32bit, LEN=1)
    cmd = 0xA0  # Read, no increment, 32-bit, 1 beat
    addr = 0x00001020
    
    # Construct frame
    frame = bytearray()
    frame.append(0xA5)  # SOF (host→device)
    frame.append(cmd)   # CMD
    # Address (little-endian)
    frame.extend([(addr >>  0) & 0xFF,
                 (addr >>  8) & 0xFF,
                 (addr >> 16) & 0xFF,
                 (addr >> 24) & 0xFF])
    
    # Calculate CRC over CMD through ADDR
    crc = crc8_calculate(frame[1:])
    frame.append(crc)
    
    print(f"📤 Sending read frame: {format_hex_bytes(frame)}")
    print(f"   SOF: 0xA5 (host→device)")
    print(f"   CMD: 0x{cmd:02X} (Read, 32-bit, 1 beat)")
    print(f"   ADDR: 0x{addr:08X}")
    print(f"   CRC: 0x{crc:02X}")
    
    try:
        ser = serial.Serial('COM3', 115200, timeout=2)
        time.sleep(0.1)
        
        ser.write(frame)
        time.sleep(0.1)
        
        response = ser.read(20)  # Read potential response
        print(f"📥 Received: {format_hex_bytes(response)}")
        
        if len(response) >= 12:
            # Expected: 5A 00 A0 20 10 00 00 XX XX XX XX CRC
            # (SOF=0x5A, STATUS=0x00, CMD=0xA0, ADDR, DATA, CRC)
            analyze_response(0x5A, 0x00, response)
            
            # Extract and display data
            if response[1] == 0x00:  # Success status
                data_bytes = response[7:11]
                data_value = (data_bytes[3] << 24) | (data_bytes[2] << 16) | (data_bytes[1] << 8) | data_bytes[0]
                print(f"   Read Data: 0x{data_value:08X}")
        else:
            print("❌ Insufficient response data")
            
        ser.close()
        
    except Exception as e:
        print(f"❌ Communication error: {e}")

def main():
    print("🎯 UART-AXI4-Lite Bridge Protocol Compliance Test")
    print("=" * 60)
    print("Testing exact compliance with uart_axi4_protocol.md")
    print("Expected behavior:")
    print("  - Write response: 5A 00 CMD CRC")
    print("  - Read response: 5A 00 CMD ADDR DATA CRC")
    print("  - SOF: 0x5A (device→host)")
    print("  - STATUS: 0x00 (success)")
    print("  - CMD: Echo original command")
    
    test_write_compliance()
    test_read_compliance()
    
    print("\n🎉 Protocol compliance test completed")
    print("Check for deviations from uart_axi4_protocol.md specification")

if __name__ == "__main__":
    main()