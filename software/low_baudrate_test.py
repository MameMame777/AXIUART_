#!/usr/bin/env python3
"""
Low Baud Rate Protocol Test for Physical Layer Verification
=========================================================
Tests protocol at various low baud rates to isolate physical layer issues
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

def test_protocol_at_baud(baud_rate):
    """Test protocol compliance at specific baud rate"""
    print(f"\n🔧 Testing Protocol at {baud_rate} baud")
    print("=" * 50)
    
    try:
        # Try to connect at specified baud rate
        ser = serial.Serial('COM3', baud_rate, timeout=5)
        time.sleep(0.5)  # Longer settling time for low baud rates
        
        print(f"✅ Connected to COM3 at {baud_rate} baud")
        
        # Test simple write command
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
        
        # Clear any pending data
        ser.flushInput()
        ser.flushOutput()
        
        # Send frame byte by byte with longer delays for low baud rates
        if baud_rate <= 19200:
            # Send byte by byte with delays for very low baud rates
            for i, byte_val in enumerate(frame):
                ser.write(bytes([byte_val]))
                time.sleep(0.01)  # 10ms between bytes
                print(f"   Byte {i+1}: 0x{byte_val:02X}")
        else:
            # Send all at once for higher baud rates
            ser.write(frame)
        
        # Wait longer for response at low baud rates
        wait_time = max(2.0, 11.0 / baud_rate * len(frame) * 8 * 2)  # 2x theoretical time
        print(f"⏳ Waiting {wait_time:.1f}s for response...")
        time.sleep(wait_time)
        
        # Read response
        response = ser.read(20)
        print(f"📥 Received: {format_hex_bytes(response)} ({len(response)} bytes)")
        
        if len(response) == 0:
            print("❌ No response received")
            return False
        
        # Analyze response
        print(f"\n📋 Analysis at {baud_rate} baud:")
        if len(response) >= 1:
            print(f"   SOF: 0x{response[0]:02X} (expected 0x5A, actual {'✅' if response[0] == 0x5A else '❌'})")
        if len(response) >= 2:
            print(f"   STATUS: 0x{response[1]:02X} (expected 0x00, actual {'✅' if response[1] == 0x00 else '❌'})")
        if len(response) >= 3:
            print(f"   CMD_ECHO: 0x{response[2]:02X} (expected 0x20, actual {'✅' if response[2] == 0x20 else '❌'})")
        if len(response) >= 4:
            actual_crc = response[-1]
            if len(response) == 4:  # Write response format
                expected_crc = crc8_calculate(response[1:-1])
                print(f"   CRC: 0x{actual_crc:02X} (expected 0x{expected_crc:02X}, {'✅' if actual_crc == expected_crc else '❌'})")
        
        # Check if this baud rate gives better results
        success = (len(response) >= 4 and 
                  response[0] == 0x5A and 
                  response[1] == 0x00 and 
                  response[2] == 0x20)
        
        if success:
            print(f"🎉 Protocol compliance achieved at {baud_rate} baud!")
        else:
            print(f"❌ Protocol violations remain at {baud_rate} baud")
            
        ser.close()
        return success
        
    except Exception as e:
        print(f"❌ Error at {baud_rate} baud: {e}")
        return False

def test_read_at_baud(baud_rate):
    """Test read operation at specific baud rate"""
    print(f"\n📖 Testing Read at {baud_rate} baud")
    print("=" * 40)
    
    try:
        ser = serial.Serial('COM3', baud_rate, timeout=5)
        time.sleep(0.5)
        
        # Read command
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
        
        print(f"📤 Sending: {format_hex_bytes(frame)}")
        
        ser.flushInput()
        ser.flushOutput()
        
        if baud_rate <= 19200:
            for byte_val in frame:
                ser.write(bytes([byte_val]))
                time.sleep(0.01)
        else:
            ser.write(frame)
        
        wait_time = max(2.0, 12.0 / baud_rate * len(frame) * 8 * 2)
        time.sleep(wait_time)
        
        response = ser.read(20)
        print(f"📥 Received: {format_hex_bytes(response)} ({len(response)} bytes)")
        
        success = len(response) >= 8 and response[0] == 0x5A and response[1] == 0x00
        if success:
            print(f"🎉 Read response looks correct at {baud_rate} baud!")
        
        ser.close()
        return success
        
    except Exception as e:
        print(f"❌ Read error at {baud_rate} baud: {e}")
        return False

def main():
    print("🐌 Low Baud Rate Physical Layer Test")
    print("=" * 60)
    print("Testing protocol at progressively lower baud rates")
    print("to isolate physical layer timing issues")
    
    # Test baud rates from very low to normal
    baud_rates = [9600, 19200, 38400, 57600, 115200]
    
    print(f"\n🎯 Testing write operations at different baud rates:")
    
    successful_rates = []
    
    for baud_rate in baud_rates:
        success = test_protocol_at_baud(baud_rate)
        if success:
            successful_rates.append(baud_rate)
            
        time.sleep(1)  # Pause between tests
    
    print(f"\n📊 Results Summary:")
    print("=" * 40)
    
    if successful_rates:
        print(f"✅ Successful baud rates: {successful_rates}")
        print("🎯 Physical layer appears functional at these rates")
        
        # Test read operation at the best rate
        best_rate = successful_rates[0]
        print(f"\n🔍 Testing read operation at best rate ({best_rate}):")
        test_read_at_baud(best_rate)
        
    else:
        print("❌ No baud rates achieved protocol compliance")
        print("🔍 This suggests the issue is NOT physical layer timing")
        print("🎯 Problem likely in RTL protocol implementation")
    
    print(f"\n🎉 Low baud rate testing completed")
    print("This helps isolate physical vs. protocol layer issues")

if __name__ == "__main__":
    main()