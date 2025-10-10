#!/usr/bin/env python3
"""
Basic FPGA Communication Test
Minimal test to identify basic communication issues
"""

import serial
import time
import sys

def test_basic_communication(port='COM3', baudrate=115200):
    """Test basic UART communication with FPGA"""
    try:
        ser = serial.Serial(
            port=port,
            baudrate=baudrate,
            bytesize=serial.EIGHTBITS,
            parity=serial.PARITY_NONE,
            stopbits=serial.STOPBITS_ONE,
            timeout=2.0
        )
        
        print(f"✅ Connected to {port} at {baudrate} baud")
        
        # Clear buffers
        ser.reset_input_buffer()
        ser.reset_output_buffer()
        time.sleep(0.5)
        
        # Test 1: Simple frame transmission
        print("\n🔍 Test 1: Sending simple read frame")
        
        # Simple read frame: SOF(0xA5) + CMD(0x91) + ADDR(0x00001020) + CRC
        simple_frame = bytes([0xA5, 0x91, 0x20, 0x10, 0x00, 0x00, 0xE7])
        
        print(f"📤 Sending: {' '.join(f'0x{b:02X}' for b in simple_frame)}")
        
        ser.write(simple_frame)
        ser.flush()
        
        # Wait for response
        time.sleep(0.5)
        response = ser.read(ser.in_waiting or 16)
        
        print(f"📥 Received {len(response)} bytes: {' '.join(f'0x{b:02X}' for b in response)}")
        
        # Test 2: Check if device responds to any data
        print("\n🔍 Test 2: Sending test pattern")
        test_pattern = bytes([0x55, 0xAA, 0xFF, 0x00])
        
        print(f"📤 Sending: {' '.join(f'0x{b:02X}' for b in test_pattern)}")
        
        ser.write(test_pattern)
        ser.flush()
        
        time.sleep(0.5)
        response2 = ser.read(ser.in_waiting or 16)
        
        print(f"📥 Received {len(response2)} bytes: {' '.join(f'0x{b:02X}' for b in response2)}")
        
        # Test 3: Check for continuous data
        print("\n🔍 Test 3: Checking for continuous data stream")
        time.sleep(1.0)
        continuous_data = ser.read(ser.in_waiting or 32)
        
        if continuous_data:
            print(f"📥 Continuous data {len(continuous_data)} bytes: {' '.join(f'0x{b:02X}' for b in continuous_data)}")
        else:
            print("📥 No continuous data detected")
        
        # Analysis
        print("\n📊 Analysis:")
        if response:
            if response[0] == 0xAD:
                print("🚨 Response starts with 0xAD - possible protocol mismatch")
            elif response[0] == 0x5A:
                print("✅ Response starts with 0x5A - correct response SOF")
            else:
                print(f"⚠️  Unexpected response SOF: 0x{response[0]:02X}")
        
        if len(response) == 4 and all(b == response[0] for b in response[1:3]):
            print("🔍 Response pattern suggests fixed/error pattern")
        
        ser.close()
        print("🔌 Disconnected")
        
        return len(response) > 0
        
    except Exception as e:
        print(f"❌ Error: {e}")
        return False

def main():
    port = sys.argv[1] if len(sys.argv) > 1 else 'COM3'
    
    print("🚀 === Basic FPGA Communication Test ===")
    print(f"🎯 Testing basic UART communication on {port}")
    
    success = test_basic_communication(port)
    
    if success:
        print("\n✅ Communication established, but protocol may be mismatched")
    else:
        print("\n❌ No communication detected")

if __name__ == "__main__":
    main()