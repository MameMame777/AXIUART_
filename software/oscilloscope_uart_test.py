#!/usr/bin/env python3
"""
Oscilloscope UART Signal Measurement Support Tool
Phase 5: Physical Layer Investigation

This tool generates specific test patterns for oscilloscope analysis
of UART TX signals from the FPGA, helping to verify signal integrity
and identify the root cause of the 0x20→0x48 conversion issue.
"""

import serial
import time
import struct
from datetime import datetime

class OscilloscopeTestPatterns:
    """Generate controlled test patterns for oscilloscope analysis"""
    
    def __init__(self, port="COM3", baudrate=115200):
        self.port = port
        self.baudrate = baudrate
        self.serial = None
        
        # Known patterns for easy oscilloscope identification
        self.test_patterns = {
            'target_byte': 0x20,        # The problematic byte
            'alternating': 0xAA,        # 10101010 - easy to see on scope
            'all_ones': 0xFF,           # 11111111 - maximum high time
            'all_zeros': 0x00,          # 00000000 - maximum low time
            'walking_ones': [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80],
            'uart_frame_markers': [0x55, 0x7E, 0xAA, 0xFF]  # Distinctive patterns
        }
    
    def connect(self):
        """Connect to UART for test pattern generation"""
        try:
            self.serial = serial.Serial(
                port=self.port,
                baudrate=self.baudrate,
                bytesize=8,
                parity='N',
                stopbits=1,
                timeout=1.0
            )
            time.sleep(0.1)
            print(f"✅ Connected to {self.port} at {self.baudrate} baud")
            print(f"📡 Ready for oscilloscope measurement")
            return True
        except Exception as e:
            print(f"❌ Connection failed: {e}")
            return False
    
    def disconnect(self):
        """Disconnect from UART"""
        if self.serial and self.serial.is_open:
            self.serial.close()
            print("🔌 Disconnected")
    
    def crc8_calculate(self, data):
        """Calculate CRC8 for protocol frames"""
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
    
    def build_test_frame(self, test_byte):
        """Build a protocol frame containing the test byte"""
        # Use READ command to REG_VERSION (0x0000101C) 
        # This should generate a response containing our test pattern
        sof = 0xA5
        cmd = 0xA0  # READ command
        addr = 0x0000101C  # VERSION register
        
        # Build frame: SOF + CMD + ADDR (little-endian) + CRC
        frame_data = [sof, cmd]
        frame_data.extend([
            addr & 0xFF,
            (addr >> 8) & 0xFF,
            (addr >> 16) & 0xFF,
            (addr >> 24) & 0xFF
        ])
        
        # Calculate CRC (exclude SOF)
        crc = self.crc8_calculate(frame_data[1:])
        frame_data.append(crc)
        
        return frame_data
    
    def send_pattern_burst(self, pattern_name, byte_value, count=10, delay=1.0):
        """Send a burst of identical patterns for scope analysis"""
        print(f"\n📡 Sending {pattern_name} pattern: 0x{byte_value:02X}")
        print(f"   Binary: {byte_value:08b}")
        print(f"   Count: {count} frames, {delay}s interval")
        print(f"🔬 **TRIGGER OSCILLOSCOPE NOW**")
        
        time.sleep(2.0)  # Give time to arm oscilloscope
        
        for i in range(count):
            if pattern_name == "protocol_frame":
                # Send proper protocol frame
                frame = self.build_test_frame(byte_value)
                self.serial.write(bytes(frame))
                print(f"   Frame {i+1}: {' '.join(f'0x{b:02X}' for b in frame)}")
            else:
                # Send raw byte
                self.serial.write(bytes([byte_value]))
                print(f"   Byte {i+1}: 0x{byte_value:02X}")
            
            self.serial.flush()
            time.sleep(delay)
        
        print(f"✅ Pattern burst complete")
    
    def continuous_pattern(self, byte_value, duration=30.0):
        """Send continuous pattern for long-term scope analysis"""
        print(f"\n📡 Continuous pattern: 0x{byte_value:02X} for {duration}s")
        print(f"🔬 **SET OSCILLOSCOPE TO CONTINUOUS MODE**")
        
        start_time = time.time()
        count = 0
        
        while (time.time() - start_time) < duration:
            self.serial.write(bytes([byte_value]))
            self.serial.flush()
            count += 1
            time.sleep(0.1)  # 10 bytes/second
        
        print(f"✅ Sent {count} bytes over {duration}s")
    
    def critical_byte_analysis(self):
        """Focused analysis of the problematic 0x20 byte"""
        print(f"\n🎯 Critical Byte Analysis: 0x20")
        print("=" * 50)
        print(f"Target: 0x20 = {0x20:08b}")
        print(f"Reported received: 0x48 = {0x48:08b}")
        print(f"XOR difference: 0x{0x20^0x48:02X} = {0x20^0x48:08b}")
        
        print(f"\n📋 Test Sequence:")
        print(f"1. Single 0x20 byte (10 times)")
        print(f"2. Alternating 0x20/0xAA (reference)")
        print(f"3. Protocol frame with 0x20")
        print(f"4. Continuous 0x20 stream")
        
        input("Press Enter when oscilloscope is ready...")
        
        # Test 1: Single bytes
        self.send_pattern_burst("single_0x20", 0x20, count=10, delay=2.0)
        
        time.sleep(3.0)
        
        # Test 2: Alternating with reference
        print(f"\n📡 Alternating 0x20/0xAA reference pattern")
        for i in range(5):
            self.serial.write(bytes([0x20]))
            time.sleep(0.5)
            self.serial.write(bytes([0xAA]))
            time.sleep(0.5)
        
        time.sleep(3.0)
        
        # Test 3: Protocol frame
        self.send_pattern_burst("protocol_frame", 0x20, count=5, delay=3.0)
        
        time.sleep(3.0)
        
        # Test 4: Continuous stream
        input("Press Enter for continuous 0x20 stream (30s)...")
        self.continuous_pattern(0x20, duration=30.0)
    
    def comprehensive_signal_test(self):
        """Complete signal integrity test suite"""
        print(f"\n🔬 Comprehensive Signal Integrity Test")
        print("=" * 60)
        print(f"Time: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        
        test_sequence = [
            ("UART Sync Pattern", 0x55, "01010101 - Basic timing"),
            ("All Ones", 0xFF, "11111111 - Maximum high"),
            ("All Zeros", 0x00, "00000000 - Maximum low"),
            ("Target Byte", 0x20, "00100000 - Problem byte"),
            ("Received Byte", 0x48, "01001000 - What PC sees"),
            ("Alternating", 0xAA, "10101010 - Reference"),
        ]
        
        for name, value, description in test_sequence:
            print(f"\n📡 Test: {name}")
            print(f"   Value: 0x{value:02X} = {value:08b}")
            print(f"   Note: {description}")
            input("   Press Enter when ready...")
            
            self.send_pattern_burst(name.lower().replace(" ", "_"), value, count=5, delay=2.0)
            time.sleep(2.0)
        
        print(f"\n✅ Comprehensive test complete")
    
    def baud_rate_verification(self):
        """Test for baud rate accuracy"""
        print(f"\n⏱️ Baud Rate Verification Test")
        print("=" * 40)
        print(f"Target: 115200 baud = 8.68 μs per bit")
        print(f"Frame: Start + 8 data + Stop = 10 bits = 86.8 μs")
        
        input("Set oscilloscope timebase to 20μs/div, trigger on falling edge...")
        
        # Send bytes with known timing
        test_byte = 0x55  # Alternating pattern for easy measurement
        print(f"Sending 0x{test_byte:02X} for timing measurement...")
        
        for i in range(10):
            print(f"Byte {i+1}")
            self.serial.write(bytes([test_byte]))
            self.serial.flush()
            time.sleep(1.0)  # 1 second between frames
        
        print(f"✅ Timing test complete")
        print(f"💡 Measure bit width on oscilloscope")
        print(f"   Expected: 8.68 μs ± 1%")
    
    def run_oscilloscope_tests(self):
        """Main test sequence for oscilloscope analysis"""
        print("🔬 Oscilloscope UART Signal Analysis")
        print("=" * 60)
        print(f"Phase 5: Physical Layer Investigation")
        print(f"Objective: Identify 0x20→0x48 conversion point")
        
        if not self.connect():
            return False
        
        try:
            print(f"\n📋 Test Menu:")
            print(f"1. Critical Byte Analysis (0x20 focus)")
            print(f"2. Comprehensive Signal Test")
            print(f"3. Baud Rate Verification")
            print(f"4. Custom Pattern")
            
            choice = input("\nSelect test (1-4): ").strip()
            
            if choice == "1":
                self.critical_byte_analysis()
            elif choice == "2":
                self.comprehensive_signal_test()
            elif choice == "3":
                self.baud_rate_verification()
            elif choice == "4":
                byte_val = int(input("Enter byte value (hex, e.g., 0x20): "), 16)
                count = int(input("Enter repeat count: "))
                self.send_pattern_burst("custom", byte_val, count, delay=2.0)
            else:
                print("Invalid choice")
                return False
            
            return True
            
        finally:
            self.disconnect()

def main():
    """Main execution"""
    print("🎯 Oscilloscope UART TX Signal Analysis Tool")
    print("Phase 5: Physical Layer Investigation")
    print("=" * 60)
    
    tester = OscilloscopeTestPatterns()
    
    print(f"\n📋 Pre-measurement Checklist:")
    print(f"✅ FPGA programmed with latest bitstream")
    print(f"✅ Oscilloscope probe connected to UART TX (JA1 pin 2)")
    print(f"✅ Oscilloscope set to 3.3V range")
    print(f"✅ Trigger configured for falling edge")
    print(f"✅ Timebase appropriate for 115200 baud")
    
    proceed = input(f"\nProceed with measurement? (y/n): ")
    if proceed.lower() == 'y':
        success = tester.run_oscilloscope_tests()
        if success:
            print(f"\n🎉 Oscilloscope test completed")
            print(f"📊 Analyze captured waveforms for:")
            print(f"   - Signal levels (0V/3.3V)")
            print(f"   - Bit timing (8.68 μs)")
            print(f"   - Pattern integrity (0x20 vs 0x48)")
            print(f"   - Jitter and signal quality")
        else:
            print(f"\n❌ Test failed")
    else:
        print(f"Test cancelled")

if __name__ == "__main__":
    main()