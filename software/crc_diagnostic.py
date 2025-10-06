#!/usr/bin/env python3
"""
CRC Diagnostic Tool for AXIUART
"""

def crc8_debug(data):
    """CRC8計算 (polynomial 0x2F) with debug output"""
    crc = 0x00
    print(f"CRC Input: {' '.join(f'{b:02X}' for b in data)}")
    print(f"Initial CRC: 0x{crc:02X}")
    
    for i, byte in enumerate(data):
        print(f"\nByte {i}: 0x{byte:02X}")
        crc ^= byte
        print(f"  After XOR: 0x{crc:02X}")
        
        for bit in range(8):
            if crc & 0x80:
                crc = (crc << 1) ^ 0x2F
                print(f"    Bit {bit}: MSB=1, shift+XOR: 0x{crc & 0xFF:02X}")
            else:
                crc <<= 1
                print(f"    Bit {bit}: MSB=0, shift: 0x{crc & 0xFF:02X}")
            crc &= 0xFF
    
    print(f"\nFinal CRC: 0x{crc:02X}")
    return crc

def test_crc_cases():
    """Test CRC for common register access cases"""
    print("🔍 CRC Diagnostic for AXIUART Register Access")
    print("=" * 60)
    
    # Test cases from our recent attempts
    test_cases = [
        # Version register read
        ([0xA0, 0x1C, 0x10, 0x00, 0x00], "Version Register Read"),
        # Control register read  
        ([0xA0, 0x00, 0x10, 0x00, 0x00], "Control Register Read"),
        # Test register read
        ([0xA0, 0x20, 0x10, 0x00, 0x00], "Test Register Read"),
    ]
    
    for data, description in test_cases:
        print(f"\n📍 {description}")
        expected_crc = crc8_debug(data)
        
        # Build full frame
        frame = [0xA5] + data + [expected_crc]
        print(f"Complete frame: {' '.join(f'{b:02X}' for b in frame)}")
        print("-" * 50)

if __name__ == "__main__":
    test_crc_cases()