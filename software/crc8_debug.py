#!/usr/bin/env python3
"""
CRC8 Debug Script - Step by step calculation
"""

def crc8_bitwise_debug(data):
    """Debug version with step-by-step trace"""
    print(f"Input data: {' '.join(f'{b:02X}' for b in data)}")
    crc = 0x00
    print(f"Initial CRC: 0x{crc:02X}")
    
    for byte_idx, byte in enumerate(data):
        print(f"\nByte {byte_idx}: 0x{byte:02X}")
        crc ^= byte
        print(f"After XOR: 0x{crc:02X}")
        
        for bit in range(8):
            if crc & 0x80:
                crc = ((crc << 1) ^ 0x07) & 0xFF
                print(f"  Bit {bit}: MSB=1, shifted+XOR -> 0x{crc:02X}")
            else:
                crc = (crc << 1) & 0xFF
                print(f"  Bit {bit}: MSB=0, shifted -> 0x{crc:02X}")
    
    print(f"\nFinal CRC: 0x{crc:02X}")
    return crc

def test_simple_cases():
    """Test simple cases first"""
    print("=== Testing Simple Cases ===")
    
    # Test case 1: Single byte 0x21
    print("\n1. Single byte 0x21 (expected: 0x21)")
    result = crc8_bitwise_debug([0x21])
    print(f"Result: 0x{result:02X}, Expected: 0x21, {'PASS' if result == 0x21 else 'FAIL'}")
    
    # Test case 2: All zeros
    print("\n2. All zeros (expected: 0x00)")
    result = crc8_bitwise_debug([0x00, 0x00, 0x00, 0x00])
    print(f"Result: 0x{result:02X}, Expected: 0x00, {'PASS' if result == 0x00 else 'FAIL'}")
    
    # Test case 3: All ones
    print("\n3. All ones (expected: 0xFF)")
    result = crc8_bitwise_debug([0xFF, 0xFF, 0xFF, 0xFF])
    print(f"Result: 0x{result:02X}, Expected: 0xFF, {'PASS' if result == 0xFF else 'FAIL'}")

if __name__ == "__main__":
    test_simple_cases()