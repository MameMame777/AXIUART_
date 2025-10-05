#!/usr/bin/env python3
"""
CRC8 Alternative Implementation Test
Testing different interpretations of CRC8 with polynomial 0x07
"""

def crc8_table_driven():
    """Generate CRC8 table for polynomial 0x07"""
    table = [0] * 256
    
    for i in range(256):
        crc = i
        for _ in range(8):
            if crc & 0x80:
                crc = ((crc << 1) ^ 0x07) & 0xFF
            else:
                crc = (crc << 1) & 0xFF
        table[i] = crc
    
    return table

def crc8_with_table(data, table):
    """Calculate CRC8 using lookup table"""
    crc = 0x00
    for byte in data:
        crc = table[crc ^ byte]
    return crc

def crc8_reflected_polynomial(data):
    """Try with reflected polynomial (bit-reversed 0x07 = 0xE0)"""
    crc = 0x00
    
    for byte in data:
        crc ^= byte
        for _ in range(8):
            if crc & 0x01:  # Check LSB instead of MSB
                crc = (crc >> 1) ^ 0xE0  # Shifted right with reflected poly
            else:
                crc = crc >> 1
    
    return crc

def crc8_different_init(data, init_val=0xFF):
    """Try with different initial value"""
    crc = init_val
    
    for byte in data:
        crc ^= byte
        for _ in range(8):
            if crc & 0x80:
                crc = ((crc << 1) ^ 0x07) & 0xFF
            else:
                crc = (crc << 1) & 0xFF
    
    return crc

def test_single_byte_21():
    """Focus on the single byte 0x21 test case"""
    print("=== Testing Single Byte 0x21 (Expected: 0x21) ===")
    
    data = [0x21]
    
    # Method 1: Table-driven
    table = crc8_table_driven()
    result1 = crc8_with_table(data, table)
    print(f"Table-driven:     0x{result1:02X}")
    
    # Method 2: Reflected polynomial
    result2 = crc8_reflected_polynomial(data)
    print(f"Reflected poly:   0x{result2:02X}")
    
    # Method 3: Different initial values
    for init in [0x00, 0xFF, 0x21]:
        result3 = crc8_different_init(data, init)
        print(f"Init 0x{init:02X}:        0x{result3:02X}")
    
    print(f"Expected:         0x21")
    
    # Check if any match
    results = [result1, result2]
    results.extend([crc8_different_init(data, init) for init in [0x00, 0xFF, 0x21]])
    
    if 0x21 in results:
        print("✅ Found matching implementation!")
        for i, result in enumerate(results):
            if result == 0x21:
                methods = ["Table-driven", "Reflected poly", "Init 0x00", "Init 0xFF", "Init 0x21"]
                print(f"   -> {methods[i]} gives correct result")
    else:
        print("❌ No implementation matches expected result")

if __name__ == "__main__":
    test_single_byte_21()
    
    # Print table for analysis
    print("\n=== CRC8 Table (first 16 entries) ===")
    table = crc8_table_driven()
    for i in range(16):
        print(f"table[0x{i:02X}] = 0x{table[i]:02X}")