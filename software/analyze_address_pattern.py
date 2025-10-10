#!/usr/bin/env python3
"""
Address-Pattern Relationship Analysis for 0xF02022XX pattern
"""

def analyze_address_pattern():
    """Analyze the relationship between addresses and pattern values"""
    
    # Observed data
    test_data = [
        {'addr': 0x1020, 'pattern': 0xF0202248, 'last_byte': 0x48},
        {'addr': 0x1024, 'pattern': 0xF0202249, 'last_byte': 0x49},
        {'addr': 0x1028, 'pattern': 0xF020224A, 'last_byte': 0x4A},
        {'addr': 0x102C, 'pattern': 0xF020224B, 'last_byte': 0x4B},
    ]
    
    print("=== Address-Pattern Relationship Analysis ===\n")
    
    print("1. Basic Pattern Structure:")
    print("   Fixed part: 0xF02022")
    print("   Variable part: Last byte (0x48, 0x49, 0x4A, 0x4B)")
    print()
    
    print("2. Address vs Last Byte Analysis:")
    print("   Address   Last Byte   Address LSB   Difference")
    print("   -------   ---------   -----------   ----------")
    
    for i, data in enumerate(test_data):
        addr_lsb = data['addr'] & 0xFF
        diff = data['last_byte'] - addr_lsb
        print(f"   0x{data['addr']:04X}    0x{data['last_byte']:02X}        0x{addr_lsb:02X}        {diff:+3d} (0x{diff:02X})")
    
    print()
    
    print("3. Pattern Increment Analysis:")
    print("   Address   Last Byte   Increment from previous")
    print("   -------   ---------   ----------------------")
    
    for i, data in enumerate(test_data):
        if i == 0:
            print(f"   0x{data['addr']:04X}    0x{data['last_byte']:02X}        -- (base)")
        else:
            prev_byte = test_data[i-1]['last_byte']
            increment = data['last_byte'] - prev_byte
            addr_increment = data['addr'] - test_data[i-1]['addr']
            print(f"   0x{data['addr']:04X}    0x{data['last_byte']:02X}        +{increment} (addr +0x{addr_increment:X})")
    
    print()
    
    print("4. ASCII Character Analysis:")
    print("   Last Byte   ASCII   Character")
    print("   ---------   -----   ---------")
    
    for data in test_data:
        ascii_char = chr(data['last_byte']) if 32 <= data['last_byte'] <= 126 else '?'
        print(f"   0x{data['last_byte']:02X}        {data['last_byte']:3d}   '{ascii_char}'")
    
    print()
    
    print("5. Register Block Address Mapping (from Register_Block.sv):")
    print("   REG_TEST_0 = 0x020  (BASE_ADDR + 0x020 = 0x1000 + 0x020 = 0x1020)")
    print("   REG_TEST_1 = 0x024  (BASE_ADDR + 0x024 = 0x1000 + 0x024 = 0x1024)")
    print("   REG_TEST_2 = 0x028  (BASE_ADDR + 0x028 = 0x1000 + 0x028 = 0x1028)")
    print("   REG_TEST_3 = 0x02C  (BASE_ADDR + 0x02C = 0x1000 + 0x02C = 0x102C)")
    
    print()
    
    print("6. Hypothesis - Address Offset Correlation:")
    print("   Register offset from BASE_ADDR vs Last Byte:")
    
    base_addr = 0x1000
    for data in test_data:
        offset = data['addr'] - base_addr
        correlation = data['last_byte'] - offset
        print(f"   Offset 0x{offset:03X} -> Last Byte 0x{data['last_byte']:02X} (difference: 0x{correlation:02X} = {correlation})")
    
    print()
    
    # Check if there's a simple mathematical relationship
    constant_diff = test_data[0]['last_byte'] - (test_data[0]['addr'] - base_addr)
    print(f"7. Mathematical Relationship Check:")
    print(f"   If Last Byte = Address Offset + Constant:")
    print(f"   Constant = 0x{constant_diff:02X} ({constant_diff})")
    
    print("\n   Verification:")
    all_match = True
    for data in test_data:
        offset = data['addr'] - base_addr
        predicted = offset + constant_diff
        actual = data['last_byte']
        match = "✓" if predicted == actual else "✗"
        print(f"   0x{data['addr']:04X}: Predicted 0x{predicted:02X}, Actual 0x{actual:02X} {match}")
        if predicted != actual:
            all_match = False
    
    print(f"\n   Result: {'All predictions match!' if all_match else 'Predictions do not match.'}")
    
    if all_match:
        print(f"\n🎯 DISCOVERED PATTERN:")
        print(f"   Last Byte = (Address - BASE_ADDR) + 0x{constant_diff:02X}")
        print(f"   Where BASE_ADDR = 0x{base_addr:04X}")
        print(f"   Constant offset = 0x{constant_diff:02X} ({constant_diff} decimal)")

if __name__ == "__main__":
    analyze_address_pattern()