#!/usr/bin/env python3
"""
Alternative Pattern Analysis for 0xF02022XX
"""

def analyze_alternative_patterns():
    """Analyze alternative mathematical relationships"""
    
    # Observed data
    test_data = [
        {'addr': 0x1020, 'offset': 0x020, 'last_byte': 0x48, 'reg': 'REG_TEST_0'},
        {'addr': 0x1024, 'offset': 0x024, 'last_byte': 0x49, 'reg': 'REG_TEST_1'},
        {'addr': 0x1028, 'offset': 0x028, 'last_byte': 0x4A, 'reg': 'REG_TEST_2'},
        {'addr': 0x102C, 'offset': 0x02C, 'last_byte': 0x4B, 'reg': 'REG_TEST_3'},
    ]
    
    print("=== Alternative Pattern Analysis ===\n")
    
    print("Theory 1: Sequential Counter Independent of Address")
    print("   Register   Address   Last Byte   Sequential Index")
    print("   --------   -------   ---------   ----------------")
    
    for i, data in enumerate(test_data):
        sequential_value = 0x48 + i  # Start from 'H' (0x48) and increment
        match = "✓" if data['last_byte'] == sequential_value else "✗"
        print(f"   {data['reg']:10} 0x{data['addr']:04X}    0x{data['last_byte']:02X}        0x{sequential_value:02X} ('{chr(sequential_value)}') {match}")
    
    print("\n🎯 PATTERN FOUND: Sequential ASCII counter starting from 'H' (0x48)")
    print("   Pattern: 0xF02022XX where XX = 0x48 + register_index")
    print("   This suggests access order determines the last byte, not address!")
    
    print("\nTheory 2: Register Index Mapping")
    print("   Test Register Index vs Last Byte:")
    
    for i, data in enumerate(test_data):
        print(f"   REG_TEST_{i} -> 0x{data['last_byte']:02X} ('{chr(data['last_byte'])}')")
    
    print("\nTheory 3: Address Bit Analysis")
    print("   Address   Binary           Relevant Bits   Last Byte")
    print("   -------   --------------   -------------   ---------")
    
    for data in test_data:
        addr_bin = f"{data['addr']:016b}"
        addr_low4 = data['addr'] & 0xF  # Lower 4 bits
        addr_byte2 = (data['addr'] >> 2) & 0xFF  # Divide by 4
        print(f"   0x{data['addr']:04X}    {addr_bin}   Low4:0x{addr_low4:X} /4:0x{addr_byte2:02X}   0x{data['last_byte']:02X}")
    
    print("\nTheory 4: Index-Based Sequential Pattern")
    print("   This pattern appears to be:")
    print("   1. Independent of actual address value")
    print("   2. Based on register access order or register index")
    print("   3. Simple increment: 0x48, 0x49, 0x4A, 0x4B...")
    print("   4. Starting value: 'H' (0x48) = ASCII 72")
    
    print("\nConclusion:")
    print("   The pattern 0xF02022XX where XX = 0x48 + N appears to be:")
    print("   - A debug/identification pattern")
    print("   - N is likely the register index (0,1,2,3) or access order")
    print("   - Fixed prefix 0xF02022 might be:")
    print("     * Module identifier")
    print("     * Debug signature")
    print("     * Uninitialized memory pattern")
    
    print("\n❓ Key Question: Why 0xF02022?")
    print("   0xF02022 in binary: 11110000 00100000 00100010")
    print("   Could this be:")
    print("   - A specific FPGA memory initialization pattern?")
    print("   - A module/block RAM identifier?")
    print("   - Related to synthesis tool defaults?")

if __name__ == "__main__":
    analyze_alternative_patterns()