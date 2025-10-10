#!/usr/bin/env python3
"""
Detailed Pattern Analysis for the new observations
"""

def analyze_new_pattern():
    """Analyze the new pattern data"""
    
    # New observed data
    results = [
        {'addr': 0x1020, 'pattern': 0x40202292, 'last_byte': 0x92},
        {'addr': 0x1024, 'pattern': 0x40202212, 'last_byte': 0x12},  # Assumed from partial data
        {'addr': 0x1028, 'pattern': 0x402022C9, 'last_byte': 0xC9},
        {'addr': 0x102C, 'pattern': 0x40202209, 'last_byte': 0x09},
        {'addr': 0x1040, 'pattern': 0x40202274, 'last_byte': 0x74},
        {'addr': 0x1050, 'pattern': 0x40202275, 'last_byte': 0x75},  # Assumed prefix
        {'addr': 0x1080, 'pattern': 0x402022B8, 'last_byte': 0xB8},  # Assumed prefix
        {'addr': 0x1100, 'pattern': 0x40602230, 'last_byte': 0x30},
    ]
    
    print("=== New Pattern Analysis ===\n")
    
    print("1. Address vs Pattern Breakdown:")
    print("   Address   Full Pattern   Prefix    Last Byte")
    print("   -------   ------------   --------  ---------")
    
    for result in results:
        prefix = result['pattern'] >> 8  # Upper 24 bits
        print(f"   0x{result['addr']:04X}    0x{result['pattern']:08X}   0x{prefix:06X}  0x{result['last_byte']:02X}")
    
    print("\n2. Prefix Analysis:")
    print("   Most addresses: 0x402022XX")
    print("   Address 0x1100: 0x406022XX")
    print("   Change threshold appears to be around 0x1100")
    
    print("\n3. Address Bit Analysis:")
    print("   Address   Addr>>8   Addr>>9   Addr>>10  Pattern Change")
    print("   -------   -------   -------   --------  --------------")
    
    for result in results:
        addr8 = result['addr'] >> 8
        addr9 = result['addr'] >> 9
        addr10 = result['addr'] >> 10
        prefix = result['pattern'] >> 8
        change = "YES" if prefix != 0x402022 else "no"
        print(f"   0x{result['addr']:04X}    0x{addr8:02X}      0x{addr9:02X}       0x{addr10:02X}        {change}")
    
    print("\n4. Hypothesis: Address bit influences prefix")
    print("   When addr[8] changes from 0x10 to 0x11:")
    print("   Prefix changes from 0x402022 to 0x406022")
    print("   Difference: 0x406022 - 0x402022 = 0x004000")
    print("   This is exactly bit 14 (0x4000)")
    
    print("\n5. Last Byte Pattern Analysis:")
    print("   Checking if there's still an address relationship...")
    
    print("   Address   Last Byte   Addr&0xFF   Relationship")
    print("   -------   ---------   ---------   ------------")
    
    for result in results:
        addr_low = result['addr'] & 0xFF
        diff = result['last_byte'] - addr_low
        print(f"   0x{result['addr']:04X}    0x{result['last_byte']:02X}        0x{addr_low:02X}        {diff:+4d} (0x{diff&0xFF:02X})")
    
    print("\n6. Revised Pattern Theory:")
    print("   Pattern = PPPPPPXX where:")
    print("   PPPPPP = Base prefix + address-dependent bits")
    print("   XX = Some function of address (not simple offset)")
    
    print("\n7. Key Questions:")
    print("   - Why did the pattern change from 0xF02022XX to 0x40202XX?")
    print("   - Is this related to recent register additions?")
    print("   - What determines the last byte value?")

if __name__ == "__main__":
    analyze_new_pattern()