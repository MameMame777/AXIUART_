#!/usr/bin/env python3
"""
0xF02022XX Pattern Decoder
Analyze the specific pattern to understand its origin
"""

def analyze_f02022_pattern():
    """Analyze the 0xF02022XX pattern in detail"""
    
    print("🔍 === 0xF02022XX Pattern Analysis ===")
    
    # Observed values
    observed_values = {
        0x00001020: 0xF0202248,
        0x00001024: 0xF0202249, 
        0x00001028: 0xF020224A,
        0x0000102C: 0xF020224B
    }
    
    # Extract pattern components
    fixed_pattern = 0xF02022
    variable_bytes = []
    
    print(f"\n📊 Pattern Breakdown:")
    print(f"Fixed part: 0x{fixed_pattern:06X}")
    
    for addr, value in observed_values.items():
        last_byte = value & 0xFF
        variable_bytes.append(last_byte)
        print(f"Address 0x{addr:08X} -> 0x{value:08X} (last byte: 0x{last_byte:02X})")
    
    # Analyze the variable bytes
    print(f"\n🔢 Variable Byte Analysis:")
    print(f"Sequence: {[hex(b) for b in variable_bytes]}")
    print(f"Decimal:  {variable_bytes}")
    
    # Check if it's a simple increment
    if all(variable_bytes[i] == variable_bytes[0] + i for i in range(len(variable_bytes))):
        print(f"✅ Simple increment pattern starting from 0x{variable_bytes[0]:02X}")
    
    # Analyze 0xF02022 as different interpretations
    print(f"\n🧮 Fixed Pattern 0xF02022 Analysis:")
    
    # As separate bytes
    byte2 = (fixed_pattern >> 16) & 0xFF  # 0xF0
    byte1 = (fixed_pattern >> 8) & 0xFF   # 0x20
    byte0 = fixed_pattern & 0xFF          # 0x22
    
    print(f"Byte breakdown: 0x{byte2:02X} 0x{byte1:02X} 0x{byte0:02X}")
    print(f"Decimal: {byte2} {byte1} {byte0}")
    
    # Check common interpretations
    print(f"\n🔍 Possible Interpretations:")
    
    # 1. Memory addresses
    print(f"1. As memory address: 0x{fixed_pattern:06X}")
    
    # 2. ASCII interpretation  
    ascii_chars = []
    for byte_val in [byte2, byte1, byte0]:
        if 32 <= byte_val <= 126:  # Printable ASCII
            ascii_chars.append(chr(byte_val))
        else:
            ascii_chars.append(f"\\x{byte_val:02X}")
    print(f"2. ASCII interpretation: {''.join(ascii_chars)}")
    
    # 3. Check if it matches register addresses
    reg_addresses = [0x001020, 0x001024, 0x001028, 0x00102C]
    print(f"3. Register address correlation:")
    for addr in reg_addresses:
        addr_match = (addr >> 8) & 0xFFFF  # Take middle bytes
        print(f"   0x{addr:06X} -> middle bytes: 0x{addr_match:04X}")
    
    # 4. Check bit patterns
    print(f"4. Bit pattern analysis:")
    print(f"   0xF0: {bin(0xF0)} (240 decimal)")
    print(f"   0x20: {bin(0x20)} (32 decimal, space character)")  
    print(f"   0x22: {bin(0x22)} (34 decimal, quote character)")
    
    # 5. Check for known FPGA/system constants
    print(f"5. Known constant check:")
    print(f"   0xF0202200: Could be default/uninitialized memory pattern")
    print(f"   0x20202020: Common space-fill pattern")
    print(f"   0xF0: Often used as error/debug marker")
    
    # Analyze increment pattern
    print(f"\n🎯 Increment Pattern Analysis:")
    start_value = variable_bytes[0]  # 0x48
    print(f"Starting value: 0x{start_value:02X} ({start_value} decimal)")
    print(f"Increment: +1 per register")
    
    # Check what 0x48 represents
    print(f"0x48 interpretations:")
    print(f"   Decimal: {start_value}")
    print(f"   ASCII: '{chr(start_value)}' (letter H)")
    print(f"   Possible meanings: ")
    print(f"     - Simple counter starting at 72")
    print(f"     - ASCII 'H' (0x48) as marker")
    print(f"     - Memory offset or index")

def analyze_bit_relationships():
    """Analyze bit-level relationships in the pattern"""
    
    print(f"\n🔬 === Bit-Level Relationship Analysis ===")
    
    # Full 32-bit values
    values = [0xF0202248, 0xF0202249, 0xF020224A, 0xF020224B]
    addresses = [0x00001020, 0x00001024, 0x00001028, 0x0000102C]
    
    print(f"Complete values:")
    for addr, val in zip(addresses, values):
        print(f"0x{addr:08X}: 0x{val:08X} = {bin(val)}")
    
    # Check XOR relationships
    print(f"\nXOR Analysis:")
    for i, (addr, val) in enumerate(zip(addresses, values)):
        addr_xor = addr ^ val
        print(f"0x{addr:08X} XOR 0x{val:08X} = 0x{addr_xor:08X}")
        
        # Check if the XOR reveals a pattern
        if i == 0:
            base_xor = addr_xor
            print(f"   Base XOR pattern: 0x{base_xor:08X}")
        else:
            xor_diff = addr_xor ^ base_xor
            print(f"   Difference from base: 0x{xor_diff:08X}")
    
    # Check address influence
    print(f"\nAddress Influence Analysis:")
    for addr, val in zip(addresses, values):
        addr_low = addr & 0xFF
        val_low = val & 0xFF
        print(f"Address low byte: 0x{addr_low:02X}, Value low byte: 0x{val_low:02X}")

def main():
    """Main analysis function"""
    analyze_f02022_pattern()
    analyze_bit_relationships()
    
    print(f"\n📋 === Summary ===")
    print(f"The 0xF02022XX pattern appears to be:")
    print(f"1. A fixed 24-bit pattern (0xF02022) + incrementing counter")
    print(f"2. Not related to register addresses or written values")
    print(f"3. Possibly from uninitialized memory or debug circuitry")
    print(f"4. Counter starts at 0x48 ('H') and increments by 1")
    print(f"5. Suggests hardware source independent of register logic")

if __name__ == "__main__":
    main()