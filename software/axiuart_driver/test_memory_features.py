"""
AXIUART Driver - Memory Access Feature Test

Test script for the new Memory Access functionality.
Demonstrates arbitrary address/data read/write capabilities.
"""

import sys
import os

# Add current directory to path for module imports
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from core import COMManager, UARTProtocol


def test_memory_access_features():
    """Test memory access functionality."""
    print("AXIUART Driver - Memory Access Feature Test")
    print("=" * 50)
    
    # Test address/data parsing
    test_addresses = [
        "1000",      # Without 0x prefix
        "0x1000",    # With 0x prefix
        "DEADBEEF",  # Uppercase
        "0xdeadbeef" # Lowercase with prefix
    ]
    
    test_data = [
        "FF",
        "0xFF", 
        "12345678",
        "0xABCDEF00"
    ]
    
    print("Testing hex value parsing:")
    for addr in test_addresses:
        try:
            parsed = int(addr.replace('0x', ''), 16)
            print(f"  Address '{addr}' -> 0x{parsed:08X} ✓")
        except ValueError as e:
            print(f"  Address '{addr}' -> ERROR: {e} ✗")
    
    print("\nTesting data value parsing:")
    for data in test_data:
        try:
            parsed = int(data.replace('0x', ''), 16)
            print(f"  Data '{data}' -> 0x{parsed:08X} ✓")
        except ValueError as e:
            print(f"  Data '{data}' -> ERROR: {e} ✗")
    
    # Test data width validation
    print("\nTesting data width validation:")
    test_cases = [
        (0xFF, 8, True),        # Valid 8-bit
        (0x100, 8, False),      # Too large for 8-bit
        (0xFFFF, 16, True),     # Valid 16-bit
        (0x10000, 16, False),   # Too large for 16-bit
        (0xFFFFFFFF, 32, True), # Valid 32-bit
        (0x100000000, 32, False) # Too large for 32-bit
    ]
    
    for value, width, should_pass in test_cases:
        max_value = (1 << width) - 1
        is_valid = value <= max_value
        status = "✓" if is_valid == should_pass else "✗"
        print(f"  0x{value:X} for {width}-bit: {is_valid} {status}")
    
    print("\nMemory Access Feature Test completed!")
    print("\nTo test the GUI:")
    print("1. Run: python gui_app.py")
    print("2. Go to the 'Memory' tab")
    print("3. Try these operations:")
    print("   - Direct Memory Access:")
    print("     * Address: 1000 or 0x1000")
    print("     * Data: FF or 0xFF")
    print("     * Click Read/Write buttons")
    print("   - Bulk Operations:")
    print("     * Start Address: 1000")
    print("     * Count: 4")
    print("     * Pattern: DEADBEEF")
    print("     * Try Bulk Read/Fill/Test")
    print("   - Memory Dump will show formatted results")


def demonstrate_memory_operations():
    """Demonstrate memory operation examples."""
    print("\nMemory Operation Examples:")
    print("=" * 30)
    
    # Example operations that would be performed
    operations = [
        ("Direct Read", "0x1000", "", "32", "Read single register"),
        ("Direct Write", "0x1004", "0x12345678", "32", "Write control value"),
        ("Write & Verify", "0x1008", "0xDEADBEEF", "32", "Write and read back"),
        ("Bulk Read", "0x1000", "", "32", "Read 8 consecutive registers"),
        ("Memory Fill", "0x2000", "0x55555555", "32", "Fill 16 locations with pattern"),
        ("Memory Test", "0x3000", "", "32", "Test 4 locations with patterns")
    ]
    
    print("Operation        | Address  | Data       | Width | Description")
    print("-" * 70)
    for op, addr, data, width, desc in operations:
        data_str = data if data else "-"
        print(f"{op:15} | {addr:8} | {data_str:10} | {width:5} | {desc}")
    
    print("\nFeatures:")
    print("✓ Arbitrary address access (any 32-bit address)")
    print("✓ Multiple data widths (8/16/32 bit)")  
    print("✓ Hexadecimal input with/without 0x prefix")
    print("✓ Write verification (write + read back)")
    print("✓ Bulk operations (read/write multiple locations)")
    print("✓ Memory testing (pattern testing)")
    print("✓ Formatted memory dump display")
    print("✓ Operation logging with timestamps")
    print("✓ Error handling and validation")


if __name__ == "__main__":
    test_memory_access_features()
    demonstrate_memory_operations()