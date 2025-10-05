#!/usr/bin/env python3
"""
CRC8 Validation Script for UART-AXI4-Lite Bridge Protocol

This script validates the CRC8 implementation against the test vectors
provided in the protocol specification.
"""

def crc8_calculate(data):
    """
    Calculate CRC8 using polynomial 0x07
    Implementation matches the protocol specification
    """
    crc = 0x00
    for byte in data:
        crc ^= byte
        for _ in range(8):
            if crc & 0x80:
                crc = ((crc << 1) ^ 0x07) & 0xFF
            else:
                crc = (crc << 1) & 0xFF
    return crc

def test_crc8_vectors():
    """Test CRC8 implementation against protocol test vectors"""
    
    # Test vectors from protocol specification Section 10.2
    test_vectors = [
        {
            'data': [0x21, 0x10, 0x00, 0x00, 0x40, 0xEF, 0xBE, 0xAD, 0xDE],
            'expected': 0x8E,
            'description': 'Example 4.1: 32-bit write frame'
        },
        {
            'data': [0x42, 0x20, 0x00, 0x00, 0x40, 0x11, 0x22],
            'expected': 0x23,
            'description': 'Example 4.2: 8-bit auto-inc frame'
        },
        {
            'data': [0x91, 0x30, 0x00, 0x00, 0x40],
            'expected': 0x77,
            'description': 'Example 4.3: 16-bit read request'
        },
        {
            'data': [0x00, 0x91, 0x30, 0x00, 0x00, 0x40, 0xEF, 0xBE],
            'expected': 0x45,
            'description': 'Example 4.3: 16-bit read response'
        },
        {
            'data': [0x21],
            'expected': 0x21,
            'description': 'Single byte (CMD only)'
        },
        {
            'data': [0x00, 0x00, 0x00, 0x00],
            'expected': 0x00,
            'description': 'All zeros'
        },
        {
            'data': [0xFF, 0xFF, 0xFF, 0xFF],
            'expected': 0xFF,
            'description': 'All ones'
        },
        {
            'data': [0x01, 0x02, 0x03, 0x04, 0x05],
            'expected': 0x37,
            'description': 'Sequential bytes'
        }
    ]
    
    print("🔧 CRC8 Validation Test")
    print("=" * 60)
    
    all_passed = True
    
    for i, vector in enumerate(test_vectors):
        data = vector['data']
        expected = vector['expected']
        description = vector['description']
        
        calculated = crc8_calculate(data)
        passed = calculated == expected
        
        status = "PASS" if passed else "FAIL"
        data_str = " ".join(f"{b:02X}" for b in data)
        
        print(f"[{status}] Test {i+1}: {description}")
        print(f"         Data: {data_str}")
        print(f"         Expected: 0x{expected:02X}, Calculated: 0x{calculated:02X}")
        
        if not passed:
            all_passed = False
        print()
    
    print("=" * 60)
    if all_passed:
        print("✅ All CRC8 tests PASSED - Implementation is correct")
    else:
        print("❌ Some CRC8 tests FAILED - Implementation needs review")
    
    return all_passed

def frame_examples():
    """Generate example frames with correct CRC8"""
    
    print("📋 Example Frame Generation")
    print("=" * 60)
    
    examples = [
        {
            'name': 'Write 32-bit to 0x40000010',
            'frame': [0xA5, 0x21, 0x10, 0x00, 0x00, 0x40, 0xEF, 0xBE, 0xAD, 0xDE],
            'crc_data': [0x21, 0x10, 0x00, 0x00, 0x40, 0xEF, 0xBE, 0xAD, 0xDE]
        },
        {
            'name': 'Read 32-bit from 0x40000030',
            'frame': [0xA5, 0x91, 0x30, 0x00, 0x00, 0x40],
            'crc_data': [0x91, 0x30, 0x00, 0x00, 0x40]
        },
        {
            'name': 'Write response (OK)',
            'frame': [0x5A, 0x00, 0x21],
            'crc_data': [0x00, 0x21]
        }
    ]
    
    for example in examples:
        frame = example['frame']
        crc_data = example['crc_data']
        
        # Calculate CRC
        crc = crc8_calculate(crc_data)
        
        # Complete frame
        complete_frame = frame + [crc]
        frame_str = " ".join(f"{b:02X}" for b in complete_frame)
        
        print(f"📍 {example['name']}")
        print(f"   Frame: {frame_str}")
        print(f"   CRC8:  0x{crc:02X}")
        print()

if __name__ == "__main__":
    # Run CRC8 validation
    crc8_valid = test_crc8_vectors()
    
    print()
    
    # Generate example frames
    frame_examples()
    
    # Exit with appropriate code
    exit(0 if crc8_valid else 1)