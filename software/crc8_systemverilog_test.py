#!/usr/bin/env python3
"""
CRC8 SystemVerilog Implementation Match Test
"""

def crc8_systemverilog_style(data):
    """Match SystemVerilog implementation exactly"""
    crc = 0x00
    
    for byte in data:
        crc_temp = crc ^ byte
        
        # Process each bit with polynomial 0x07 (unrolled like SystemVerilog)
        if crc_temp & 0x80: crc_temp = (crc_temp << 1) ^ 0x07
        else:               crc_temp = crc_temp << 1
        crc_temp &= 0xFF
        
        if crc_temp & 0x80: crc_temp = (crc_temp << 1) ^ 0x07
        else:               crc_temp = crc_temp << 1
        crc_temp &= 0xFF
        
        if crc_temp & 0x80: crc_temp = (crc_temp << 1) ^ 0x07
        else:               crc_temp = crc_temp << 1
        crc_temp &= 0xFF
        
        if crc_temp & 0x80: crc_temp = (crc_temp << 1) ^ 0x07
        else:               crc_temp = crc_temp << 1
        crc_temp &= 0xFF
        
        if crc_temp & 0x80: crc_temp = (crc_temp << 1) ^ 0x07
        else:               crc_temp = crc_temp << 1
        crc_temp &= 0xFF
        
        if crc_temp & 0x80: crc_temp = (crc_temp << 1) ^ 0x07
        else:               crc_temp = crc_temp << 1
        crc_temp &= 0xFF
        
        if crc_temp & 0x80: crc_temp = (crc_temp << 1) ^ 0x07
        else:               crc_temp = crc_temp << 1
        crc_temp &= 0xFF
        
        if crc_temp & 0x80: crc_temp = (crc_temp << 1) ^ 0x07
        else:               crc_temp = crc_temp << 1
        crc_temp &= 0xFF
        
        crc = crc_temp
    
    return crc

def test_protocol_vectors():
    """Test against protocol specification test vectors"""
    test_vectors = [
        ([0x21, 0x10, 0x00, 0x00, 0x40, 0xEF, 0xBE, 0xAD, 0xDE], 0x8E, "32-bit write frame"),
        ([0x42, 0x20, 0x00, 0x00, 0x40, 0x11, 0x22], 0x23, "8-bit auto-inc frame"),
        ([0x91, 0x30, 0x00, 0x00, 0x40], 0x77, "16-bit read request"),
        ([0x00, 0x91, 0x30, 0x00, 0x00, 0x40, 0xEF, 0xBE], 0x45, "16-bit read response"),
        ([0x21], 0x21, "Single byte (CMD only)"),
        ([0x00, 0x00, 0x00, 0x00], 0x00, "All zeros"),
        ([0xFF, 0xFF, 0xFF, 0xFF], 0xFF, "All ones"),
        ([0x01, 0x02, 0x03, 0x04, 0x05], 0x37, "Sequential bytes"),
    ]
    
    print("=== CRC8 SystemVerilog Style Implementation Test ===")
    all_pass = True
    
    for data, expected, description in test_vectors:
        calculated = crc8_systemverilog_style(data)
        status = "PASS" if calculated == expected else "FAIL"
        if status == "FAIL":
            all_pass = False
        
        print(f"[{status}] {description}")
        print(f"         Data: {' '.join(f'{b:02X}' for b in data)}")
        print(f"         Expected: 0x{expected:02X}, Calculated: 0x{calculated:02X}")
        print()
    
    if all_pass:
        print("✅ ALL TESTS PASSED - SystemVerilog style implementation matches protocol!")
    else:
        print("❌ Some tests FAILED - Implementation needs correction")

if __name__ == "__main__":
    test_protocol_vectors()