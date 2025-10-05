#!/usr/bin/env python3
"""
Test Register Validation Script
Tests the newly added test registers (0x00001020-0x0000102C)
"""

from uart_axi_register_access import UartAxiBridge

def test_new_registers():
    """Test the newly added test registers"""
    print("🧪 Testing New Test Registers")
    print("=" * 50)
    
    # Test register addresses
    REG_TEST_0 = 0x00001020
    REG_TEST_1 = 0x00001024  
    REG_TEST_2 = 0x00001028
    REG_TEST_3 = 0x0000102C
    
    bridge = UartAxiBridge("COM3", 115200)
    
    if not bridge.connect():
        print("❌ Failed to connect to FPGA")
        return False
    
    try:
        print("\n📍 Testing TEST_REG_0 (0x00001020)")
        # Read initial value (should be 0xDEADBEEF)
        initial_value = bridge.read_register(REG_TEST_0)
        if initial_value is not None:
            print(f"✅ Initial value: 0x{initial_value:08X}")
        else:
            print("❌ Failed to read initial value")
            
        # Write test value
        test_value = 0x12345678
        write_ok = bridge.write_register(REG_TEST_0, test_value)
        if write_ok:
            print(f"✅ Write successful: 0x{test_value:08X}")
        else:
            print("❌ Write failed")
            
        # Read back
        read_back = bridge.read_register(REG_TEST_0)
        if read_back == test_value:
            print(f"✅ Read-back successful: 0x{read_back:08X}")
        else:
            print(f"❌ Read-back mismatch: expected 0x{test_value:08X}, got 0x{read_back:08X}")
            
        print("\n📍 Testing TEST_REG_1 (0x00001024)")
        # Test different pattern
        test_patterns = [0xAAAA5555, 0x55555555, 0x00000000, 0xFFFFFFFF]
        
        for pattern in test_patterns:
            bridge.write_register(REG_TEST_1, pattern)
            read_back = bridge.read_register(REG_TEST_1)
            if read_back == pattern:
                print(f"✅ Pattern 0x{pattern:08X}: OK")
            else:
                print(f"❌ Pattern 0x{pattern:08X}: Expected 0x{pattern:08X}, got 0x{read_back:08X}")
                
        print("\n📍 Testing all test registers")
        test_values = [0x11111111, 0x22222222, 0x33333333, 0x44444444]
        test_addrs = [REG_TEST_0, REG_TEST_1, REG_TEST_2, REG_TEST_3]
        
        # Write different values to each register
        for addr, value in zip(test_addrs, test_values):
            bridge.write_register(addr, value)
            
        # Read back and verify
        all_ok = True
        for addr, expected_value in zip(test_addrs, test_values):
            read_value = bridge.read_register(addr)
            if read_value == expected_value:
                print(f"✅ 0x{addr:08X}: 0x{read_value:08X}")
            else:
                print(f"❌ 0x{addr:08X}: Expected 0x{expected_value:08X}, got 0x{read_value:08X}")
                all_ok = False
                
        return all_ok
        
    finally:
        bridge.disconnect()

if __name__ == "__main__":
    success = test_new_registers()
    if success:
        print("\n🎉 All test register tests passed!")
    else:
        print("\n❌ Some test register tests failed!")