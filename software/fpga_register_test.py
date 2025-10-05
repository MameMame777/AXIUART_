#!/usr/bin/env python3
"""
FPGA Register Test Suite
Comprehensive register access testing for UART-AXI4-Lite Bridge

This script provides specific test functions for the FPGA register map
as defined in the project documentation.
"""

from uart_axi_register_access import UartAxiBridge, AccessSize, StatusCode
import time
import sys

class FpgaRegisterTester:
    """FPGA-specific register test functions"""
    
    # Register addresses from project register map
    REG_CONTROL = 0x00001000    # Control register
    REG_STATUS = 0x00001004     # Status register  
    REG_CONFIG = 0x00001008     # Configuration register
    REG_DEBUG = 0x0000100C      # Debug control
    REG_TX_COUNT = 0x00001010   # TX counter (RO)
    REG_RX_COUNT = 0x00001014   # RX counter (RO)
    REG_FIFO_STAT = 0x00001018  # FIFO status (RO)
    REG_VERSION = 0x0000101C    # Version register (RO)
    
    def __init__(self, port="COM3", baudrate=115200):
        """Initialize tester with UART-AXI bridge"""
        self.bridge = UartAxiBridge(port, baudrate)
        self.test_results = []
    
    def connect(self):
        """Connect to FPGA"""
        return self.bridge.connect()
    
    def disconnect(self):
        """Disconnect from FPGA"""
        self.bridge.disconnect()
    
    def log_test(self, test_name, passed, details=""):
        """Log test result"""
        status = "PASS" if passed else "FAIL"
        result = f"[{status}] {test_name}"
        if details:
            result += f" - {details}"
        print(result)
        self.test_results.append((test_name, passed, details))
    
    def test_register_read(self, addr, name):
        """Test single register read"""
        print(f"\n📍 Testing {name} (0x{addr:08X})")
        value = self.bridge.read_register(addr)
        if value is not None:
            self.log_test(f"Read {name}", True, f"Value: 0x{value:08X}")
            return value
        else:
            self.log_test(f"Read {name}", False, "Read failed")
            return None
    
    def test_register_write_read(self, addr, name, test_value=0x12345678):
        """Test register write followed by read (for RW registers)"""
        print(f"\n📍 Testing {name} Write/Read (0x{addr:08X})")
        
        # Write test value
        write_ok = self.bridge.write_register(addr, test_value)
        if not write_ok:
            self.log_test(f"Write {name}", False, "Write failed")
            return False
        
        # Read back
        read_value = self.bridge.read_register(addr)
        if read_value is None:
            self.log_test(f"Read {name}", False, "Read failed")
            return False
        
        # Compare
        if read_value == test_value:
            self.log_test(f"Write/Read {name}", True, f"Value matches: 0x{test_value:08X}")
            return True
        else:
            self.log_test(f"Write/Read {name}", False, 
                         f"Mismatch: wrote 0x{test_value:08X}, read 0x{read_value:08X}")
            return False
    
    def test_basic_registers(self):
        """Test basic register access"""
        print("\n🔧 Basic Register Access Test")
        print("=" * 50)
        
        # Test read-only registers first
        self.test_register_read(self.REG_VERSION, "VERSION")
        self.test_register_read(self.REG_STATUS, "STATUS")
        self.test_register_read(self.REG_TX_COUNT, "TX_COUNT")
        self.test_register_read(self.REG_RX_COUNT, "RX_COUNT")
        self.test_register_read(self.REG_FIFO_STAT, "FIFO_STATUS")
        
        # Test read/write registers
        self.test_register_write_read(self.REG_CONTROL, "CONTROL", 0x00000001)
        self.test_register_write_read(self.REG_CONFIG, "CONFIG", 0xABCD1234)
        self.test_register_write_read(self.REG_DEBUG, "DEBUG", 0x0000000F)
    
    def test_data_width_access(self):
        """Test different data width access (8/16/32 bit)"""
        print("\n🔧 Data Width Access Test")
        print("=" * 50)
        
        addr = self.REG_CONFIG  # Use CONFIG register for testing
        
        # Test 32-bit access
        value32 = 0x12345678
        print(f"\n📍 32-bit access test")
        write_ok = self.bridge.write_register(addr, value32, AccessSize.DWORD)
        if write_ok:
            read_value = self.bridge.read_register(addr, AccessSize.DWORD)
            if read_value == value32:
                self.log_test("32-bit access", True, f"0x{value32:08X}")
            else:
                self.log_test("32-bit access", False, f"Expected 0x{value32:08X}, got 0x{read_value:08X}")
        
        # Test 16-bit access (lower half)
        value16 = 0xABCD
        print(f"\n📍 16-bit access test")
        write_ok = self.bridge.write_register(addr, value16, AccessSize.WORD)
        if write_ok:
            read_value = self.bridge.read_register(addr, AccessSize.WORD)
            if read_value == value16:
                self.log_test("16-bit access", True, f"0x{value16:04X}")
            else:
                self.log_test("16-bit access", False, f"Expected 0x{value16:04X}, got 0x{read_value:04X}")
        
        # Test 8-bit access
        value8 = 0xEF
        print(f"\n📍 8-bit access test")
        write_ok = self.bridge.write_register(addr, value8, AccessSize.BYTE)
        if write_ok:
            read_value = self.bridge.read_register(addr, AccessSize.BYTE)
            if read_value == value8:
                self.log_test("8-bit access", True, f"0x{value8:02X}")
            else:
                self.log_test("8-bit access", False, f"Expected 0x{value8:02X}, got 0x{read_value:02X}")
    
    def test_burst_read(self):
        """Test burst read functionality"""
        print("\n🔧 Burst Read Test")
        print("=" * 50)
        
        # Test burst read of consecutive registers
        start_addr = self.REG_CONTROL
        count = 4
        
        print(f"\n📍 Burst read {count} registers from 0x{start_addr:08X}")
        values = self.bridge.read_burst(start_addr, count, AccessSize.DWORD, auto_inc=True)
        
        if values and len(values) == count:
            self.log_test("Burst read", True, f"Read {len(values)} values")
        else:
            self.log_test("Burst read", False, f"Expected {count} values, got {len(values) if values else 0}")
    
    def test_error_conditions(self):
        """Test error condition handling"""
        print("\n🔧 Error Condition Test")
        print("=" * 50)
        
        # Test misaligned access (should fail)
        print(f"\n📍 Misaligned access test")
        misaligned_addr = 0x00001001  # Misaligned for 32-bit access
        value = self.bridge.read_register(misaligned_addr, AccessSize.DWORD)
        if value is None:
            self.log_test("Misaligned access detection", True, "Correctly rejected")
        else:
            self.log_test("Misaligned access detection", False, "Should have been rejected")
        
        # Test invalid address
        print(f"\n📍 Invalid address test")
        invalid_addr = 0xFFFFFFFF
        value = self.bridge.read_register(invalid_addr)
        if value is None:
            self.log_test("Invalid address detection", True, "Correctly rejected")
        else:
            self.log_test("Invalid address detection", False, "Should have been rejected")
    
    def test_performance(self):
        """Test performance characteristics"""
        print("\n🔧 Performance Test")
        print("=" * 50)
        
        # Single register read/write latency
        addr = self.REG_CONFIG
        iterations = 10
        
        print(f"\n📍 Single register access latency ({iterations} iterations)")
        
        # Write latency
        start_time = time.time()
        for i in range(iterations):
            self.bridge.write_register(addr, 0x12345678 + i)
        write_time = time.time() - start_time
        avg_write_latency = (write_time / iterations) * 1000  # ms
        
        # Read latency  
        start_time = time.time()
        for i in range(iterations):
            self.bridge.read_register(addr)
        read_time = time.time() - start_time
        avg_read_latency = (read_time / iterations) * 1000  # ms
        
        self.log_test("Write latency", True, f"{avg_write_latency:.1f} ms average")
        self.log_test("Read latency", True, f"{avg_read_latency:.1f} ms average")
        
        # Burst read performance
        print(f"\n📍 Burst read performance")
        start_time = time.time()
        values = self.bridge.read_burst(self.REG_CONTROL, 8, AccessSize.DWORD)
        burst_time = time.time() - start_time
        
        if values:
            throughput = (8 * 4) / burst_time  # bytes per second
            self.log_test("Burst read throughput", True, f"{throughput:.0f} bytes/sec")
        else:
            self.log_test("Burst read throughput", False, "Burst read failed")
    
    def run_all_tests(self):
        """Run complete test suite"""
        print("🚀 FPGA Register Test Suite")
        print("=" * 60)
        
        start_time = time.time()
        
        # Run all test categories
        try:
            self.test_basic_registers()
            self.test_data_width_access()
            self.test_burst_read()
            self.test_error_conditions()
            self.test_performance()
        except KeyboardInterrupt:
            print("\n⏹️ Tests interrupted by user")
        except Exception as e:
            print(f"\n❌ Test suite error: {e}")
        
        # Summary
        total_time = time.time() - start_time
        total_tests = len(self.test_results)
        passed_tests = sum(1 for _, passed, _ in self.test_results if passed)
        failed_tests = total_tests - passed_tests
        
        print("\n" + "=" * 60)
        print("📊 TEST SUMMARY")
        print("=" * 60)
        print(f"Total tests: {total_tests}")
        print(f"Passed: {passed_tests}")
        print(f"Failed: {failed_tests}")
        print(f"Success rate: {(passed_tests/total_tests*100) if total_tests > 0 else 0:.1f}%")
        print(f"Total time: {total_time:.1f} seconds")
        
        if failed_tests > 0:
            print("\n❌ Failed tests:")
            for name, passed, details in self.test_results:
                if not passed:
                    print(f"  - {name}: {details}")
        
        return failed_tests == 0

def main():
    """Main test execution"""
    if len(sys.argv) > 1:
        port = sys.argv[1]
    else:
        port = "COM3"
    
    print(f"🔌 Connecting to FPGA on {port}...")
    
    tester = FpgaRegisterTester(port)
    
    if not tester.connect():
        print("❌ Failed to connect to FPGA")
        return 1
    
    try:
        success = tester.run_all_tests()
        return 0 if success else 1
    finally:
        tester.disconnect()

if __name__ == "__main__":
    exit(main())