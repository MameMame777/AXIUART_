#!/usr/bin/env python3
"""
UART-AXI4 Protocol Comprehensive Test Suite
==========================================

This module implements comprehensive test scenarios to validate the UART-AXI4 protocol
specification through pure software simulation.

Test Categories:
1. Basic Protocol Tests - Frame construction, parsing, CRC validation
2. Register Access Tests - 8/16/32-bit read/write operations
3. Error Condition Tests - Alignment, CRC, timeout, AXI errors
4. Burst Operation Tests - Multi-beat transfers with auto-increment
5. Edge Case Tests - Boundary conditions and corner cases
6. Performance Tests - Throughput and latency measurements

Author: Protocol Verification Team
Date: October 2025
Version: 1.0
"""

import time
import struct
import logging
from typing import List, Dict, Any, Tuple
from dataclasses import dataclass

from uart_axi4_protocol import (
    UartAxi4Protocol, VirtualUartPair, ProtocolFrame, 
    StatusCode, CommandFields, CRC8Calculator
)
from virtual_bridge_simulator import UartAxi4BridgeSimulator


@dataclass
class TestResult:
    """Test result data structure"""
    name: str
    passed: bool
    description: str
    error_message: str = ""
    execution_time: float = 0.0
    additional_data: Dict[str, Any] = None
    
    def __post_init__(self):
        if self.additional_data is None:
            self.additional_data = {}


class ProtocolTestSuite:
    """
    Comprehensive test suite for UART-AXI4 protocol verification
    """
    
    def __init__(self):
        self.uart_pair = VirtualUartPair(baud_rate=115200)
        self.host_uart = self.uart_pair.get_host_interface()
        self.device_uart = self.uart_pair.get_device_interface()
        
        self.bridge = UartAxi4BridgeSimulator(self.device_uart)
        self.protocol = UartAxi4Protocol()
        
        self.test_results: List[TestResult] = []
        self.logger = logging.getLogger(__name__)
        
        # Test configuration
        self.test_timeout = 2.0  # 2 second timeout for responses
        
    def run_all_tests(self) -> Dict[str, Any]:
        """Run all test categories and return summary"""
        print("UART-AXI4 Protocol Comprehensive Test Suite")
        print("=" * 60)
        
        self.bridge.start()
        
        try:
            # Run test categories
            self._run_basic_protocol_tests()
            self._run_register_access_tests()
            self._run_error_condition_tests()
            self._run_burst_operation_tests()
            self._run_edge_case_tests()
            self._run_performance_tests()
            
        finally:
            self.bridge.stop()
        
        # Generate summary
        return self._generate_summary()
    
    def _run_basic_protocol_tests(self):
        """Test basic protocol frame construction and parsing"""
        print("\n1. Basic Protocol Tests")
        print("-" * 30)
        
        # Test 1.1: Frame construction consistency
        start_time = time.time()
        try:
            # Build write frame
            write_frame = self.protocol.build_write_frame(
                address=0x40000000,
                data=bytes([0xAA, 0xBB, 0xCC, 0xDD]),
                size=2,  # 32-bit
                auto_increment=False
            )
            
            # Parse it back
            parsed = self.protocol.parse_frame(write_frame)
            
            # Verify fields
            success = (
                parsed.cmd_fields.rw == False and
                parsed.cmd_fields.size == 2 and
                parsed.cmd_fields.length == 1 and
                parsed.address == 0x40000000 and
                parsed.data == bytes([0xAA, 0xBB, 0xCC, 0xDD])
            )
            
            result = TestResult(
                name="Frame Construction Consistency",
                passed=success,
                description="Build and parse write frame",
                execution_time=time.time() - start_time
            )
            
        except Exception as e:
            result = TestResult(
                name="Frame Construction Consistency",
                passed=False,
                description="Build and parse write frame",
                error_message=str(e),
                execution_time=time.time() - start_time
            )
        
        self.test_results.append(result)
        self._print_result(result)
        
        # Test 1.2: CRC validation with intentional corruption
        start_time = time.time()
        try:
            write_frame = self.protocol.build_write_frame(
                address=0x40000004,
                data=bytes([0x12, 0x34, 0x56, 0x78]),
                size=2,
                auto_increment=False
            )
            
            # Corrupt the CRC
            corrupted_frame = bytearray(write_frame)
            corrupted_frame[-1] ^= 0xFF  # Flip all bits in CRC
            
            # Attempt to parse corrupted frame
            try:
                self.protocol.parse_frame(bytes(corrupted_frame))
                success = False  # Should have failed
                error_msg = "CRC error not detected"
            except ValueError as ve:
                if "CRC mismatch" in str(ve):
                    success = True
                    error_msg = ""
                else:
                    success = False
                    error_msg = f"Wrong error type: {ve}"
            
            result = TestResult(
                name="CRC Error Detection",
                passed=success,
                description="Detect corrupted CRC in frame",
                error_message=error_msg,
                execution_time=time.time() - start_time
            )
            
        except Exception as e:
            result = TestResult(
                name="CRC Error Detection",
                passed=False,
                description="Detect corrupted CRC in frame",
                error_message=str(e),
                execution_time=time.time() - start_time
            )
        
        self.test_results.append(result)
        self._print_result(result)
    
    def _run_register_access_tests(self):
        """Test basic register read/write operations"""
        print("\n2. Register Access Tests")
        print("-" * 30)
        
        # Test 2.1: 32-bit write and read back
        result = self._test_register_access(
            name="32-bit Write/Read",
            address=0x40000000,
            write_data=0xDEADBEEF,
            size=2,
            description="Write and read back 32-bit value"
        )
        self.test_results.append(result)
        self._print_result(result)
        
        # Test 2.2: 16-bit write and read back
        result = self._test_register_access(
            name="16-bit Write/Read",
            address=0x40000010,
            write_data=0xCAFE,
            size=1,
            description="Write and read back 16-bit value"
        )
        self.test_results.append(result)
        self._print_result(result)
        
        # Test 2.3: 8-bit write and read back
        result = self._test_register_access(
            name="8-bit Write/Read",
            address=0x40000020,
            write_data=0xAA,
            size=0,
            description="Write and read back 8-bit value"
        )
        self.test_results.append(result)
        self._print_result(result)
    
    def _test_register_access(self, name: str, address: int, write_data: int,
                            size: int, description: str) -> TestResult:
        """Helper method for register access tests"""
        start_time = time.time()
        
        try:
            # Convert data to bytes (little-endian)
            if size == 0:  # 8-bit
                data_bytes = bytes([write_data & 0xFF])
            elif size == 1:  # 16-bit
                data_bytes = struct.pack('<H', write_data & 0xFFFF)
            else:  # 32-bit
                data_bytes = struct.pack('<I', write_data & 0xFFFFFFFF)
            
            # Write operation
            write_frame = self.protocol.build_write_frame(
                address=address, data=data_bytes, size=size, auto_increment=False
            )
            
            self.host_uart.write(write_frame)
            write_response = self.host_uart.read(4, timeout=self.test_timeout)
            
            if len(write_response) != 4 or write_response[1] != StatusCode.OK:
                return TestResult(
                    name=name, passed=False, description=description,
                    error_message=f"Write failed: {write_response.hex() if write_response else 'timeout'}",
                    execution_time=time.time() - start_time
                )
            
            # Read operation
            read_frame = self.protocol.build_read_frame(
                address=address, size=size, length=1, auto_increment=False
            )
            
            self.host_uart.write(read_frame)
            
            # Calculate expected response length
            expected_len = 8 + (1 << size)  # SOF + STATUS + CMD + ADDR(4) + DATA + CRC
            read_response = self.host_uart.read(expected_len, timeout=self.test_timeout)
            
            if len(read_response) != expected_len or read_response[1] != StatusCode.OK:
                return TestResult(
                    name=name, passed=False, description=description,
                    error_message=f"Read failed: {read_response.hex() if read_response else 'timeout'}",
                    execution_time=time.time() - start_time
                )
            
            # Extract and verify data
            data_start = 7  # After SOF + STATUS + CMD + ADDR
            read_data_bytes = read_response[data_start:data_start + (1 << size)]
            
            if size == 0:  # 8-bit
                read_value = read_data_bytes[0]
            elif size == 1:  # 16-bit
                read_value = struct.unpack('<H', read_data_bytes)[0]
            else:  # 32-bit
                read_value = struct.unpack('<I', read_data_bytes)[0]
            
            success = (read_value == write_data)
            error_msg = "" if success else f"Data mismatch: wrote 0x{write_data:X}, read 0x{read_value:X}"
            
            return TestResult(
                name=name, passed=success, description=description,
                error_message=error_msg, execution_time=time.time() - start_time,
                additional_data={"written": write_data, "read": read_value}
            )
            
        except Exception as e:
            return TestResult(
                name=name, passed=False, description=description,
                error_message=str(e), execution_time=time.time() - start_time
            )
    
    def _run_error_condition_tests(self):
        """Test various error conditions"""
        print("\n3. Error Condition Tests")
        print("-" * 30)
        
        # Test 3.1: Address alignment error
        start_time = time.time()
        try:
            # Manually construct misaligned frame (bypass protocol validation)
            misaligned_frame = bytearray([
                0xA5,  # SOF
                0x21,  # CMD: 32-bit write, length=1
                0x01, 0x00, 0x00, 0x40,  # Misaligned address 0x40000001
                0xAA, 0xBB, 0xCC, 0xDD,  # Data
            ])
            
            # Calculate CRC for the payload (excluding SOF)
            crc = self.protocol.crc_calc.calculate(misaligned_frame[1:])
            misaligned_frame.append(crc)
            
            self.host_uart.write(bytes(misaligned_frame))
            response = self.host_uart.read(4, timeout=self.test_timeout)
            
            success = (len(response) == 4 and response[1] == StatusCode.ADDR_ALIGN)
            error_msg = "" if success else f"Expected alignment error, got: {response.hex() if response else 'timeout'}"
            
            result = TestResult(
                name="Address Alignment Error",
                passed=success,
                description="Detect misaligned 32-bit access",
                error_message=error_msg,
                execution_time=time.time() - start_time
            )
            
        except Exception as e:
            result = TestResult(
                name="Address Alignment Error",
                passed=False,
                description="Detect misaligned 32-bit access",
                error_message=str(e),
                execution_time=time.time() - start_time
            )
        
        self.test_results.append(result)
        self._print_result(result)
        
        # Test 3.2: Invalid command size
        start_time = time.time()
        try:
            # Manually construct frame with invalid size (11b = 3)
            invalid_frame = bytearray([
                0xA5,  # SOF
                0x31,  # CMD: size=11b (invalid), length=1
                0x00, 0x00, 0x00, 0x40,  # Address
                0xAA,  # Single byte data
            ])
            
            crc = self.protocol.crc_calc.calculate(invalid_frame[1:])
            invalid_frame.append(crc)
            
            self.host_uart.write(bytes(invalid_frame))
            response = self.host_uart.read(4, timeout=self.test_timeout)
            
            success = (len(response) == 4 and response[1] == StatusCode.CMD_INV)
            error_msg = "" if success else f"Expected command invalid, got: {response.hex() if response else 'timeout'}"
            
            result = TestResult(
                name="Invalid Command Size",
                passed=success,
                description="Detect invalid SIZE field in command",
                error_message=error_msg,
                execution_time=time.time() - start_time
            )
            
        except Exception as e:
            result = TestResult(
                name="Invalid Command Size",
                passed=False,
                description="Detect invalid SIZE field in command",
                error_message=str(e),
                execution_time=time.time() - start_time
            )
        
        self.test_results.append(result)
        self._print_result(result)
        
        # Test 3.3: AXI slave error (access to error region)
        result = self._test_axi_error_response(
            name="AXI Slave Error",
            address=0x60000000,  # Error region
            expected_status=StatusCode.AXI_SLVERR,
            description="Access to error-generating memory region"
        )
        self.test_results.append(result)
        self._print_result(result)
    
    def _test_axi_error_response(self, name: str, address: int, 
                               expected_status: int, description: str) -> TestResult:
        """Test AXI error response handling"""
        start_time = time.time()
        
        try:
            read_frame = self.protocol.build_read_frame(
                address=address, size=2, length=1, auto_increment=False
            )
            
            self.host_uart.write(read_frame)
            response = self.host_uart.read(4, timeout=self.test_timeout)
            
            success = (len(response) == 4 and response[1] == expected_status)
            error_msg = "" if success else f"Expected status 0x{expected_status:02X}, got: {response.hex() if response else 'timeout'}"
            
            return TestResult(
                name=name, passed=success, description=description,
                error_message=error_msg, execution_time=time.time() - start_time
            )
            
        except Exception as e:
            return TestResult(
                name=name, passed=False, description=description,
                error_message=str(e), execution_time=time.time() - start_time
            )
    
    def _run_burst_operation_tests(self):
        """Test burst operations with auto-increment"""
        print("\n4. Burst Operation Tests")
        print("-" * 30)
        
        # Test 4.1: 4×32-bit burst write with auto-increment
        start_time = time.time()
        try:
            # Prepare test data
            test_data = []
            for i in range(4):
                test_data.extend([(i * 0x11111111) & 0xFFFFFFFF])
            
            # Convert to bytes
            data_bytes = b''.join(struct.pack('<I', val) for val in test_data)
            
            # Burst write
            write_frame = self.protocol.build_write_frame(
                address=0x40001000,
                data=data_bytes,
                size=2,  # 32-bit
                auto_increment=True
            )
            
            self.host_uart.write(write_frame)
            write_response = self.host_uart.read(4, timeout=self.test_timeout)
            
            write_success = (len(write_response) == 4 and write_response[1] == StatusCode.OK)
            
            if write_success:
                # Verify by reading back each location
                all_correct = True
                for i, expected_value in enumerate(test_data):
                    addr = 0x40001000 + i * 4
                    
                    read_frame = self.protocol.build_read_frame(
                        address=addr, size=2, length=1, auto_increment=False
                    )
                    
                    self.host_uart.write(read_frame)
                    read_response = self.host_uart.read(12, timeout=self.test_timeout)
                    
                    if len(read_response) == 12 and read_response[1] == StatusCode.OK:
                        read_value = struct.unpack('<I', read_response[7:11])[0]
                        if read_value != expected_value:
                            all_correct = False
                            break
                    else:
                        all_correct = False
                        break
                
                success = all_correct
                error_msg = "" if success else "Burst data verification failed"
            else:
                success = False
                error_msg = f"Burst write failed: {write_response.hex() if write_response else 'timeout'}"
            
            result = TestResult(
                name="4×32-bit Burst Write",
                passed=success,
                description="Burst write with auto-increment",
                error_message=error_msg,
                execution_time=time.time() - start_time
            )
            
        except Exception as e:
            result = TestResult(
                name="4×32-bit Burst Write",
                passed=False,
                description="Burst write with auto-increment",
                error_message=str(e),
                execution_time=time.time() - start_time
            )
        
        self.test_results.append(result)
        self._print_result(result)
        
        # Test 4.2: Burst read with auto-increment
        start_time = time.time()
        try:
            # Read back the burst data
            read_frame = self.protocol.build_read_frame(
                address=0x40001000,
                size=2,  # 32-bit
                length=4,  # 4 beats
                auto_increment=True
            )
            
            self.host_uart.write(read_frame)
            expected_len = 8 + 16  # SOF + STATUS + CMD + ADDR + 4×4bytes data + CRC
            read_response = self.host_uart.read(expected_len, timeout=self.test_timeout)
            
            if len(read_response) == expected_len and read_response[1] == StatusCode.OK:
                # Extract and verify data
                data_bytes = read_response[7:23]  # 16 bytes of data
                read_values = [struct.unpack('<I', data_bytes[i:i+4])[0] for i in range(0, 16, 4)]
                
                expected_values = [(i * 0x11111111) & 0xFFFFFFFF for i in range(4)]
                success = (read_values == expected_values)
                error_msg = "" if success else f"Data mismatch: expected {expected_values}, got {read_values}"
            else:
                success = False
                error_msg = f"Burst read failed: {read_response.hex() if read_response else 'timeout'}"
            
            result = TestResult(
                name="4×32-bit Burst Read",
                passed=success,
                description="Burst read with auto-increment",
                error_message=error_msg,
                execution_time=time.time() - start_time
            )
            
        except Exception as e:
            result = TestResult(
                name="4×32-bit Burst Read",
                passed=False,
                description="Burst read with auto-increment",
                error_message=str(e),
                execution_time=time.time() - start_time
            )
        
        self.test_results.append(result)
        self._print_result(result)
    
    def _run_edge_case_tests(self):
        """Test edge cases and boundary conditions"""
        print("\n5. Edge Case Tests")
        print("-" * 30)
        
        # Test 5.1: Maximum length operation (16 beats)
        start_time = time.time()
        try:
            # Create 16×8-bit data
            data_bytes = bytes(range(16))
            
            write_frame = self.protocol.build_write_frame(
                address=0x40002000,
                data=data_bytes,
                size=0,  # 8-bit
                auto_increment=True
            )
            
            self.host_uart.write(write_frame)
            response = self.host_uart.read(4, timeout=self.test_timeout)
            
            success = (len(response) == 4 and response[1] == StatusCode.OK)
            error_msg = "" if success else f"Max length write failed: {response.hex() if response else 'timeout'}"
            
            result = TestResult(
                name="Maximum Length Operation",
                passed=success,
                description="16-beat write operation",
                error_message=error_msg,
                execution_time=time.time() - start_time
            )
            
        except Exception as e:
            result = TestResult(
                name="Maximum Length Operation",
                passed=False,
                description="16-beat write operation",
                error_message=str(e),
                execution_time=time.time() - start_time
            )
        
        self.test_results.append(result)
        self._print_result(result)
        
        # Test 5.2: Fixed address mode (no auto-increment)
        result = self._test_fixed_address_mode()
        self.test_results.append(result)
        self._print_result(result)
    
    def _test_fixed_address_mode(self) -> TestResult:
        """Test fixed address mode (no auto-increment)"""
        start_time = time.time()
        
        try:
            # Write multiple times to same address
            test_values = [0xAA, 0xBB, 0xCC]
            
            for value in test_values:
                write_frame = self.protocol.build_write_frame(
                    address=0x40003000,
                    data=bytes([value]),
                    size=0,  # 8-bit
                    auto_increment=False
                )
                
                self.host_uart.write(write_frame)
                response = self.host_uart.read(4, timeout=self.test_timeout)
                
                if len(response) != 4 or response[1] != StatusCode.OK:
                    return TestResult(
                        name="Fixed Address Mode",
                        passed=False,
                        description="Multiple writes to same address",
                        error_message=f"Write failed for value 0x{value:02X}",
                        execution_time=time.time() - start_time
                    )
            
            # Read back the final value
            read_frame = self.protocol.build_read_frame(
                address=0x40003000, size=0, length=1, auto_increment=False
            )
            
            self.host_uart.write(read_frame)
            read_response = self.host_uart.read(9, timeout=self.test_timeout)
            
            if len(read_response) == 9 and read_response[1] == StatusCode.OK:
                final_value = read_response[7]  # Data byte
                success = (final_value == test_values[-1])  # Should be last written value
                error_msg = "" if success else f"Expected 0x{test_values[-1]:02X}, got 0x{final_value:02X}"
            else:
                success = False
                error_msg = f"Read failed: {read_response.hex() if read_response else 'timeout'}"
            
            return TestResult(
                name="Fixed Address Mode",
                passed=success,
                description="Multiple writes to same address",
                error_message=error_msg,
                execution_time=time.time() - start_time
            )
            
        except Exception as e:
            return TestResult(
                name="Fixed Address Mode",
                passed=False,
                description="Multiple writes to same address",
                error_message=str(e),
                execution_time=time.time() - start_time
            )
    
    def _run_performance_tests(self):
        """Test performance characteristics"""
        print("\n6. Performance Tests")
        print("-" * 30)
        
        # Test 6.1: Latency measurement
        start_time = time.time()
        
        latencies = []
        for i in range(10):
            operation_start = time.time()
            
            # Single 32-bit read
            read_frame = self.protocol.build_read_frame(
                address=0x40000000, size=2, length=1, auto_increment=False
            )
            
            self.host_uart.write(read_frame)
            response = self.host_uart.read(12, timeout=self.test_timeout)
            
            operation_end = time.time()
            
            if len(response) == 12 and response[1] == StatusCode.OK:
                latencies.append(operation_end - operation_start)
            
        if latencies:
            avg_latency = sum(latencies) / len(latencies)
            min_latency = min(latencies)
            max_latency = max(latencies)
            
            result = TestResult(
                name="Latency Measurement",
                passed=True,
                description="Single 32-bit read latency",
                execution_time=time.time() - start_time,
                additional_data={
                    "avg_latency_ms": avg_latency * 1000,
                    "min_latency_ms": min_latency * 1000,
                    "max_latency_ms": max_latency * 1000,
                    "samples": len(latencies)
                }
            )
        else:
            result = TestResult(
                name="Latency Measurement",
                passed=False,
                description="Single 32-bit read latency",
                error_message="No successful operations",
                execution_time=time.time() - start_time
            )
        
        self.test_results.append(result)
        self._print_result(result)
    
    def _print_result(self, result: TestResult):
        """Print formatted test result"""
        status = "✓ PASS" if result.passed else "✗ FAIL"
        print(f"{status:8} {result.name:30} ({result.execution_time*1000:.1f}ms)")
        
        if not result.passed and result.error_message:
            print(f"         Error: {result.error_message}")
        
        if result.additional_data:
            for key, value in result.additional_data.items():
                if isinstance(value, float):
                    print(f"         {key}: {value:.3f}")
                else:
                    print(f"         {key}: {value}")
    
    def _generate_summary(self) -> Dict[str, Any]:
        """Generate test summary report"""
        total_tests = len(self.test_results)
        passed_tests = sum(1 for r in self.test_results if r.passed)
        failed_tests = total_tests - passed_tests
        
        total_time = sum(r.execution_time for r in self.test_results)
        
        # Get bridge statistics
        bridge_stats = self.bridge.get_statistics()
        
        summary = {
            "test_summary": {
                "total_tests": total_tests,
                "passed": passed_tests,
                "failed": failed_tests,
                "pass_rate": (passed_tests / total_tests * 100) if total_tests > 0 else 0,
                "total_execution_time": total_time
            },
            "bridge_statistics": bridge_stats,
            "detailed_results": self.test_results
        }
        
        print(f"\n" + "=" * 60)
        print("TEST SUMMARY")
        print("=" * 60)
        print(f"Total Tests:     {total_tests}")
        print(f"Passed:          {passed_tests}")
        print(f"Failed:          {failed_tests}")
        print(f"Pass Rate:       {summary['test_summary']['pass_rate']:.1f}%")
        print(f"Execution Time:  {total_time:.3f}s")
        print()
        print("Bridge Statistics:")
        for key, value in bridge_stats.items():
            print(f"  {key:20}: {value}")
        
        return summary


if __name__ == "__main__":
    # Configure logging
    logging.basicConfig(level=logging.WARNING,  # Reduce verbosity for test output
                       format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    
    # Run comprehensive test suite
    test_suite = ProtocolTestSuite()
    summary = test_suite.run_all_tests()
    
    # Save results to file for documentation
    import json
    with open('protocol_test_results.json', 'w') as f:
        # Convert TestResult objects to dict for JSON serialization
        serializable_summary = {
            "test_summary": summary["test_summary"],
            "bridge_statistics": summary["bridge_statistics"],
            "detailed_results": [
                {
                    "name": r.name,
                    "passed": r.passed,
                    "description": r.description,
                    "error_message": r.error_message,
                    "execution_time": r.execution_time,
                    "additional_data": r.additional_data
                }
                for r in summary["detailed_results"]
            ]
        }
        json.dump(serializable_summary, f, indent=2)
    
    print(f"\nDetailed results saved to: protocol_test_results.json")
    
    # Exit with appropriate code
    failed_count = summary["test_summary"]["failed"]
    exit(0 if failed_count == 0 else 1)