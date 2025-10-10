#!/usr/bin/env python3
"""
Virtual UART-AXI4 Bridge Simulator
==================================

This module simulates the behavior of the UART-AXI4-Lite bridge for protocol verification.
It implements a virtual AXI4-Lite slave and responds to UART protocol frames.

Features:
- Virtual AXI4-Lite memory space simulation
- Protocol frame parsing and response generation
- Error condition simulation (alignment, timeout, etc.)
- Configurable response delays and error injection

Author: Protocol Verification Team
Date: October 2025
Version: 1.0
"""

import threading
import time
import logging
from typing import Dict, Optional, Callable
from uart_axi4_protocol import (
    UartAxi4Protocol, VirtualUartInterface, ProtocolFrame, 
    StatusCode, CommandFields
)


class VirtualAxiMemory:
    """
    Virtual AXI4-Lite memory space simulation
    Supports configurable regions with different behaviors
    """
    
    def __init__(self):
        # Memory regions with different behaviors
        self.memory_regions = {
            'normal': {
                'range': (0x40000000, 0x4000FFFF),
                'data': {},
                'response': StatusCode.OK,
                'delay_cycles': 1
            },
            'slow': {
                'range': (0x50000000, 0x5000FFFF),
                'data': {},
                'response': StatusCode.OK,
                'delay_cycles': 100  # Slow response
            },
            'error': {
                'range': (0x60000000, 0x6000FFFF),
                'data': {},
                'response': StatusCode.AXI_SLVERR,
                'delay_cycles': 1
            },
            'timeout': {
                'range': (0x70000000, 0x7000FFFF),
                'data': {},
                'response': StatusCode.TIMEOUT,
                'delay_cycles': 1000  # Timeout simulation
            }
        }
        
        # Initialize some test registers
        self._init_test_registers()
        self.logger = logging.getLogger(__name__)
    
    def _init_test_registers(self):
        """Initialize test registers with known values"""
        normal_mem = self.memory_regions['normal']['data']
        
        # Test registers for verification
        normal_mem[0x40000000] = 0xDEADBEEF  # 32-bit test value
        normal_mem[0x40000004] = 0x12345678  # Another 32-bit value
        normal_mem[0x40000008] = 0xA5A5A5A5  # Pattern value
        normal_mem[0x4000000C] = 0x00000000  # Zero value
        
        # 16-bit test values (stored as 32-bit)
        normal_mem[0x40000010] = 0x0000CAFE  # 16-bit in lower half
        normal_mem[0x40000014] = 0xBEEF0000  # 16-bit in upper half
        
        # 8-bit test values
        normal_mem[0x40000020] = 0x000000AA  # Byte 0
        normal_mem[0x40000024] = 0x0000BB00  # Byte 1
        normal_mem[0x40000028] = 0x00CC0000  # Byte 2
        normal_mem[0x4000002C] = 0xDD000000  # Byte 3
        
        # Counter register that increments on each read
        normal_mem[0x40000100] = 0x00000001
    
    def _find_region(self, address: int) -> Optional[str]:
        """Find which memory region contains the address"""
        for region_name, region_info in self.memory_regions.items():
            start, end = region_info['range']
            if start <= address <= end:
                return region_name
        return None
    
    def read(self, address: int, size: int) -> tuple[int, int]:
        """
        Read from virtual AXI memory
        
        Args:
            address: 32-bit address
            size: 0=8-bit, 1=16-bit, 2=32-bit
            
        Returns:
            (data_value, status_code)
        """
        region_name = self._find_region(address)
        if not region_name:
            self.logger.warning(f"Read from unmapped address 0x{address:08X}")
            return (0, StatusCode.AXI_SLVERR)
        
        region = self.memory_regions[region_name]
        
        # Simulate response delay
        if region['delay_cycles'] > 10:
            time.sleep(region['delay_cycles'] / 1000.0)  # Convert to seconds
        
        # Check for error response
        if region['response'] != StatusCode.OK:
            return (0, region['response'])
        
        # Special handling for counter register
        if address == 0x40000100:
            current = region['data'].get(address, 0)
            region['data'][address] = (current + 1) & 0xFFFFFFFF
            return (current, StatusCode.OK)
        
        # Get the 32-bit value (default to 0 if not set)
        word_addr = address & ~0x03  # Align to 32-bit boundary
        full_value = region['data'].get(word_addr, 0)
        
        # Extract the requested portion based on size and address
        if size == 0:  # 8-bit
            byte_offset = address & 0x03
            value = (full_value >> (byte_offset * 8)) & 0xFF
        elif size == 1:  # 16-bit
            half_offset = (address & 0x02) >> 1
            value = (full_value >> (half_offset * 16)) & 0xFFFF
        else:  # 32-bit
            value = full_value
        
        self.logger.debug(f"AXI Read: 0x{address:08X} size={size} -> 0x{value:X}")
        return (value, StatusCode.OK)
    
    def write(self, address: int, data: int, size: int) -> int:
        """
        Write to virtual AXI memory
        
        Args:
            address: 32-bit address
            data: Data value to write
            size: 0=8-bit, 1=16-bit, 2=32-bit
            
        Returns:
            status_code
        """
        region_name = self._find_region(address)
        if not region_name:
            self.logger.warning(f"Write to unmapped address 0x{address:08X}")
            return StatusCode.AXI_SLVERR
        
        region = self.memory_regions[region_name]
        
        # Simulate response delay
        if region['delay_cycles'] > 10:
            time.sleep(region['delay_cycles'] / 1000.0)  # Convert to seconds
        
        # Check for error response
        if region['response'] != StatusCode.OK:
            return region['response']
        
        # Get current 32-bit value
        word_addr = address & ~0x03  # Align to 32-bit boundary
        current_value = region['data'].get(word_addr, 0)
        
        # Update the appropriate portion based on size and address
        if size == 0:  # 8-bit
            byte_offset = address & 0x03
            mask = 0xFF << (byte_offset * 8)
            new_value = (current_value & ~mask) | ((data & 0xFF) << (byte_offset * 8))
        elif size == 1:  # 16-bit
            half_offset = (address & 0x02) >> 1
            mask = 0xFFFF << (half_offset * 16)
            new_value = (current_value & ~mask) | ((data & 0xFFFF) << (half_offset * 16))
        else:  # 32-bit
            new_value = data & 0xFFFFFFFF
        
        region['data'][word_addr] = new_value
        self.logger.debug(f"AXI Write: 0x{address:08X} size={size} data=0x{data:X}")
        return StatusCode.OK


class UartAxi4BridgeSimulator:
    """
    Virtual UART-AXI4 bridge simulator
    Processes UART frames and generates appropriate responses
    """
    
    def __init__(self, uart_interface: VirtualUartInterface):
        self.uart = uart_interface
        self.axi_memory = VirtualAxiMemory()
        self.protocol = UartAxi4Protocol()
        
        self.running = False
        self.worker_thread = None
        self.logger = logging.getLogger(__name__)
        
        # Statistics
        self.stats = {
            'frames_processed': 0,
            'frames_error': 0,
            'writes_processed': 0,
            'reads_processed': 0
        }
    
    def start(self):
        """Start the bridge simulator in a background thread"""
        if self.running:
            return
        
        self.running = True
        self.worker_thread = threading.Thread(target=self._process_frames, daemon=True)
        self.worker_thread.start()
        self.logger.info("Bridge simulator started")
    
    def stop(self):
        """Stop the bridge simulator"""
        self.running = False
        if self.worker_thread:
            self.worker_thread.join(timeout=1.0)
        self.logger.info("Bridge simulator stopped")
    
    def _process_frames(self):
        """Main processing loop for incoming UART frames"""
        while self.running:
            try:
                # Check for incoming data
                if self.uart.available() == 0:
                    time.sleep(0.001)  # 1ms sleep to avoid busy waiting
                    continue
                
                # Try to read a complete frame
                frame_bytes = self._read_frame()
                if not frame_bytes:
                    continue
                
                # Process the frame
                self._handle_frame(frame_bytes)
                
            except Exception as e:
                self.logger.error(f"Error processing frame: {e}")
                self.stats['frames_error'] += 1
    
    def _read_frame(self) -> Optional[bytes]:
        """Read a complete frame from UART"""
        # Look for SOF (0xA5)
        sof_found = False
        while self.uart.available() > 0 and not sof_found:
            byte_data = self.uart.read(1, timeout=0.1)
            if byte_data and byte_data[0] == 0xA5:
                sof_found = True
                break
        
        if not sof_found:
            return None
        
        # Read the rest of the frame
        # Minimum frame is 7 bytes: SOF + CMD + ADDR(4) + CRC
        frame_data = bytearray([0xA5])
        
        # Read CMD byte
        cmd_data = self.uart.read(1, timeout=0.1)
        if not cmd_data:
            return None
        frame_data.extend(cmd_data)
        
        # Parse CMD to determine frame length
        try:
            cmd_fields = CommandFields.from_byte(cmd_data[0])
        except:
            return None
        
        # Read ADDR (4 bytes)
        addr_data = self.uart.read(4, timeout=0.1)
        if len(addr_data) != 4:
            return None
        frame_data.extend(addr_data)
        
        # For write commands, read DATA
        if not cmd_fields.rw:  # Write command
            beat_size = 1 << cmd_fields.size
            data_length = cmd_fields.length * beat_size
            data_payload = self.uart.read(data_length, timeout=0.1)
            if len(data_payload) != data_length:
                return None
            frame_data.extend(data_payload)
        
        # Read CRC byte
        crc_data = self.uart.read(1, timeout=0.1)
        if not crc_data:
            return None
        frame_data.extend(crc_data)
        
        return bytes(frame_data)
    
    def _handle_frame(self, frame_bytes: bytes):
        """Handle a complete frame and generate response"""
        try:
            # Parse the frame
            frame = self.protocol.parse_frame(frame_bytes)
            self.stats['frames_processed'] += 1
            
            # Validate command fields
            if frame.cmd_fields.size > 2:  # Invalid size
                response = self.protocol.build_response_frame(
                    frame.cmd_fields.to_byte(), StatusCode.CMD_INV)
                self.uart.write(response)
                return
            
            if frame.cmd_fields.length > 16:  # Invalid length
                response = self.protocol.build_response_frame(
                    frame.cmd_fields.to_byte(), StatusCode.LEN_RANGE)
                self.uart.write(response)
                return
            
            # Check address alignment
            if not self._check_alignment(frame.address, frame.cmd_fields.size):
                response = self.protocol.build_response_frame(
                    frame.cmd_fields.to_byte(), StatusCode.ADDR_ALIGN)
                self.uart.write(response)
                return
            
            # Process based on command type
            if frame.cmd_fields.rw:  # Read command
                self._handle_read_command(frame)
            else:  # Write command
                self._handle_write_command(frame)
                
        except ValueError as e:
            # CRC error or frame format error
            self.logger.warning(f"Frame parsing error: {e}")
            self.stats['frames_error'] += 1
            # For frame errors, we can't reliably extract CMD, so no response
    
    def _check_alignment(self, address: int, size: int) -> bool:
        """Check address alignment for given size"""
        if size == 1 and (address & 0x01):  # 16-bit must be 2-byte aligned
            return False
        elif size == 2 and (address & 0x03):  # 32-bit must be 4-byte aligned
            return False
        return True
    
    def _handle_read_command(self, frame: ProtocolFrame):
        """Handle read command and send response"""
        self.stats['reads_processed'] += 1
        
        cmd_byte = frame.cmd_fields.to_byte()
        address = frame.address
        
        # Collect read data for all beats
        read_data = bytearray()
        
        for beat in range(frame.cmd_fields.length):
            # Calculate address for this beat
            if frame.cmd_fields.inc:
                beat_addr = address + beat * (1 << frame.cmd_fields.size)
            else:
                beat_addr = address
            
            # Perform AXI read
            data, status = self.axi_memory.read(beat_addr, frame.cmd_fields.size)
            
            if status != StatusCode.OK:
                # Send error response
                response = self.protocol.build_response_frame(cmd_byte, status)
                self.uart.write(response)
                return
            
            # Append data in little-endian format
            if frame.cmd_fields.size == 0:  # 8-bit
                read_data.append(data & 0xFF)
            elif frame.cmd_fields.size == 1:  # 16-bit
                read_data.extend([(data >> 0) & 0xFF, (data >> 8) & 0xFF])
            else:  # 32-bit
                read_data.extend([
                    (data >> 0) & 0xFF, (data >> 8) & 0xFF,
                    (data >> 16) & 0xFF, (data >> 24) & 0xFF
                ])
        
        # Send successful read response
        response = self.protocol.build_response_frame(
            cmd_byte, StatusCode.OK, address, bytes(read_data))
        self.uart.write(response)
    
    def _handle_write_command(self, frame: ProtocolFrame):
        """Handle write command and send response"""
        self.stats['writes_processed'] += 1
        
        cmd_byte = frame.cmd_fields.to_byte()
        address = frame.address
        data_bytes = frame.data
        
        # Process each beat
        beat_size = 1 << frame.cmd_fields.size
        
        for beat in range(frame.cmd_fields.length):
            # Calculate address for this beat
            if frame.cmd_fields.inc:
                beat_addr = address + beat * beat_size
            else:
                beat_addr = address
            
            # Extract data for this beat (little-endian)
            data_offset = beat * beat_size
            beat_data = data_bytes[data_offset:data_offset + beat_size]
            
            # Convert to integer (little-endian)
            if frame.cmd_fields.size == 0:  # 8-bit
                data_value = beat_data[0]
            elif frame.cmd_fields.size == 1:  # 16-bit
                data_value = beat_data[0] | (beat_data[1] << 8)
            else:  # 32-bit
                data_value = (beat_data[0] | (beat_data[1] << 8) |
                             (beat_data[2] << 16) | (beat_data[3] << 24))
            
            # Perform AXI write
            status = self.axi_memory.write(beat_addr, data_value, frame.cmd_fields.size)
            
            if status != StatusCode.OK:
                # Send error response
                response = self.protocol.build_response_frame(cmd_byte, status)
                self.uart.write(response)
                return
        
        # Send successful write response
        response = self.protocol.build_response_frame(cmd_byte, StatusCode.OK)
        self.uart.write(response)
    
    def get_statistics(self) -> Dict[str, int]:
        """Get processing statistics"""
        return self.stats.copy()


if __name__ == "__main__":
    # Test the bridge simulator
    import sys
    sys.path.append('.')
    
    from uart_axi4_protocol import VirtualUartPair
    
    # Configure logging
    logging.basicConfig(level=logging.INFO,
                       format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    
    print("UART-AXI4 Bridge Simulator Test")
    print("=" * 40)
    
    # Create virtual UART pair
    uart_pair = VirtualUartPair()
    host_uart = uart_pair.get_host_interface()
    device_uart = uart_pair.get_device_interface()
    
    # Create and start bridge simulator
    bridge = UartAxi4BridgeSimulator(device_uart)
    bridge.start()
    
    # Create protocol instance for host side
    protocol = UartAxi4Protocol()
    
    try:
        # Test 1: Simple 32-bit write
        print("\n1. Testing 32-bit write...")
        write_frame = protocol.build_write_frame(
            address=0x40000000,
            data=bytes([0xEF, 0xBE, 0xAD, 0xDE]),  # 0xDEADBEEF in little-endian
            size=2,  # 32-bit
            auto_increment=False
        )
        
        host_uart.write(write_frame)
        time.sleep(0.1)  # Wait for processing
        
        # Read response
        response_data = host_uart.read(4, timeout=1.0)  # Expect: SOF + STATUS + CMD + CRC
        if len(response_data) == 4:
            sof, status, cmd, crc = response_data
            print(f"Write response: SOF=0x{sof:02X}, STATUS=0x{status:02X}, CMD=0x{cmd:02X}, CRC=0x{crc:02X}")
            if status == StatusCode.OK:
                print("✓ Write successful")
            else:
                print(f"✗ Write failed with status 0x{status:02X}")
        else:
            print(f"✗ Unexpected response length: {len(response_data)} bytes")
        
        # Test 2: Read back the written value
        print("\n2. Testing 32-bit read...")
        read_frame = protocol.build_read_frame(
            address=0x40000000,
            size=2,  # 32-bit
            length=1,
            auto_increment=False
        )
        
        host_uart.write(read_frame)
        time.sleep(0.1)  # Wait for processing
        
        # Read response (should be longer for successful read)
        response_data = host_uart.read(12, timeout=1.0)  # SOF + STATUS + CMD + ADDR + DATA + CRC
        if len(response_data) >= 8:
            print(f"Read response ({len(response_data)} bytes): {' '.join(f'0x{b:02X}' for b in response_data)}")
            if response_data[1] == StatusCode.OK:
                # Extract data (bytes 7-10)
                if len(response_data) >= 12:
                    data_bytes = response_data[7:11]
                    data_value = (data_bytes[0] | (data_bytes[1] << 8) |
                                 (data_bytes[2] << 16) | (data_bytes[3] << 24))
                    print(f"✓ Read successful: 0x{data_value:08X}")
                else:
                    print("✗ Response too short for data")
            else:
                print(f"✗ Read failed with status 0x{response_data[1]:02X}")
        else:
            print(f"✗ Unexpected response length: {len(response_data)} bytes")
        
        # Test 3: Address alignment error
        print("\n3. Testing alignment error...")
        misaligned_frame = protocol.build_write_frame(
            address=0x40000001,  # Misaligned for 32-bit
            data=bytes([0xAA, 0xBB, 0xCC, 0xDD]),
            size=2,  # 32-bit
            auto_increment=False
        )
        
        host_uart.write(misaligned_frame)
        time.sleep(0.1)
        
        response_data = host_uart.read(4, timeout=1.0)
        if len(response_data) == 4:
            status = response_data[1]
            if status == StatusCode.ADDR_ALIGN:
                print("✓ Alignment error correctly detected")
            else:
                print(f"✗ Expected alignment error, got status 0x{status:02X}")
        
        # Show statistics
        print(f"\nBridge Statistics: {bridge.get_statistics()}")
        
    finally:
        bridge.stop()
    
    print("\nBridge simulator test completed!")