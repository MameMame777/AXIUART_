"""
UART-AXI4 Protocol Implementation

Implements the UART-AXI4 bridge protocol for register access over serial connection.
Handles frame construction, parsing, and error handling.
"""

import time
from typing import Tuple, List, Optional
from .crc_calculator import CRC8
from .register_map import RegisterMap
from .com_manager import COMManager


class ProtocolError(Exception):
    """Protocol-specific error"""
    pass


class UARTProtocol:
    """UART-AXI4 Protocol Handler"""
    
    # Frame markers
    SOF_REQUEST = 0xA5      # Start of frame for requests (host->device)
    SOF_RESPONSE = 0x5A     # Start of frame for responses (device->host)
    
    # Default timeouts
    DEFAULT_RESPONSE_TIMEOUT = 0.1  # 100ms
    DEFAULT_RETRY_COUNT = 3
    
    def __init__(self, com_manager: COMManager):
        """
        Initialize protocol handler
        
        Args:
            com_manager: COM port manager instance
        """
        self.com = com_manager
        self.response_timeout = self.DEFAULT_RESPONSE_TIMEOUT
        self.retry_count = self.DEFAULT_RETRY_COUNT
        self.stats = {
            'frames_sent': 0,
            'frames_received': 0,
            'crc_errors': 0,
            'timeouts': 0,
            'protocol_errors': 0
        }
    
    def build_read_frame(self, addr: int, size: int = 2, length: int = 1) -> bytes:
        """
        Build read frame
        
        Args:
            addr: Register address
            size: Data size (0=8bit, 1=16bit, 2=32bit)
            length: Number of transfers (1-16)
            
        Returns:
            Complete frame with CRC
        """
        if not (1 <= length <= 16):
            raise ValueError("Length must be 1-16")
        if size not in [0, 1, 2]:
            raise ValueError("Size must be 0, 1, or 2")
        
        # Build command byte
        cmd = RegisterMap.make_cmd_byte(True, size, length, False)
        
        # Build frame: SOF + CMD + ADDR(4 bytes, little-endian)
        frame = bytearray()
        frame.append(self.SOF_REQUEST)
        frame.append(cmd)
        
        # Address in little-endian format
        frame.extend(addr.to_bytes(4, 'little'))
        
        # Add CRC
        crc = CRC8.calculate(frame)
        frame.append(crc)
        
        return bytes(frame)
    
    def build_write_frame(self, addr: int, data: bytes, size: int = 2) -> bytes:
        """
        Build write frame
        
        Args:
            addr: Register address
            data: Data to write
            size: Data size (0=8bit, 1=16bit, 2=32bit)
            
        Returns:
            Complete frame with CRC
        """
        if not data:
            raise ValueError("Data cannot be empty")
        
        # Calculate length based on data size
        size_bytes = [1, 2, 4][size]
        if len(data) % size_bytes != 0:
            raise ValueError(f"Data length must be multiple of {size_bytes}")
        
        length = len(data) // size_bytes
        if not (1 <= length <= 16):
            raise ValueError("Length must be 1-16")
        
        # Build command byte
        cmd = RegisterMap.make_cmd_byte(False, size, length, False)
        
        # Build frame: SOF + CMD + ADDR(4 bytes) + DATA
        frame = bytearray()
        frame.append(self.SOF_REQUEST)
        frame.append(cmd)
        
        # Address in little-endian format
        frame.extend(addr.to_bytes(4, 'little'))
        
        # Data payload
        frame.extend(data)
        
        # Add CRC
        crc = CRC8.calculate(frame)
        frame.append(crc)
        
        return bytes(frame)
    
    def parse_response(self, frame: bytes) -> Tuple[int, bytes]:
        """
        Parse response frame
        
        Args:
            frame: Received frame data
            
        Returns:
            Tuple of (status_code, data)
            
        Raises:
            ProtocolError: On parse errors
        """
        if len(frame) < 3:  # Minimum: SOF + STATUS + CRC
            raise ProtocolError("Frame too short")
        
        # Check SOF
        if frame[0] != self.SOF_RESPONSE:
            raise ProtocolError(f"Invalid SOF: 0x{frame[0]:02X}")
        
        # Extract status and data
        status = frame[1]
        data = frame[2:-1]  # Everything except SOF, STATUS, and CRC
        expected_crc = frame[-1]
        
        # Verify CRC
        calculated_crc = CRC8.calculate(frame[:-1])
        if calculated_crc != expected_crc:
            self.stats['crc_errors'] += 1
            raise ProtocolError(f"CRC error: expected 0x{expected_crc:02X}, got 0x{calculated_crc:02X}")
        
        return status, data
    
    def send_frame_and_receive(self, frame: bytes) -> Tuple[int, bytes]:
        """
        Send frame and wait for response
        
        Args:
            frame: Frame to send
            
        Returns:
            Tuple of (status_code, response_data)
            
        Raises:
            ProtocolError: On communication errors
        """
        if not self.com.is_connected:
            raise ProtocolError("Not connected to COM port")
        
        # Clear buffers
        self.com.clear_buffers()
        
        # Send frame
        bytes_sent = self.com.write_data(frame)
        if bytes_sent != len(frame):
            raise ProtocolError(f"Failed to send complete frame: {bytes_sent}/{len(frame)}")
        
        self.stats['frames_sent'] += 1
        
        # Wait for response
        start_time = time.time()
        response_buffer = b''
        
        # First, wait for SOF
        while time.time() - start_time < self.response_timeout:
            byte_data = self.com.read_data(1, 0.01)
            if byte_data == bytes([self.SOF_RESPONSE]):
                response_buffer = byte_data
                break
        
        if not response_buffer:
            self.stats['timeouts'] += 1
            raise ProtocolError("Timeout waiting for response SOF")
        
        # Read rest of frame (at least STATUS + CRC)
        while len(response_buffer) < 3 and time.time() - start_time < self.response_timeout:
            byte_data = self.com.read_data(1, 0.01)
            if byte_data:
                response_buffer += byte_data
        
        # For read commands, we might need more data
        # Try to read additional bytes if available
        remaining_time = self.response_timeout - (time.time() - start_time)
        if remaining_time > 0:
            extra_data = self.com.read_data(16, min(remaining_time, 0.05))
            response_buffer += extra_data
        
        if len(response_buffer) < 3:
            self.stats['timeouts'] += 1
            raise ProtocolError("Incomplete response frame")
        
        self.stats['frames_received'] += 1
        
        try:
            return self.parse_response(response_buffer)
        except ProtocolError as e:
            self.stats['protocol_errors'] += 1
            raise
    
    def register_read(self, addr: int, size: int = 2) -> int:
        """
        Read register value
        
        Args:
            addr: Register address
            size: Data size (0=8bit, 1=16bit, 2=32bit)
            
        Returns:
            Register value
            
        Raises:
            ProtocolError: On communication or protocol errors
        """
        frame = self.build_read_frame(addr, size, 1)
        
        for attempt in range(self.retry_count):
            try:
                status, data = self.send_frame_and_receive(frame)
                
                if status != RegisterMap.STATUS_SUCCESS:
                    raise ProtocolError(f"Register read failed: status=0x{status:02X}")
                
                # Convert data to integer (little-endian)
                size_bytes = [1, 2, 4][size]
                if len(data) != size_bytes:
                    raise ProtocolError(f"Invalid data length: expected {size_bytes}, got {len(data)}")
                
                value = int.from_bytes(data, 'little')
                return value
                
            except ProtocolError as e:
                if attempt == self.retry_count - 1:
                    raise
                time.sleep(0.01 * (attempt + 1))  # Exponential backoff
        
        raise ProtocolError("Max retries exceeded")
    
    def register_write(self, addr: int, value: int, size: int = 2) -> bool:
        """
        Write register value
        
        Args:
            addr: Register address
            value: Value to write
            size: Data size (0=8bit, 1=16bit, 2=32bit)
            
        Returns:
            True if successful
            
        Raises:
            ProtocolError: On communication or protocol errors
        """
        # Convert value to bytes (little-endian)
        size_bytes = [1, 2, 4][size]
        max_value = (1 << (size_bytes * 8)) - 1
        
        if not (0 <= value <= max_value):
            raise ValueError(f"Value out of range for {size_bytes}-byte size")
        
        data = value.to_bytes(size_bytes, 'little')
        frame = self.build_write_frame(addr, data, size)
        
        for attempt in range(self.retry_count):
            try:
                status, response_data = self.send_frame_and_receive(frame)
                
                if status != RegisterMap.STATUS_SUCCESS:
                    raise ProtocolError(f"Register write failed: status=0x{status:02X}")
                
                return True
                
            except ProtocolError as e:
                if attempt == self.retry_count - 1:
                    raise
                time.sleep(0.01 * (attempt + 1))  # Exponential backoff
        
        raise ProtocolError("Max retries exceeded")
    
    def bulk_read(self, start_addr: int, count: int, size: int = 2) -> List[int]:
        """
        Read multiple consecutive registers
        
        Args:
            start_addr: Starting address
            count: Number of registers to read
            size: Data size per register
            
        Returns:
            List of register values
        """
        values = []
        for i in range(count):
            addr = start_addr + (i * [1, 2, 4][size])
            value = self.register_read(addr, size)
            values.append(value)
        return values
    
    def get_statistics(self) -> dict:
        """
        Get protocol statistics
        
        Returns:
            Statistics dictionary
        """
        return self.stats.copy()
    
    def reset_statistics(self) -> None:
        """Reset protocol statistics"""
        for key in self.stats:
            self.stats[key] = 0

def test_protocol():
    """Test protocol functionality"""
    # This would require actual hardware connection
    print("Protocol tests require hardware connection")
    
    # Test frame building
    protocol = UARTProtocol(None)  # No COM manager for testing
    
    # Test read frame
    frame = protocol.build_read_frame(0x1000, 2, 1)
    expected_length = 1 + 1 + 4 + 1  # SOF + CMD + ADDR + CRC
    assert len(frame) == expected_length
    assert frame[0] == UARTProtocol.SOF_REQUEST
    
    # Test write frame
    data = b'\x01\x00\x00\x00'  # 32-bit value 1
    frame = protocol.build_write_frame(0x1000, data, 2)
    expected_length = 1 + 1 + 4 + 4 + 1  # SOF + CMD + ADDR + DATA + CRC
    assert len(frame) == expected_length
    
    print("Protocol frame building tests passed!")

if __name__ == "__main__":
    test_protocol()