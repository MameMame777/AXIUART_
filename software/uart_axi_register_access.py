#!/usr/bin/env python3
"""
UART-AXI4-Lite Bridge Register Access Tool
Protocol v0.1 compliant implementation

This script provides register access functionality to FPGA via UART
following the UART-AXI4-Lite Bridge Protocol specification.
"""

import serial
import time
import struct
from typing import Optional, Union, List, Tuple
from enum import IntEnum

class StatusCode(IntEnum):
    """Protocol status codes as defined in Section 3"""
    OK = 0x00           # Success
    CRC_ERR = 0x01      # CRC mismatch on received frame
    CMD_INV = 0x02      # Unsupported/illegal CMD
    ADDR_ALIGN = 0x03   # Address/size alignment error
    TIMEOUT = 0x04      # AXI or internal timeout
    AXI_SLVERR = 0x05   # AXI response SLVERR/DECERR
    BUSY = 0x06         # Device busy/resource contention
    LEN_RANGE = 0x07    # LEN exceeds supported maximum
    PARAM = 0x08        # Other parameter error

class AccessSize(IntEnum):
    """Data access sizes"""
    BYTE = 0    # 8-bit
    WORD = 1    # 16-bit
    DWORD = 2   # 32-bit

class UartAxiBridge:
    """UART-AXI4-Lite Bridge Protocol Implementation"""
    
    # Protocol constants
    SOF_HOST_TO_DEVICE = 0xA5
    SOF_DEVICE_TO_HOST = 0x5A
    
    def __init__(self, port: str = "COM3", baudrate: int = 115200, timeout: float = 1.0):
        """
        Initialize UART-AXI bridge connection
        
        Args:
            port: Serial port name (default: COM3)
            baudrate: UART baud rate (default: 115200)
            timeout: Communication timeout in seconds
        """
        self.port = port
        self.baudrate = baudrate
        self.timeout = timeout
        self.serial = None
        self.max_retries = 3
        self.retry_delay = 0.1  # seconds
        
    def connect(self) -> bool:
        """
        Open UART connection
        
        Returns:
            True if successful, False otherwise
        """
        try:
            self.serial = serial.Serial(
                port=self.port,
                baudrate=self.baudrate,
                bytesize=serial.EIGHTBITS,
                parity=serial.PARITY_NONE,
                stopbits=serial.STOPBITS_ONE,
                timeout=self.timeout,
                write_timeout=self.timeout
            )
            print(f"✅ Connected to {self.port} at {self.baudrate} baud")
            return True
        except Exception as e:
            print(f"❌ Failed to connect to {self.port}: {e}")
            return False
    
    def disconnect(self):
        """Close UART connection"""
        if self.serial and self.serial.is_open:
            self.serial.close()
            print("🔌 Disconnected from UART")
    
    def crc8_calculate(self, data: bytes) -> int:
        """
        Calculate CRC8 using polynomial 0x07
        
        Args:
            data: Input data bytes
            
        Returns:
            CRC8 value (0x00-0xFF)
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
    
    def build_write_frame(self, addr: int, data: Union[int, List[int]], 
                         size: AccessSize, auto_inc: bool = False) -> bytes:
        """
        Build write command frame
        
        Args:
            addr: 32-bit address
            data: Data to write (int for single value, List[int] for multiple)
            size: Access size (BYTE/WORD/DWORD)
            auto_inc: Enable address auto-increment
            
        Returns:
            Complete frame bytes
        """
        if isinstance(data, int):
            data = [data]
        
        if len(data) > 16:
            raise ValueError("Maximum 16 beats supported")
        
        # Build CMD byte: RW=0, INC, SIZE, LEN
        cmd = 0x00  # RW=0 (write)
        if auto_inc:
            cmd |= 0x40  # INC=1
        cmd |= (size << 4)  # SIZE field
        cmd |= (len(data) - 1)  # LEN field (0-based)
        
        # Start frame
        frame = bytearray()
        frame.append(self.SOF_HOST_TO_DEVICE)
        frame.append(cmd)
        
        # Address (little-endian)
        frame.extend(struct.pack('<I', addr))
        
        # Data payload
        bytes_per_beat = 1 << size
        for value in data:
            if size == AccessSize.BYTE:
                frame.extend(struct.pack('<B', value & 0xFF))
            elif size == AccessSize.WORD:
                frame.extend(struct.pack('<H', value & 0xFFFF))
            elif size == AccessSize.DWORD:
                frame.extend(struct.pack('<I', value & 0xFFFFFFFF))
        
        # CRC8 (from CMD through end of data)
        crc = self.crc8_calculate(frame[1:])
        frame.append(crc)
        
        return bytes(frame)
    
    def build_read_frame(self, addr: int, count: int, size: AccessSize, 
                        auto_inc: bool = False) -> bytes:
        """
        Build read command frame
        
        Args:
            addr: 32-bit address
            count: Number of beats to read (1-16)
            size: Access size (BYTE/WORD/DWORD)
            auto_inc: Enable address auto-increment
            
        Returns:
            Complete frame bytes
        """
        if count < 1 or count > 16:
            raise ValueError("Count must be 1-16")
        
        # Build CMD byte: RW=1, INC, SIZE, LEN
        cmd = 0x80  # RW=1 (read)
        if auto_inc:
            cmd |= 0x40  # INC=1
        cmd |= (size << 4)  # SIZE field
        cmd |= (count - 1)  # LEN field (0-based)
        
        # Build frame
        frame = bytearray()
        frame.append(self.SOF_HOST_TO_DEVICE)
        frame.append(cmd)
        
        # Address (little-endian)
        frame.extend(struct.pack('<I', addr))
        
        # CRC8 (from CMD through ADDR)
        crc = self.crc8_calculate(frame[1:])
        frame.append(crc)
        
        return bytes(frame)
    
    def parse_response(self, response: bytes) -> Tuple[int, Optional[List[int]]]:
        """
        Parse response frame
        
        Args:
            response: Raw response bytes
            
        Returns:
            Tuple of (status_code, data_list) where data_list is None for errors
        """
        if len(response) < 4:
            raise ValueError("Response too short")
        
        if response[0] != self.SOF_DEVICE_TO_HOST:
            raise ValueError(f"Invalid SOF: expected 0x{self.SOF_DEVICE_TO_HOST:02X}, got 0x{response[0]:02X}")
        
        status = response[1]
        cmd_echo = response[2]
        
        if status != StatusCode.OK:
            # Error response: SOF | STATUS | CMD | CRC
            if len(response) != 4:
                raise ValueError("Invalid error response length")
            expected_crc = self.crc8_calculate(response[1:3])
            if response[3] != expected_crc:
                raise ValueError("CRC mismatch in error response")
            return status, None
        
        # Success response for read: SOF | STATUS | CMD | ADDR | DATA | CRC
        if len(response) < 8:
            raise ValueError("Success response too short")
        
        # Extract data based on CMD
        rw_bit = (cmd_echo >> 7) & 1
        size = (cmd_echo >> 4) & 3
        length = (cmd_echo & 0xF) + 1
        
        if rw_bit == 0:
            # Write response: no data
            expected_crc = self.crc8_calculate(response[1:3])
            if response[3] != expected_crc:
                raise ValueError("CRC mismatch in write response")
            return status, []
        else:
            # Read response: extract data
            addr_end = 7  # SOF + STATUS + CMD + ADDR(4)
            bytes_per_beat = 1 << size
            data_bytes = length * bytes_per_beat
            data_end = addr_end + data_bytes
            
            if len(response) != data_end + 1:
                raise ValueError("Invalid read response length")
            
            # Verify CRC
            expected_crc = self.crc8_calculate(response[1:data_end])
            if response[data_end] != expected_crc:
                raise ValueError("CRC mismatch in read response")
            
            # Extract data values
            data_list = []
            data_payload = response[addr_end:data_end]
            
            for i in range(length):
                offset = i * bytes_per_beat
                if size == AccessSize.BYTE:
                    value = struct.unpack('<B', data_payload[offset:offset+1])[0]
                elif size == AccessSize.WORD:
                    value = struct.unpack('<H', data_payload[offset:offset+2])[0]
                elif size == AccessSize.DWORD:
                    value = struct.unpack('<I', data_payload[offset:offset+4])[0]
                data_list.append(value)
            
            return status, data_list
    
    def send_frame_with_retry(self, frame: bytes) -> bytes:
        """
        Send frame and receive response with retry logic
        
        Args:
            frame: Frame to send
            
        Returns:
            Response bytes
        """
        if not self.serial or not self.serial.is_open:
            raise RuntimeError("UART not connected")
        
        for attempt in range(self.max_retries):
            try:
                # Clear any pending data
                self.serial.reset_input_buffer()
                
                # Send frame
                self.serial.write(frame)
                self.serial.flush()
                
                # Wait for response (read until timeout or sufficient data)
                response = bytearray()
                start_time = time.time()
                
                while time.time() - start_time < self.timeout:
                    if self.serial.in_waiting > 0:
                        chunk = self.serial.read(self.serial.in_waiting)
                        response.extend(chunk)
                        
                        # Check if we have at least a minimal response
                        if len(response) >= 4:
                            # For error responses, 4 bytes is complete
                            if len(response) >= 4 and response[1] != StatusCode.OK:
                                break
                            # For success responses, we need more data
                            elif len(response) >= 8:
                                # Check if this looks like a complete read response
                                cmd_echo = response[2]
                                rw_bit = (cmd_echo >> 7) & 1
                                if rw_bit == 0:  # Write response
                                    if len(response) >= 4:
                                        break
                                else:  # Read response
                                    size = (cmd_echo >> 4) & 3
                                    length = (cmd_echo & 0xF) + 1
                                    expected_len = 7 + (length * (1 << size)) + 1
                                    if len(response) >= expected_len:
                                        break
                    time.sleep(0.01)
                
                if len(response) >= 4:
                    return bytes(response)
                
                # If no response, retry
                print(f"⚠️ Attempt {attempt + 1} failed, retrying...")
                time.sleep(self.retry_delay)
                
            except Exception as e:
                print(f"⚠️ Attempt {attempt + 1} error: {e}")
                time.sleep(self.retry_delay)
        
        raise RuntimeError(f"Failed to get response after {self.max_retries} attempts")
    
    def write_register(self, addr: int, value: int, size: AccessSize = AccessSize.DWORD) -> bool:
        """
        Write single register
        
        Args:
            addr: Register address
            value: Value to write
            size: Access size
            
        Returns:
            True if successful
        """
        try:
            frame = self.build_write_frame(addr, value, size)
            response = self.send_frame_with_retry(frame)
            status, _ = self.parse_response(response)
            
            if status == StatusCode.OK:
                print(f"✅ Write 0x{value:08X} to 0x{addr:08X} successful")
                return True
            else:
                print(f"❌ Write failed with status 0x{status:02X}")
                return False
                
        except Exception as e:
            print(f"❌ Write error: {e}")
            return False
    
    def read_register(self, addr: int, size: AccessSize = AccessSize.DWORD) -> Optional[int]:
        """
        Read single register
        
        Args:
            addr: Register address
            size: Access size
            
        Returns:
            Register value or None if failed
        """
        try:
            frame = self.build_read_frame(addr, 1, size)
            response = self.send_frame_with_retry(frame)
            status, data = self.parse_response(response)
            
            if status == StatusCode.OK and data:
                value = data[0]
                print(f"✅ Read 0x{addr:08X} = 0x{value:08X}")
                return value
            else:
                print(f"❌ Read failed with status 0x{status:02X}")
                return None
                
        except Exception as e:
            print(f"❌ Read error: {e}")
            return None
    
    def read_burst(self, addr: int, count: int, size: AccessSize = AccessSize.DWORD, 
                  auto_inc: bool = True) -> Optional[List[int]]:
        """
        Read multiple registers
        
        Args:
            addr: Starting address
            count: Number of registers to read (1-16)
            size: Access size
            auto_inc: Enable address auto-increment
            
        Returns:
            List of values or None if failed
        """
        try:
            frame = self.build_read_frame(addr, count, size, auto_inc)
            response = self.send_frame_with_retry(frame)
            status, data = self.parse_response(response)
            
            if status == StatusCode.OK and data:
                print(f"✅ Burst read from 0x{addr:08X}, {count} values")
                for i, value in enumerate(data):
                    offset = i * (1 << size) if auto_inc else 0
                    print(f"  [0x{addr + offset:08X}] = 0x{value:08X}")
                return data
            else:
                print(f"❌ Burst read failed with status 0x{status:02X}")
                return None
                
        except Exception as e:
            print(f"❌ Burst read error: {e}")
            return None

def main():
    """Example usage and interactive mode"""
    bridge = UartAxiBridge()
    
    if not bridge.connect():
        return
    
    try:
        print("\n🔧 UART-AXI Register Access Tool")
        print("📋 Available commands:")
        print("  r <addr>           - Read 32-bit register")
        print("  w <addr> <value>   - Write 32-bit register")
        print("  rb <addr> <count>  - Burst read (1-16 registers)")
        print("  test               - Run basic test sequence")
        print("  quit               - Exit")
        
        while True:
            try:
                cmd = input("\n> ").strip().split()
                if not cmd:
                    continue
                
                if cmd[0] == 'quit':
                    break
                elif cmd[0] == 'r' and len(cmd) == 2:
                    addr = int(cmd[1], 0)
                    bridge.read_register(addr)
                elif cmd[0] == 'w' and len(cmd) == 3:
                    addr = int(cmd[1], 0)
                    value = int(cmd[2], 0)
                    bridge.write_register(addr, value)
                elif cmd[0] == 'rb' and len(cmd) == 3:
                    addr = int(cmd[1], 0)
                    count = int(cmd[2])
                    bridge.read_burst(addr, count)
                elif cmd[0] == 'test':
                    print("\n🧪 Running basic test sequence...")
                    # Test addresses from register map
                    test_addresses = [0x00001000, 0x00001004, 0x00001008, 0x0000101C]
                    for addr in test_addresses:
                        bridge.read_register(addr)
                        time.sleep(0.1)
                else:
                    print("❌ Invalid command")
                    
            except KeyboardInterrupt:
                break
            except Exception as e:
                print(f"❌ Command error: {e}")
    
    finally:
        bridge.disconnect()

if __name__ == "__main__":
    main()