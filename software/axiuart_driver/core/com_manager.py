"""
COM Port Manager for AXIUART Driver

Handles serial port communication, connection management, and flow control.
"""

import serial
import serial.tools.list_ports
import time
import threading
from typing import List, Optional


class COMManager:
    """COM Port Manager for UART communication"""
    
    def __init__(self):
        """Initialize COM manager"""
        self.port: Optional[serial.Serial] = None
        self.is_connected = False
        self.port_name = ""
        self.baudrate = 115200
        self.timeout = 0.1
        self._lock = threading.Lock()
    
    def scan_ports(self) -> List[str]:
        """
        Scan for available COM ports
        
        Returns:
            List of available COM port names
        """
        ports = serial.tools.list_ports.comports()
        return [port.device for port in ports]
    
    def list_ports(self) -> List:
        """
        List available COM ports with detailed information
        
        Returns:
            List of port info objects with device, description, etc.
        """
        return list(serial.tools.list_ports.comports())
    
    def connect(self, port_name: str, baudrate: int = 115200, 
                timeout: float = 0.1, flow_control: bool = True) -> bool:
        """
        Connect to specified COM port
        
        Args:
            port_name: COM port name (e.g., "COM3", "/dev/ttyUSB0")
            baudrate: Baud rate (default: 115200)
            timeout: Read timeout in seconds
            flow_control: Enable RTS/CTS flow control
            
        Returns:
            True if connection successful, False otherwise
        """
        try:
            with self._lock:
                if self.is_connected:
                    self.disconnect()
                
                self.port = serial.Serial(
                    port=port_name,
                    baudrate=baudrate,
                    bytesize=serial.EIGHTBITS,
                    parity=serial.PARITY_NONE,
                    stopbits=serial.STOPBITS_ONE,
                    timeout=timeout,
                    xonxoff=False,  # No software flow control
                    rtscts=flow_control,  # Hardware flow control
                    dsrdtr=False
                )
                
                # Clear buffers
                self.port.reset_input_buffer()
                self.port.reset_output_buffer()
                
                self.port_name = port_name
                self.baudrate = baudrate
                self.timeout = timeout
                self.is_connected = True
                
                # Small delay for hardware to stabilize
                time.sleep(0.1)
                
                return True
                
        except Exception as e:
            print(f"Connection failed: {e}")
            return False
    
    def disconnect(self) -> None:
        """Disconnect from COM port"""
        try:
            with self._lock:
                if self.port and self.is_connected:
                    self.port.close()
                    self.port = None
                    self.is_connected = False
                    self.port_name = ""
        except Exception as e:
            print(f"Disconnect error: {e}")
    
    def set_flow_control(self, rts: bool, cts: bool) -> bool:
        """
        Set flow control signals
        
        Args:
            rts: RTS signal state
            cts: Enable CTS checking
            
        Returns:
            True if successful
        """
        try:
            with self._lock:
                if not self.is_connected or not self.port:
                    return False
                
                # Set RTS
                self.port.rts = rts
                
                # CTS is read-only, but we can enable/disable CTS checking
                self.port.rtscts = cts
                
                return True
        except Exception as e:
            print(f"Flow control error: {e}")
            return False
    
    def get_signals(self) -> dict:
        """
        Get current signal states
        
        Returns:
            Dictionary with signal states
        """
        if not self.is_connected or not self.port:
            return {}
        
        try:
            with self._lock:
                return {
                    'rts': self.port.rts,
                    'cts': self.port.cts,
                    'dsr': self.port.dsr,
                    'dtr': self.port.dtr,
                    'cd': self.port.cd,
                    'ri': self.port.ri
                }
        except Exception as e:
            print(f"Signal read error: {e}")
            return {}
    
    def write_data(self, data: bytes) -> int:
        """
        Write data to COM port
        
        Args:
            data: Data bytes to write
            
        Returns:
            Number of bytes written, -1 on error
        """
        if not self.is_connected or not self.port:
            return -1
        
        try:
            with self._lock:
                bytes_written = self.port.write(data)
                self.port.flush()  # Ensure data is sent
                return bytes_written
        except Exception as e:
            print(f"Write error: {e}")
            return -1
    
    def read_data(self, length: int = 1, timeout: Optional[float] = None) -> bytes:
        """
        Read data from COM port
        
        Args:
            length: Number of bytes to read
            timeout: Read timeout (None = use default)
            
        Returns:
            Read data bytes (may be shorter than requested)
        """
        if not self.is_connected or not self.port:
            return b''
        
        try:
            with self._lock:
                old_timeout = self.port.timeout
                if timeout is not None:
                    self.port.timeout = timeout
                
                data = self.port.read(length)
                
                if timeout is not None:
                    self.port.timeout = old_timeout
                
                return data
        except Exception as e:
            print(f"Read error: {e}")
            return b''
    
    def read_until(self, terminator: bytes = b'\x5A', max_length: int = 256, 
                   timeout: float = 1.0) -> bytes:
        """
        Read data until terminator or timeout
        
        Args:
            terminator: Terminator sequence
            max_length: Maximum bytes to read
            timeout: Total timeout
            
        Returns:
            Read data including terminator (if found)
        """
        if not self.is_connected or not self.port:
            return b''
        
        try:
            with self._lock:
                start_time = time.time()
                buffer = b''
                
                while len(buffer) < max_length:
                    if time.time() - start_time > timeout:
                        break
                    
                    byte_data = self.port.read(1)
                    if not byte_data:
                        continue
                    
                    buffer += byte_data
                    
                    # Check for terminator
                    if buffer.endswith(terminator):
                        break
                
                return buffer
        except Exception as e:
            print(f"Read until error: {e}")
            return b''
    
    def clear_buffers(self) -> bool:
        """
        Clear input and output buffers
        
        Returns:
            True if successful
        """
        if not self.is_connected or not self.port:
            return False
        
        try:
            with self._lock:
                self.port.reset_input_buffer()
                self.port.reset_output_buffer()
                return True
        except Exception as e:
            print(f"Buffer clear error: {e}")
            return False
    
    def get_status(self) -> dict:
        """
        Get connection status and information
        
        Returns:
            Status dictionary
        """
        status = {
            'connected': self.is_connected,
            'port_name': self.port_name,
            'baudrate': self.baudrate,
            'timeout': self.timeout
        }
        
        if self.is_connected and self.port:
            status.update({
                'in_waiting': self.port.in_waiting,
                'out_waiting': self.port.out_waiting,
                'signals': self.get_signals()
            })
        
        return status

def test_com_manager():
    """Test COM manager functionality"""
    com = COMManager()
    
    # Test port scanning
    ports = com.scan_ports()
    print(f"Available ports: {ports}")
    
    # Test status when not connected
    status = com.get_status()
    assert status['connected'] == False
    
    print("COM Manager tests completed!")

if __name__ == "__main__":
    test_com_manager()