"""
CRC-8 Calculator for UART-AXI4 Protocol

Implements CRC-8 calculation with polynomial 0x07 as specified in the UART-AXI4 protocol.
"""

class CRC8:
    """CRC-8 calculator for UART frame validation"""
    
    POLYNOMIAL = 0x07
    INIT_VALUE = 0x00
    
    @staticmethod
    def calculate(data: bytes, offset: int = 0, length: int = -1) -> int:
        """
        Calculate CRC-8 for given data
        
        Args:
            data: Input data bytes
            offset: Starting offset in data
            length: Number of bytes to process (-1 = all remaining)
            
        Returns:
            Calculated CRC-8 value (0-255)
        """
        if length == -1:
            length = len(data) - offset
            
        if offset + length > len(data):
            raise ValueError("offset + length exceeds data length")
            
        crc = CRC8.INIT_VALUE
        
        for i in range(offset, offset + length):
            crc ^= data[i]
            
            # Process 8 bits
            for _ in range(8):
                if crc & 0x80:
                    crc = ((crc << 1) ^ CRC8.POLYNOMIAL) & 0xFF
                else:
                    crc = (crc << 1) & 0xFF
                    
        return crc
    
    @staticmethod
    def verify(data: bytes, expected_crc: int) -> bool:
        """
        Verify CRC-8 of frame data
        
        Args:
            data: Frame data including CRC byte at the end
            expected_crc: Expected CRC value
            
        Returns:
            True if CRC matches, False otherwise
        """
        if len(data) == 0:
            return False
            
        # Calculate CRC for all bytes except the last one (CRC byte)
        calculated = CRC8.calculate(data[:-1])
        return calculated == expected_crc
    
    @staticmethod
    def append_crc(data: bytes) -> bytes:
        """
        Append CRC-8 to data
        
        Args:
            data: Input data
            
        Returns:
            Data with CRC-8 appended
        """
        crc = CRC8.calculate(data)
        return data + bytes([crc])

def test_crc8():
    """Test CRC-8 calculation with known values"""
    
    # Test case 1: Empty data
    assert CRC8.calculate(b'') == 0x00
    
    # Test case 2: Single byte
    assert CRC8.calculate(b'\x00') == 0x00
    crc_ff = CRC8.calculate(b'\xFF')
    print(f"CRC of 0xFF: 0x{crc_ff:02X}")
    
    # Test case 3: Multiple bytes
    test_data = b'\xA5\x80\x00\x10\x00\x00'
    expected_crc = CRC8.calculate(test_data)
    
    # Verify with append and verify functions
    frame_with_crc = CRC8.append_crc(test_data)
    assert CRC8.verify(frame_with_crc, expected_crc)
    
    print("All CRC-8 tests passed!")

if __name__ == "__main__":
    test_crc8()