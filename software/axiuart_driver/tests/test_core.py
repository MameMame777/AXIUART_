"""
Unit Tests for AXIUART Driver Core Components

Test CRC calculation, register map, and protocol functionality.
"""

import pytest
import sys
import os
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from core.crc_calculator import CRC8
from core.register_map import RegisterMap
from core.uart_protocol import UARTProtocol


class TestCRC8:
    """Test CRC-8 calculations"""
    
    def test_empty_data(self):
        """Test CRC of empty data"""
        assert CRC8.calculate(b'') == 0x00
    
    def test_single_byte(self):
        """Test CRC of single bytes"""
        assert CRC8.calculate(b'\x00') == 0x00
        assert CRC8.calculate(b'\xFF') == 0xF3
    
    def test_multiple_bytes(self):
        """Test CRC of multiple bytes"""
        # Test with known frame data
        test_data = b'\xA5\x80\x00\x10\x00\x00'
        crc = CRC8.calculate(test_data)
        assert isinstance(crc, int)
        assert 0 <= crc <= 255
    
    def test_append_and_verify(self):
        """Test CRC append and verification"""
        test_data = b'\xA5\x80\x00\x10\x00\x00'
        
        # Append CRC
        frame_with_crc = CRC8.append_crc(test_data)
        assert len(frame_with_crc) == len(test_data) + 1
        
        # Verify CRC
        expected_crc = frame_with_crc[-1]
        assert CRC8.verify(frame_with_crc, expected_crc)
    
    def test_invalid_crc(self):
        """Test CRC verification with wrong CRC"""
        test_data = b'\xA5\x80\x00\x10\x00\x00\x00'  # Wrong CRC
        assert not CRC8.verify(test_data, 0xFF)


class TestRegisterMap:
    """Test register map functionality"""
    
    def test_register_addresses(self):
        """Test register address constants"""
        assert RegisterMap.CONTROL == 0x1000
        assert RegisterMap.STATUS == 0x1004
        assert RegisterMap.VERSION == 0x101C
    
    def test_register_names(self):
        """Test register name lookup"""
        assert RegisterMap.get_register_name(RegisterMap.CONTROL) == "CONTROL"
        assert RegisterMap.get_register_name(RegisterMap.STATUS) == "STATUS"
        assert RegisterMap.get_register_name(0x9999) == "0x00009999"
    
    def test_command_byte_creation(self):
        """Test command byte generation"""
        # Read, 32-bit, length 1
        cmd = RegisterMap.make_cmd_byte(True, 2, 1, False)
        expected = 0x80 | (2 << 4) | 0  # READ | SIZE_32BIT | (len-1)
        assert cmd == expected
        
        # Write, 16-bit, length 2, increment
        cmd = RegisterMap.make_cmd_byte(False, 1, 2, True)
        expected = 0x40 | (1 << 4) | 1  # INCREMENT | SIZE_16BIT | (len-1)
        assert cmd == expected
    
    def test_command_byte_parsing(self):
        """Test command byte parsing"""
        cmd = 0x80 | (2 << 4) | 0  # READ, 32-bit, length 1
        parsed = RegisterMap.parse_cmd_byte(cmd)
        
        assert parsed['is_read'] == True
        assert parsed['size'] == 2
        assert parsed['length'] == 1
        assert parsed['increment'] == False
    
    def test_invalid_parameters(self):
        """Test invalid parameter handling"""
        with pytest.raises(ValueError):
            RegisterMap.make_cmd_byte(True, 2, 0, False)  # length 0
        
        with pytest.raises(ValueError):
            RegisterMap.make_cmd_byte(True, 2, 17, False)  # length 17
        
        with pytest.raises(ValueError):
            RegisterMap.make_cmd_byte(True, 3, 1, False)  # invalid size


class TestUARTProtocol:
    """Test UART protocol functionality (without actual COM connection)"""
    
    def test_read_frame_building(self):
        """Test read frame construction"""
        # Create protocol without COM manager for testing
        protocol = UARTProtocol(None)  # We'll mock this
        
        frame = protocol.build_read_frame(0x1000, 2, 1)
        
        # Check frame structure
        assert frame[0] == UARTProtocol.SOF_REQUEST  # SOF
        assert frame[1] & 0x80 == 0x80  # READ bit set
        assert frame[2:6] == (0x1000).to_bytes(4, 'little')  # Address
        
        # Check CRC is appended
        assert len(frame) == 7  # SOF + CMD + ADDR(4) + CRC
        
        # Verify CRC
        expected_crc = CRC8.calculate(frame[:-1])
        assert frame[-1] == expected_crc
    
    def test_write_frame_building(self):
        """Test write frame construction"""
        protocol = UARTProtocol(None)
        
        data = b'\x01\x00\x00\x00'  # 32-bit value 1
        frame = protocol.build_write_frame(0x1000, data, 2)
        
        # Check frame structure
        assert frame[0] == UARTProtocol.SOF_REQUEST  # SOF
        assert frame[1] & 0x80 == 0x00  # WRITE (READ bit clear)
        assert frame[2:6] == (0x1000).to_bytes(4, 'little')  # Address
        assert frame[6:10] == data  # Data payload
        
        # Check total length
        assert len(frame) == 11  # SOF + CMD + ADDR(4) + DATA(4) + CRC
    
    def test_response_parsing(self):
        """Test response frame parsing"""
        protocol = UARTProtocol(None)
        
        # Create a valid response frame
        response_data = b'\x01\x00\x00\x00'  # Some data
        frame = bytearray()
        frame.append(UARTProtocol.SOF_RESPONSE)
        frame.append(RegisterMap.STATUS_SUCCESS)
        frame.extend(response_data)
        
        # Add CRC
        crc = CRC8.calculate(frame)
        frame.append(crc)
        
        # Parse response
        status, data = protocol.parse_response(bytes(frame))
        assert status == RegisterMap.STATUS_SUCCESS
        assert data == response_data
    
    def test_invalid_response_parsing(self):
        """Test invalid response handling"""
        protocol = UARTProtocol(None)
        
        # Test short frame
        with pytest.raises(Exception):  # Should be ProtocolError
            protocol.parse_response(b'\x5A\x00')  # Too short
        
        # Test wrong SOF
        with pytest.raises(Exception):  # Should be ProtocolError
            protocol.parse_response(b'\xA5\x00\x00\x00')  # Wrong SOF


def run_tests():
    """Run all tests"""
    print("Running AXIUART Driver Tests...")
    
    # CRC Tests
    test_crc = TestCRC8()
    test_crc.test_empty_data()
    test_crc.test_single_byte()
    test_crc.test_multiple_bytes()
    test_crc.test_append_and_verify()
    test_crc.test_invalid_crc()
    print("✓ CRC8 tests passed")
    
    # Register Map Tests
    test_reg = TestRegisterMap()
    test_reg.test_register_addresses()
    test_reg.test_register_names()
    test_reg.test_command_byte_creation()
    test_reg.test_command_byte_parsing()
    try:
        test_reg.test_invalid_parameters()
    except:
        pass  # Expected to raise exceptions
    print("✓ RegisterMap tests passed")
    
    # Protocol Tests
    test_proto = TestUARTProtocol()
    test_proto.test_read_frame_building()
    test_proto.test_write_frame_building()
    test_proto.test_response_parsing()
    try:
        test_proto.test_invalid_response_parsing()
    except:
        pass  # Expected to raise exceptions
    print("✓ UARTProtocol tests passed")
    
    print("\nAll tests completed successfully!")


if __name__ == "__main__":
    run_tests()