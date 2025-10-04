"""
Register Map Definitions for AXIUART System

Defines all register addresses, bit fields, and constants for the AXIUART register block.
Based on register_map.md specification.
"""

class RegisterMap:
    """AXIUART Register Map Constants"""
    
    # Base address for register block
    BASE_ADDR = 0x1000
    
    # Register addresses (32-bit aligned)
    CONTROL = BASE_ADDR + 0x000     # Global control register
    STATUS = BASE_ADDR + 0x004      # Global status and error flags
    CONFIG = BASE_ADDR + 0x008      # UART and AXI configuration
    DEBUG = BASE_ADDR + 0x00C       # Debug mode and control
    TX_COUNT = BASE_ADDR + 0x010    # TX transaction counter
    RX_COUNT = BASE_ADDR + 0x014    # RX transaction counter
    FIFO_STAT = BASE_ADDR + 0x018   # FIFO status and flags
    VERSION = BASE_ADDR + 0x01C     # Hardware version information
    
    # CONTROL register bit fields
    CONTROL_BRIDGE_ENABLE = 0x01    # bit[0]: Enable UART bridge
    CONTROL_RESET_STATS = 0x02      # bit[1]: Reset statistics counters (W1C)
    
    # STATUS register bit fields (example)
    STATUS_BRIDGE_READY = 0x01      # bit[0]: Bridge ready
    STATUS_TX_BUSY = 0x02           # bit[1]: TX busy
    STATUS_RX_ERROR = 0x04          # bit[2]: RX error
    STATUS_CRC_ERROR = 0x08         # bit[3]: CRC error
    
    # Protocol status codes (returned in UART response frames)
    STATUS_SUCCESS = 0x00           # Success
    STATUS_CRC_ERR = 0x01          # CRC error
    STATUS_TIMEOUT = 0x02          # Timeout
    STATUS_INVALID_CMD = 0x03      # Invalid command
    STATUS_AXI_ERROR = 0x04        # AXI4-Lite error
    STATUS_BUSY = 0x80             # System busy
    
    # Data access sizes
    SIZE_8BIT = 0b00
    SIZE_16BIT = 0b01
    SIZE_32BIT = 0b10
    SIZE_RESERVED = 0b11
    
    # Command bit fields
    CMD_READ = 0x80                # bit[7]: 1=read, 0=write
    CMD_INCREMENT = 0x40           # bit[6]: Address auto-increment
    CMD_SIZE_MASK = 0x30           # bit[5:4]: Data size
    CMD_SIZE_SHIFT = 4
    CMD_LEN_MASK = 0x0F            # bit[3:0]: Transfer length-1
    
    @staticmethod
    def get_register_name(addr: int) -> str:
        """
        Get register name from address
        
        Args:
            addr: Register address
            
        Returns:
            Register name string
        """
        register_names = {
            RegisterMap.CONTROL: "CONTROL",
            RegisterMap.STATUS: "STATUS", 
            RegisterMap.CONFIG: "CONFIG",
            RegisterMap.DEBUG: "DEBUG",
            RegisterMap.TX_COUNT: "TX_COUNT",
            RegisterMap.RX_COUNT: "RX_COUNT",
            RegisterMap.FIFO_STAT: "FIFO_STAT",
            RegisterMap.VERSION: "VERSION"
        }
        return register_names.get(addr, f"0x{addr:08X}")
    
    @staticmethod
    def get_all_registers() -> dict:
        """
        Get all register addresses and names
        
        Returns:
            Dictionary of {address: name}
        """
        return {
            RegisterMap.CONTROL: "CONTROL",
            RegisterMap.STATUS: "STATUS",
            RegisterMap.CONFIG: "CONFIG", 
            RegisterMap.DEBUG: "DEBUG",
            RegisterMap.TX_COUNT: "TX_COUNT",
            RegisterMap.RX_COUNT: "RX_COUNT",
            RegisterMap.FIFO_STAT: "FIFO_STAT",
            RegisterMap.VERSION: "VERSION"
        }
    
    @staticmethod
    def is_valid_register(addr: int) -> bool:
        """
        Check if address is a valid register
        
        Args:
            addr: Address to check
            
        Returns:
            True if valid register address
        """
        return addr in RegisterMap.get_all_registers().keys()
    
    @staticmethod
    def make_cmd_byte(is_read: bool, size: int, length: int, increment: bool = False) -> int:
        """
        Create command byte for UART protocol
        
        Args:
            is_read: True for read, False for write
            size: Data size (0=8bit, 1=16bit, 2=32bit)
            length: Transfer length (1-16)
            increment: Address auto-increment
            
        Returns:
            Command byte value
        """
        if not (1 <= length <= 16):
            raise ValueError("Length must be 1-16")
        if size not in [0, 1, 2]:
            raise ValueError("Size must be 0, 1, or 2")
            
        cmd = 0
        if is_read:
            cmd |= RegisterMap.CMD_READ
        if increment:
            cmd |= RegisterMap.CMD_INCREMENT
        cmd |= (size << RegisterMap.CMD_SIZE_SHIFT) & RegisterMap.CMD_SIZE_MASK
        cmd |= (length - 1) & RegisterMap.CMD_LEN_MASK
        
        return cmd
    
    @staticmethod
    def parse_cmd_byte(cmd: int) -> dict:
        """
        Parse command byte
        
        Args:
            cmd: Command byte value
            
        Returns:
            Dictionary with parsed fields
        """
        return {
            'is_read': bool(cmd & RegisterMap.CMD_READ),
            'increment': bool(cmd & RegisterMap.CMD_INCREMENT),
            'size': (cmd & RegisterMap.CMD_SIZE_MASK) >> RegisterMap.CMD_SIZE_SHIFT,
            'length': (cmd & RegisterMap.CMD_LEN_MASK) + 1
        }

def test_register_map():
    """Test register map functionality"""
    
    # Test register name lookup
    assert RegisterMap.get_register_name(RegisterMap.CONTROL) == "CONTROL"
    assert RegisterMap.get_register_name(0x9999) == "0x00009999"
    
    # Test command byte creation
    cmd = RegisterMap.make_cmd_byte(True, 2, 1, False)  # Read, 32-bit, length 1
    expected = 0x80 | (2 << 4) | 0  # READ | SIZE_32BIT | (len-1)
    assert cmd == expected
    
    # Test command byte parsing
    parsed = RegisterMap.parse_cmd_byte(cmd)
    assert parsed['is_read'] == True
    assert parsed['size'] == 2
    assert parsed['length'] == 1
    assert parsed['increment'] == False
    
    print("All register map tests passed!")

if __name__ == "__main__":
    test_register_map()