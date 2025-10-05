#!/usr/bin/env python3
"""
Debug Test Register Access Script
Enhanced debugging for test register access issues
"""

import serial
import time
import struct

class DebugTestRegisterAccess:
    """Debug version with detailed logging"""
    
    def __init__(self, port: str = "COM3", baudrate: int = 115200):
        self.port = port
        self.baudrate = baudrate
        self.serial = None
        
        # Test register addresses
        self.REG_TEST_0 = 0x00001020
        
        # Protocol constants
        self.SOF_HOST_TO_DEVICE = 0xA5
        self.CMD_READ = 0xA0
        
    def connect(self) -> bool:
        """Connect to UART"""
        try:
            self.serial = serial.Serial(
                port=self.port,
                baudrate=self.baudrate,
                bytesize=8,
                parity='N',
                stopbits=1,
                timeout=2.0
            )
            time.sleep(0.1)
            print(f"✅ Connected to {self.port}")
            return True
        except Exception as e:
            print(f"❌ Connection failed: {e}")
            return False
    
    def disconnect(self):
        """Disconnect from UART"""
        if self.serial and self.serial.is_open:
            self.serial.close()
            print("🔌 Disconnected")
    
    def crc8_calculate(self, data: bytes) -> int:
        """Calculate CRC8 using polynomial 0x07"""
        crc = 0x00
        for byte in data:
            crc ^= byte
            for _ in range(8):
                if crc & 0x80:
                    crc = (crc << 1) ^ 0x07
                else:
                    crc = crc << 1
                crc &= 0xFF
        return crc
    
    def debug_read_register(self, addr: int):
        """Debug version of register read with detailed logging"""
        print(f"\n🔍 Debug: Reading register 0x{addr:08X}")
        
        if not self.serial or not self.serial.is_open:
            print("❌ UART not connected")
            return
        
        try:
            # Clear buffers
            self.serial.reset_input_buffer()
            self.serial.reset_output_buffer()
            
            # Build read command frame - check UVM format
            # UVM format: SOF + CMD + ADDR_LOW + ADDR_HIGH + SIZE + LENGTH + CRC
            frame_data = struct.pack('<BBBBBB', 
                                   self.SOF_HOST_TO_DEVICE,  # 0xA5
                                   self.CMD_READ,            # 0xA0  
                                   addr & 0xFF,              # ADDR[7:0]
                                   (addr >> 8) & 0xFF,       # ADDR[15:8]  
                                   (addr >> 16) & 0xFF,      # ADDR[23:16]
                                   (addr >> 24) & 0xFF)      # ADDR[31:24]
            
            # Calculate CRC (excluding SOF)
            crc = self.crc8_calculate(frame_data[1:])
            frame = frame_data + bytes([crc])
            
            print(f"📤 Sending frame: {' '.join(f'0x{b:02X}' for b in frame)}")
            print(f"   SOF: 0x{frame[0]:02X}")
            print(f"   CMD: 0x{frame[1]:02X}")
            print(f"   ADDR: 0x{frame[5]:02X}{frame[4]:02X}{frame[3]:02X}{frame[2]:02X}")
            crc_data = frame_data[1:]
            print(f"   CRC: 0x{frame[6]:02X} (calculated from {' '.join(f'0x{b:02X}' for b in crc_data)})")
            
            # Send command
            self.serial.write(frame)
            self.serial.flush()
            
            # Wait and read response
            time.sleep(0.1)
            response = self.serial.read(32)
            
            print(f"📥 Received {len(response)} bytes: {' '.join(f'0x{b:02X}' for b in response)}")
            
            if len(response) == 0:
                print("❌ No response received")
                return
            
            # Parse response
            if len(response) >= 1:
                print(f"   SOF: 0x{response[0]:02X}")
            if len(response) >= 2:
                print(f"   STATUS: 0x{response[1]:02X}")
                if response[1] == 0x00:
                    print("     ✅ STATUS OK")
                elif response[1] == 0x40:
                    print("     ❌ STATUS 0x40 - Unknown error")
                else:
                    print(f"     ❌ Unknown status: 0x{response[1]:02X}")
            if len(response) >= 3:
                print(f"   CMD_ECHO: 0x{response[2]:02X}")
            if len(response) >= 7:
                data = struct.unpack('<L', response[3:7])[0]
                print(f"   DATA: 0x{data:08X}")
            if len(response) >= 8:
                print(f"   CRC: 0x{response[7]:02X}")
                
                # Verify CRC
                if len(response) >= 8:
                    calc_crc = self.crc8_calculate(response[1:7])
                    print(f"   CRC_CALC: 0x{calc_crc:02X}")
                    if response[7] == calc_crc:
                        print("   ✅ CRC OK")
                    else:
                        print("   ❌ CRC Mismatch")
            
        except Exception as e:
            print(f"❌ Error: {e}")

def main():
    """Main debug execution"""
    print("🔍 Debug Test Register Access")
    print("=" * 50)
    
    debug = DebugTestRegisterAccess()
    
    if debug.connect():
        try:
            # Test reading from TEST_REG_0
            debug.debug_read_register(0x00001020)
            
            # Also try a known working register for comparison
            print(f"\n🔍 Comparison: Reading known register 0x00001000")
            debug.debug_read_register(0x00001000)
            
        finally:
            debug.disconnect()
    
    print("\n🔍 Debug session completed")

if __name__ == "__main__":
    main()