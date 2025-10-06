#!/usr/bin/env python3
"""
Dynamic UART Baud Rate Changer via AXI Registers
==============================================
Change FPGA UART baud rate at runtime without reprogramming
"""

import serial
import time

def crc8_calculate(data):
    """Calculate CRC8 with polynomial 0x07"""
    crc = 0x00
    for byte in data:
        crc ^= byte
        for _ in range(8):
            if crc & 0x80:
                crc = ((crc << 1) ^ 0x07) & 0xFF
            else:
                crc = (crc << 1) & 0xFF
    return crc

def format_hex_bytes(data):
    """Format bytes for display"""
    return ' '.join(f'{b:02X}' for b in data)

def send_axi_write(ser, addr, data):
    """Send AXI write command via UART protocol"""
    cmd = 0x20  # Write, no increment, 32-bit, 1 beat
    
    # Construct frame
    frame = bytearray()
    frame.append(0xA5)  # SOF (host→device)
    frame.append(cmd)   # CMD
    # Address (little-endian)
    frame.extend([(addr >>  0) & 0xFF,
                 (addr >>  8) & 0xFF,
                 (addr >> 16) & 0xFF,
                 (addr >> 24) & 0xFF])
    # Data (little-endian)
    frame.extend([(data >>  0) & 0xFF,
                 (data >>  8) & 0xFF,
                 (data >> 16) & 0xFF,
                 (data >> 24) & 0xFF])
    
    # Calculate CRC over CMD through DATA
    crc = crc8_calculate(frame[1:])
    frame.append(crc)
    
    print(f"📤 Writing 0x{data:08X} to 0x{addr:08X}")
    print(f"   Frame: {format_hex_bytes(frame)}")
    
    ser.write(frame)
    time.sleep(0.1)
    
    response = ser.read(10)
    print(f"📥 Response: {format_hex_bytes(response)}")
    return len(response) > 0

def change_baud_rate_register(current_baud, target_baud):
    """Change UART baud rate via register write"""
    print(f"\n🔄 Dynamic Baud Rate Change: {current_baud} → {target_baud}")
    print("=" * 60)
    
    # Common baud rate divisor values (from UVM sequences)
    baud_configs = {
        115200: 0x0000043d,  # 115200 baud divisor
        57600:  0x000008ac,  # 57600 baud divisor  
        19200:  0x00001a0a,  # 19200 baud divisor
        9600:   0x000032dc   # 9600 baud divisor
    }
    
    if target_baud not in baud_configs:
        print(f"❌ Unsupported baud rate: {target_baud}")
        return False
    
    try:
        # Connect at current baud rate
        ser = serial.Serial('COM3', current_baud, timeout=2)
        time.sleep(0.5)
        print(f"✅ Connected at {current_baud} baud")
        
        # Hypothetical UART control register addresses (need to verify)
        UART_BAUD_REG = 0x00001010  # UART baud rate divisor register
        UART_CTRL_REG = 0x00001000  # UART control register
        
        # Step 1: Disable UART
        print("📝 Step 1: Disable UART for configuration")
        if not send_axi_write(ser, UART_CTRL_REG, 0x00000000):
            print("❌ Failed to disable UART")
            ser.close()
            return False
        
        time.sleep(0.1)
        
        # Step 2: Write new baud rate divisor
        divisor = baud_configs[target_baud]
        print(f"📝 Step 2: Set baud divisor to 0x{divisor:08X}")
        if not send_axi_write(ser, UART_BAUD_REG, divisor):
            print("❌ Failed to write baud rate")
            ser.close()
            return False
        
        time.sleep(0.1)
        
        # Step 3: Re-enable UART
        print("📝 Step 3: Re-enable UART with new baud rate")
        if not send_axi_write(ser, UART_CTRL_REG, 0x00000007):
            print("❌ Failed to re-enable UART")
            ser.close()
            return False
        
        ser.close()
        
        # Step 4: Test communication at new baud rate
        print(f"📝 Step 4: Test communication at {target_baud} baud")
        time.sleep(1)  # Allow time for baud rate change
        
        ser_new = serial.Serial('COM3', target_baud, timeout=2)
        time.sleep(0.5)
        
        # Send test command at new baud rate
        test_addr = 0x00001020
        test_data = 0x12345678
        success = send_axi_write(ser_new, test_addr, test_data)
        
        ser_new.close()
        
        if success:
            print(f"🎉 Successfully changed to {target_baud} baud!")
            return True
        else:
            print(f"❌ Communication failed at {target_baud} baud")
            return False
            
    except Exception as e:
        print(f"❌ Error during baud rate change: {e}")
        return False

def test_baud_rate_sequence():
    """Test sequence of different baud rates"""
    print("🎯 Dynamic Baud Rate Testing Sequence")
    print("=" * 50)
    
    # Test sequence: 115200 → 57600 → 19200 → 9600 → back to 115200
    baud_sequence = [
        (115200, 57600),
        (57600, 19200), 
        (19200, 9600),
        (9600, 115200)  # Return to original
    ]
    
    for current, target in baud_sequence:
        success = change_baud_rate_register(current, target)
        if not success:
            print(f"❌ Failed at {current} → {target}, stopping sequence")
            break
        time.sleep(2)  # Pause between changes
    
    print(f"\n🎉 Baud rate sequence testing completed")

def main():
    print("🔄 Dynamic UART Baud Rate Changer")
    print("=" * 50)
    print("Changes FPGA UART baud rate via AXI register writes")
    
    print("\n📋 Options:")
    print("1. Change 115200 → 9600 baud")
    print("2. Change 115200 → 19200 baud")
    print("3. Change 115200 → 57600 baud")
    print("4. Run full baud rate sequence test")
    print("5. Return to 115200 baud (from any rate)")
    
    choice = input("\nSelect option (1-5): ")
    
    if choice == "1":
        change_baud_rate_register(115200, 9600)
    elif choice == "2":
        change_baud_rate_register(115200, 19200)
    elif choice == "3":
        change_baud_rate_register(115200, 57600)
    elif choice == "4":
        test_baud_rate_sequence()
    elif choice == "5":
        # Try from common baud rates back to 115200
        for baud in [9600, 19200, 57600]:
            try:
                if change_baud_rate_register(baud, 115200):
                    print(f"✅ Successfully returned to 115200 from {baud}")
                    break
            except:
                continue
    
    print(f"\n⚠️  Note: This requires UART control registers to be implemented in FPGA")
    print(f"If this doesn't work, use the RTL modification approach instead")

if __name__ == "__main__":
    main()