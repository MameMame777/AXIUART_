#!/usr/bin/env python3
"""
ILA Trigger Failure Analysis Tool
Analyze why reg_test_write_trigger = 1 doesn't work
"""

import serial
import time
import struct

class TriggerAnalyzer:
    def __init__(self, port='COM3', baudrate=115200):
        self.port = port
        self.baudrate = baudrate
        self.serial = None
        
    def connect(self):
        """Connect to serial port"""
        try:
            self.serial = serial.Serial(self.port, self.baudrate, timeout=2)
            time.sleep(0.1)
            print(f"✅ Connected to {self.port}")
            return True
        except Exception as e:
            print(f"❌ Connection failed: {e}")
            return False

    def disconnect(self):
        if self.serial and self.serial.is_open:
            self.serial.close()
            print("🔌 Disconnected")

    def analyze_write_sequence(self, address, data):
        """Analyze a single write sequence timing"""
        print(f"\n🔍 Analyzing write sequence to 0x{address:08X} with data 0x{data:08X}")
        print("=" * 70)
        
        # UART protocol analysis
        cmd_bytes = [0xA5, 0x20]  # SOF + WRITE_CMD
        addr_bytes = [(address >> (8*i)) & 0xFF for i in range(4)]
        data_bytes = [(data >> (8*i)) & 0xFF for i in range(4)]
        
        print("📡 UART Command Breakdown:")
        print(f"   SOF: 0x{cmd_bytes[0]:02X}")
        print(f"   CMD: 0x{cmd_bytes[1]:02X} (WRITE)")
        print(f"   ADDR: {' '.join(f'0x{b:02X}' for b in addr_bytes)} = 0x{address:08X}")
        print(f"   DATA: {' '.join(f'0x{b:02X}' for b in data_bytes)} = 0x{data:08X}")
        
        # Calculate expected CRC
        all_bytes = cmd_bytes + addr_bytes + data_bytes
        crc = self.calculate_crc8(all_bytes[1:])  # Exclude SOF from CRC
        print(f"   CRC: 0x{crc:02X}")
        
        # Full packet
        packet = all_bytes + [crc]
        print(f"📦 Full packet: {' '.join(f'{b:02X}' for b in packet)}")
        
        return packet

    def calculate_crc8(self, data):
        """Calculate CRC8 for UART protocol"""
        crc = 0xFF
        for byte in data:
            crc ^= byte
            for _ in range(8):
                if crc & 0x80:
                    crc = (crc << 1) ^ 0x07
                else:
                    crc <<= 1
                crc &= 0xFF
        return crc

    def timing_analysis(self):
        """Analyze timing requirements for ILA trigger"""
        print("\n⏱️  ILA TIMING ANALYSIS")
        print("=" * 70)
        
        print("🎯 Expected Signal Sequence for reg_test_write_trigger = 1:")
        print("   1. UART receives write command")
        print("   2. AXI4-Lite transaction starts:")
        print("      - axi.awvalid = 1")
        print("      - axi.awaddr = 0x00001020-0x0000102C")
        print("      - aw_handshake = 1 (awvalid && awready)")
        print("      - axi_state = WRITE_DATA")
        print("      - axi.wvalid = 1")
        print("      - axi.wdata = written data")
        print("      - w_handshake = 1 (wvalid && wready)")
        print("      - write_enable = 1")
        print("      - write_addr_reg[11:0] = 0x020-0x02C")
        print("      - reg_test_write_trigger = 1")
        
        print("\n🚨 Potential Issues:")
        print("   A. Register_Block.sv NOT instantiated in FPGA")
        print("   B. Different register module responding")
        print("   C. AXI4-Lite signals not reaching Register_Block")
        print("   D. write_enable never asserted")
        print("   E. write_addr_reg has wrong value")
        print("   F. Timing too fast for ILA capture")

    def alternative_trigger_analysis(self):
        """Suggest alternative trigger conditions"""
        print("\n🔧 ALTERNATIVE TRIGGER STRATEGIES")
        print("=" * 70)
        
        print("📊 Priority Order for Existing Signals:")
        print("   1. axi_awvalid_debug = 1 AND axi_awaddr_debug[11:0] = 0x020")
        print("   2. axi_wvalid_debug = 1 AND axi_wdata_debug = 0x55AA55AA")
        print("   3. aw_handshake = 1 AND axi_awaddr_debug[15:4] = 0x102")
        print("   4. w_handshake = 1")
        print("   5. axi_state = WRITE_DATA")
        print("   6. write_enable = 1 (if it ever gets asserted)")
        
        print("\n🎯 Most Reliable Trigger:")
        print("   Trigger: axi_awvalid_debug = 1")
        print("   Condition: AND axi_awaddr_debug = 0x00001020")
        print("   Reason: This catches the address write phase")
        
        print("\n🔍 Diagnostic Triggers:")
        print("   1. axi_awvalid_debug = 1 (any AXI write)")
        print("   2. axi_wvalid_debug = 1 (any data write)")
        print("   3. aw_handshake = 1 (successful address handshake)")

    def run_comprehensive_analysis(self):
        """Run complete trigger failure analysis"""
        print("🔬 ILA TRIGGER FAILURE ANALYSIS")
        print("=" * 80)
        print("Objective: Determine why reg_test_write_trigger = 1 doesn't work")
        print("=" * 80)
        
        # Analyze write sequences for all test registers
        test_data = [
            (0x00001020, 0x55AA55AA),
            (0x00001024, 0xFFFFFFFF),
            (0x00001028, 0x00000000),
            (0x0000102C, 0xCAFEBABE)
        ]
        
        for addr, data in test_data:
            self.analyze_write_sequence(addr, data)
        
        self.timing_analysis()
        self.alternative_trigger_analysis()
        
        print("\n💡 DIAGNOSIS CONCLUSION:")
        print("=" * 70)
        print("🚨 Most Likely Cause: Register_Block.sv NOT active in FPGA")
        print("   - Test pattern generator (0xF02022XX) still responding")
        print("   - write_enable signal never asserts")
        print("   - reg_test_write_trigger remains 0")
        
        print("\n📋 IMMEDIATE ACTION ITEMS:")
        print("   1. Use axi_awvalid_debug = 1 as basic trigger")
        print("   2. Verify axi_awaddr_debug shows 0x00001020-0x0000102C")
        print("   3. Check if write_enable ever goes to 1")
        print("   4. Confirm Register_Block.sv is instantiated")
        
        print("\n🎯 STEP-BY-STEP ILA SETUP:")
        print("   Step 1: Trigger = axi_awvalid_debug = 1")
        print("   Step 2: Check axi_awaddr_debug value")
        print("   Step 3: If address wrong → AXI routing issue")
        print("   Step 4: If address correct → Check write_enable")
        print("   Step 5: If write_enable = 0 → Register_Block not active")

def main():
    print("Starting ILA Trigger Failure Analysis...")
    print("Based on reg_test_write_trigger = 1 not working\n")
    
    analyzer = TriggerAnalyzer()
    
    if analyzer.connect():
        try:
            analyzer.run_comprehensive_analysis()
        finally:
            analyzer.disconnect()
    
    print("\n" + "=" * 80)
    print("📝 ANALYSIS COMPLETE")
    print("Use the alternative trigger strategies above")
    print("=" * 80)

if __name__ == "__main__":
    main()