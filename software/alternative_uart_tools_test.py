#!/usr/bin/env python3
"""
Alternative UART Tool Testing Guide
Phase 5: Physical Layer Investigation

This script provides guidance and automation for testing UART communication
using alternative tools (Tera Term, PuTTY, CoolTerm, etc.) to isolate
whether the 0x20→0x48 conversion is Python-specific or hardware-wide.
"""

import os
import sys
import time
import subprocess
from datetime import datetime

class AlternativeUartTester:
    """Test framework for alternative UART tools"""
    
    def __init__(self):
        self.test_results = {}
        self.fpga_port = "COM3"
        self.baud_rate = 115200
        
        # Common alternative UART tools
        self.uart_tools = {
            'tera_term': {
                'name': 'Tera Term',
                'executable': 'ttermpro.exe',
                'install_url': 'https://ttssh2.osdn.jp/index.html.en',
                'test_method': 'manual'
            },
            'putty': {
                'name': 'PuTTY',
                'executable': 'putty.exe',
                'install_url': 'https://www.putty.org/',
                'test_method': 'manual'
            },
            'coolterm': {
                'name': 'CoolTerm',
                'executable': 'CoolTerm.exe',
                'install_url': 'https://freeware.the-meiers.org/',
                'test_method': 'manual'
            },
            'realterm': {
                'name': 'RealTerm',
                'executable': 'realterm.exe',
                'install_url': 'https://realterm.sourceforge.io/',
                'test_method': 'manual'
            },
            'hercules': {
                'name': 'Hercules SETUP utility',
                'executable': 'Hercules_3-2-8.exe',
                'install_url': 'https://www.hw-group.com/software/hercules-setup-utility',
                'test_method': 'manual'
            }
        }
    
    def check_tool_availability(self):
        """Check which alternative UART tools are available"""
        print("🔍 Checking Alternative UART Tool Availability")
        print("=" * 60)
        
        available_tools = []
        
        for tool_id, tool_info in self.uart_tools.items():
            executable = tool_info['executable']
            
            # Check if executable exists in PATH
            found = False
            try:
                result = subprocess.run(['where', executable], 
                                      capture_output=True, 
                                      text=True, 
                                      shell=True)
                if result.returncode == 0:
                    found = True
                    path = result.stdout.strip().split('\n')[0]
                    print(f"✅ {tool_info['name']}: Found at {path}")
                    available_tools.append(tool_id)
                else:
                    print(f"❌ {tool_info['name']}: Not found")
                    print(f"   Download from: {tool_info['install_url']}")
            except Exception as e:
                print(f"❌ {tool_info['name']}: Error checking - {e}")
        
        if not available_tools:
            print(f"\n⚠️  No alternative UART tools found")
            print(f"   Install at least one tool for comparison testing")
        else:
            print(f"\n✅ Found {len(available_tools)} alternative tools")
        
        return available_tools
    
    def generate_test_instructions(self):
        """Generate detailed test instructions for manual testing"""
        print(f"\n📋 Manual Testing Instructions")
        print("=" * 60)
        print(f"Objective: Verify if 0x20→0x48 conversion occurs with non-Python tools")
        
        print(f"\n🔧 UART Connection Settings:")
        print(f"   Port: {self.fpga_port}")
        print(f"   Baud Rate: {self.baud_rate}")
        print(f"   Data Bits: 8")
        print(f"   Parity: None")
        print(f"   Stop Bits: 1")
        print(f"   Flow Control: None")
        
        print(f"\n📡 Test Procedure for Each Tool:")
        print(f"1. Configure UART settings as above")
        print(f"2. Connect to {self.fpga_port}")
        print(f"3. Send test frame (manually or via script)")
        print(f"4. Observe received data")
        print(f"5. Record results")
        
        print(f"\n🎯 Test Frame to Send:")
        test_frame = [0xA5, 0xA0, 0x1C, 0x10, 0x00, 0x00, 0xEE]
        frame_hex = ' '.join(f'{b:02X}' for b in test_frame)
        print(f"   Hex: {frame_hex}")
        print(f"   Purpose: Read VERSION register")
        print(f"   Expected Response: 5A 00 A0 1C 10 00 00 00 01 00 00 XX")
        print(f"   Key Bytes: SOF=5A, CMD_ECHO=A0")
        
        print(f"\n🔍 What to Look For:")
        print(f"   Expected SOF: 0x5A")
        print(f"   If receive:   0xAD → Same pattern as Python")
        print(f"   Expected CMD: 0xA0") 
        print(f"   If receive:   0x48 → Same conversion as Python")
        
        print(f"\n📊 Result Categories:")
        print(f"   A) Same conversion (0x5A→0xAD, 0xA0→0x48) = Hardware issue")
        print(f"   B) Correct values (0x5A, 0xA0) = Python/driver issue")
        print(f"   C) Different pattern = Tool-specific issue")
        print(f"   D) No response = Connection/FPGA issue")
    
    def create_test_files(self):
        """Create test files for tools that support scripting"""
        print(f"\n📁 Creating Test Files")
        print("=" * 30)
        
        # Create directory for test files
        test_dir = "alternative_uart_tests"
        os.makedirs(test_dir, exist_ok=True)
        
        # Test frame for VERSION register read
        test_frame = [0xA5, 0xA0, 0x1C, 0x10, 0x00, 0x00, 0xEE]
        
        # Hercules script file
        hercules_script = f"""
# Hercules SETUP utility script
# Phase 5: Alternative UART Tool Test
# Send: {' '.join(f'{b:02X}' for b in test_frame)}

SEND {' '.join(f'{b:02X}' for b in test_frame)}
WAIT 1000
RECEIVE 12
"""
        
        with open(f"{test_dir}/hercules_test.txt", "w") as f:
            f.write(hercules_script)
        
        # RealTerm capture file setup
        realterm_setup = f"""
RealTerm Configuration for FPGA Test:
1. Port tab: {self.fpga_port}, {self.baud_rate}, 8, N, 1
2. Send tab: Enter hex values: A5 A0 1C 10 00 00 EE
3. Display tab: Set to Hex display
4. Capture tab: Enable capture to file
5. Click Send
6. Observe receive window

Expected response: 5A 00 A0 1C 10 00 00 00 01 00 00 XX
"""
        
        with open(f"{test_dir}/realterm_setup.txt", "w") as f:
            f.write(realterm_setup)
        
        # Generic hex file for copy-paste
        with open(f"{test_dir}/test_frame.hex", "w") as f:
            f.write(' '.join(f'{b:02X}' for b in test_frame))
        
        # Expected response file
        expected_response = "5A 00 A0 1C 10 00 00 00 01 00 00 XX"
        with open(f"{test_dir}/expected_response.hex", "w") as f:
            f.write(expected_response)
        
        print(f"✅ Created test files in {test_dir}/")
        print(f"   - hercules_test.txt (Hercules script)")
        print(f"   - realterm_setup.txt (RealTerm instructions)")
        print(f"   - test_frame.hex (Frame to send)")
        print(f"   - expected_response.hex (Expected response)")
    
    def automated_comparison_test(self):
        """Run automated comparison using pyserial as reference"""
        print(f"\n🤖 Automated Python Serial Test (Reference)")
        print("=" * 50)
        
        try:
            import serial
            
            with serial.Serial(self.fpga_port, self.baud_rate, timeout=2) as ser:
                print(f"✅ Connected to {self.fpga_port}")
                
                # Test frame: Read VERSION register
                test_frame = bytes([0xA5, 0xA0, 0x1C, 0x10, 0x00, 0x00, 0xEE])
                
                print(f"📤 Sending: {' '.join(f'{b:02X}' for b in test_frame)}")
                ser.write(test_frame)
                ser.flush()
                
                time.sleep(0.5)
                
                response = ser.read(20)
                if response:
                    response_hex = ' '.join(f'{b:02X}' for b in response)
                    print(f"📥 Received: {response_hex}")
                    
                    # Analyze key bytes
                    if len(response) >= 3:
                        sof = response[0]
                        status = response[1] 
                        cmd_echo = response[2]
                        
                        print(f"\n🔍 Analysis:")
                        print(f"   SOF: 0x{sof:02X} (expected: 0x5A)")
                        print(f"   STATUS: 0x{status:02X}")
                        print(f"   CMD_ECHO: 0x{cmd_echo:02X} (expected: 0xA0)")
                        
                        # Store results for comparison
                        self.test_results['python_pyserial'] = {
                            'sof': sof,
                            'cmd_echo': cmd_echo,
                            'full_response': response_hex
                        }
                        
                        return True
                else:
                    print(f"❌ No response received")
                    return False
                    
        except ImportError:
            print(f"❌ pyserial not available")
            return False
        except Exception as e:
            print(f"❌ Error: {e}")
            return False
    
    def generate_comparison_report(self):
        """Generate comparison report template"""
        print(f"\n📊 Test Results Comparison Template")
        print("=" * 60)
        
        report_template = f"""
# Alternative UART Tool Test Results
Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
Phase 5: Physical Layer Investigation

## Test Configuration
- FPGA Port: {self.fpga_port}
- Baud Rate: {self.baud_rate}
- Test Frame: A5 A0 1C 10 00 00 EE
- Expected Response: 5A 00 A0 1C 10 00 00 00 01 00 00 XX

## Results Summary

| Tool | SOF Received | CMD_ECHO Received | Status | Notes |
|------|-------------|------------------|---------|-------|
| Python (pyserial) | ? | ? | ? | Reference |
| Tera Term | ? | ? | ? | Manual test |
| PuTTY | ? | ? | ? | Manual test |
| CoolTerm | ? | ? | ? | Manual test |
| RealTerm | ? | ? | ? | Manual test |
| Hercules | ? | ? | ? | Script test |

## Analysis
- [ ] All tools show same conversion (Hardware issue)
- [ ] Python only shows conversion (Software issue)  
- [ ] Mixed results (Tool-specific issues)
- [ ] No tools work (FPGA/Connection issue)

## Conclusion
TBD - Fill in after completing tests

## Next Steps
TBD - Based on results
"""
        
        with open("alternative_uart_test_report.md", "w") as f:
            f.write(report_template)
        
        print(f"✅ Created report template: alternative_uart_test_report.md")
        print(f"   Fill in results as you test each tool")
    
    def run_alternative_tool_tests(self):
        """Main test execution"""
        print("🔬 Alternative UART Tool Testing")
        print("=" * 60)
        print(f"Phase 5: Physical Layer Investigation")
        print(f"Objective: Isolate Python vs Hardware issues")
        
        # Check available tools
        available_tools = self.check_tool_availability()
        
        # Generate instructions and files
        self.generate_test_instructions()
        self.create_test_files()
        
        # Run automated reference test
        print(f"\n🤖 Running Python Reference Test...")
        self.automated_comparison_test()
        
        # Generate comparison report
        self.generate_comparison_report()
        
        print(f"\n📋 Next Steps:")
        print(f"1. Open each available UART tool")
        print(f"2. Configure connection settings")
        print(f"3. Send test frame and record response")
        print(f"4. Fill in comparison report")
        print(f"5. Analyze results for patterns")
        
        return len(available_tools) > 0

def main():
    """Main execution"""
    print("🎯 Alternative UART Tool Testing Suite")
    print("Phase 5: Physical Layer Investigation")
    print("=" * 60)
    
    tester = AlternativeUartTester()
    
    print(f"\n📋 Prerequisites:")
    print(f"✅ FPGA programmed and responsive")
    print(f"✅ Python test shows 0x20→0x48 conversion")
    print(f"✅ Alternative UART tools installed")
    
    proceed = input(f"\nProceed with alternative tool testing? (y/n): ")
    if proceed.lower() == 'y':
        success = tester.run_alternative_tool_tests()
        if success:
            print(f"\n🎉 Test setup completed")
            print(f"📊 Perform manual tests and fill in report")
        else:
            print(f"\n⚠️  No alternative tools available")
            print(f"   Install tools and re-run")
    else:
        print(f"Test cancelled")

if __name__ == "__main__":
    main()