#!/usr/bin/env python3
"""
UART Configuration & Baud Rate Verification Tool
Phase 5: Physical Layer Investigation

This tool verifies UART configuration parameters and measures
baud rate accuracy to ensure proper communication timing.
"""

import serial
import time
import threading
from datetime import datetime, timedelta

class UartConfigVerifier:
    """UART configuration and timing verification"""
    
    def __init__(self, port="COM3"):
        self.port = port
        self.test_results = {}
        
        # Standard UART configurations to test
        self.baud_rates = [
            9600, 19200, 38400, 57600, 115200, 230400, 460800, 921600
        ]
        
        # UART parameter combinations
        self.uart_configs = [
            {'baud': 115200, 'bytesize': 8, 'parity': 'N', 'stopbits': 1},
            {'baud': 115200, 'bytesize': 7, 'parity': 'N', 'stopbits': 1},
            {'baud': 115200, 'bytesize': 8, 'parity': 'E', 'stopbits': 1},
            {'baud': 115200, 'bytesize': 8, 'parity': 'O', 'stopbits': 1},
            {'baud': 115200, 'bytesize': 8, 'parity': 'N', 'stopbits': 2},
        ]
    
    def verify_port_availability(self):
        """Check if the UART port is available and responsive"""
        print(f"🔌 Verifying Port Availability: {self.port}")
        print("-" * 40)
        
        try:
            # List available ports
            import serial.tools.list_ports
            ports = serial.tools.list_ports.comports()
            
            print(f"📋 Available COM Ports:")
            for port in ports:
                print(f"   {port.device}: {port.description}")
                if port.device == self.port:
                    print(f"   ✅ Target port found: {port.description}")
            
            # Test basic connection
            with serial.Serial(self.port, 115200, timeout=1) as ser:
                print(f"✅ Successfully opened {self.port}")
                print(f"   Default settings: 115200,8,N,1")
                return True
                
        except ImportError:
            print(f"⚠️  serial.tools.list_ports not available")
            return self._basic_connection_test()
        except Exception as e:
            print(f"❌ Port verification failed: {e}")
            return False
    
    def _basic_connection_test(self):
        """Fallback connection test"""
        try:
            with serial.Serial(self.port, 115200, timeout=1) as ser:
                print(f"✅ Basic connection test passed")
                return True
        except Exception as e:
            print(f"❌ Basic connection failed: {e}")
            return False
    
    def test_baud_rate_accuracy(self, target_baud=115200):
        """Test baud rate timing accuracy"""
        print(f"\n⏱️ Baud Rate Accuracy Test: {target_baud}")
        print("-" * 40)
        
        try:
            with serial.Serial(self.port, target_baud, timeout=2) as ser:
                # Test pattern: alternating bits for easy timing measurement
                test_byte = 0x55  # 01010101
                test_count = 100
                
                print(f"📡 Sending {test_count} bytes of 0x{test_byte:02X}")
                print(f"Expected timing: {1/target_baud*8:.2f} μs per bit")
                
                # Clear buffers
                ser.reset_input_buffer()
                ser.reset_output_buffer()
                
                # Measure transmission time
                start_time = time.perf_counter()
                
                for _ in range(test_count):
                    ser.write(bytes([test_byte]))
                
                ser.flush()  # Wait for all data to be transmitted
                end_time = time.perf_counter()
                
                # Calculate actual timing
                total_time = end_time - start_time
                bits_per_byte = 10  # Start + 8 data + Stop
                total_bits = test_count * bits_per_byte
                actual_baud = total_bits / total_time
                error_percent = ((actual_baud - target_baud) / target_baud) * 100
                
                print(f"📊 Timing Results:")
                print(f"   Total time: {total_time*1000:.2f} ms")
                print(f"   Total bits: {total_bits}")
                print(f"   Measured baud: {actual_baud:.0f}")
                print(f"   Error: {error_percent:+.2f}%")
                
                # Store results
                self.test_results[f'baud_{target_baud}'] = {
                    'target': target_baud,
                    'measured': actual_baud,
                    'error_percent': error_percent,
                    'status': 'PASS' if abs(error_percent) < 2.0 else 'FAIL'
                }
                
                if abs(error_percent) < 2.0:
                    print(f"   ✅ PASS (< 2% error)")
                else:
                    print(f"   ❌ FAIL (> 2% error)")
                
                return True
                
        except Exception as e:
            print(f"❌ Baud rate test failed: {e}")
            return False
    
    def test_uart_parameter_combinations(self):
        """Test different UART parameter combinations"""
        print(f"\n🔧 UART Parameter Combination Test")
        print("=" * 50)
        
        for i, config in enumerate(self.uart_configs):
            print(f"\nTest {i+1}: {config['baud']},{config['bytesize']},{config['parity']},{config['stopbits']}")
            print("-" * 30)
            
            try:
                with serial.Serial(
                    port=self.port,
                    baudrate=config['baud'],
                    bytesize=config['bytesize'],
                    parity=config['parity'],
                    stopbits=config['stopbits'],
                    timeout=2
                ) as ser:
                    
                    print(f"✅ Connection established")
                    
                    # Send test frame
                    test_frame = bytes([0xA5, 0xA0, 0x1C, 0x10, 0x00, 0x00, 0xEE])
                    print(f"📤 Sending test frame...")
                    
                    ser.write(test_frame)
                    ser.flush()
                    time.sleep(0.5)
                    
                    # Check for response
                    response = ser.read(20)
                    if response:
                        response_hex = ' '.join(f'{b:02X}' for b in response)
                        print(f"📥 Response: {response_hex}")
                        
                        # Analyze response quality
                        if len(response) >= 3:
                            sof = response[0]
                            status = response[1]
                            print(f"   SOF: 0x{sof:02X}, STATUS: 0x{status:02X}")
                            
                            config_key = f"config_{i+1}"
                            self.test_results[config_key] = {
                                'config': config,
                                'response_length': len(response),
                                'sof': sof,
                                'status': status,
                                'full_response': response_hex,
                                'status': 'RESPONSE' if response else 'NO_RESPONSE'
                            }
                        else:
                            print(f"   ⚠️  Short response: {len(response)} bytes")
                    else:
                        print(f"   ❌ No response")
                        self.test_results[f"config_{i+1}"] = {
                            'config': config,
                            'status': 'NO_RESPONSE'
                        }
                    
            except Exception as e:
                print(f"❌ Configuration failed: {e}")
                self.test_results[f"config_{i+1}"] = {
                    'config': config,
                    'status': 'CONNECTION_FAILED',
                    'error': str(e)
                }
    
    def analyze_fpga_clock_settings(self):
        """Analyze FPGA clock configuration for UART timing"""
        print(f"\n🕰️ FPGA Clock Configuration Analysis")
        print("=" * 50)
        
        print(f"📋 Zybo Z7-20 Clock Specifications:")
        print(f"   Input Clock: 125 MHz (PS_CLK)")
        print(f"   UART Clock Source: Usually derived from PS_CLK")
        print(f"   Expected UART Clock: 100 MHz (typical)")
        
        print(f"\n🧮 Baud Rate Generation Analysis:")
        print(f"   Target Baud Rate: 115200")
        print(f"   Required Clock Division:")
        
        # Common clock frequencies and their divisors
        clock_configs = [
            {'freq': 100_000_000, 'name': '100 MHz'},
            {'freq': 125_000_000, 'name': '125 MHz'},
            {'freq': 50_000_000, 'name': '50 MHz'},
        ]
        
        target_baud = 115200
        
        for config in clock_configs:
            freq = config['freq']
            name = config['name']
            
            # Calculate required divisor
            divisor = freq / (16 * target_baud)  # Common UART divisor formula
            integer_divisor = round(divisor)
            actual_baud = freq / (16 * integer_divisor)
            error_ppm = ((actual_baud - target_baud) / target_baud) * 1_000_000
            
            print(f"\n   {name}:")
            print(f"     Required divisor: {divisor:.2f}")
            print(f"     Integer divisor: {integer_divisor}")
            print(f"     Actual baud: {actual_baud:.0f}")
            print(f"     Error: {error_ppm:+.0f} ppm ({error_ppm/10000:+.2f}%)")
            
            if abs(error_ppm) < 20000:  # < 2% error
                print(f"     ✅ Acceptable accuracy")
            else:
                print(f"     ⚠️  High error")
    
    def uart_stress_test(self, duration=30):
        """Perform sustained UART communication test"""
        print(f"\n💪 UART Stress Test ({duration}s)")
        print("=" * 40)
        
        try:
            with serial.Serial(self.port, 115200, timeout=1) as ser:
                print(f"📡 Starting sustained communication test...")
                
                start_time = time.time()
                bytes_sent = 0
                bytes_received = 0
                errors = 0
                
                test_frame = bytes([0xA5, 0xA0, 0x1C, 0x10, 0x00, 0x00, 0xEE])
                
                while (time.time() - start_time) < duration:
                    try:
                        # Send test frame
                        ser.write(test_frame)
                        bytes_sent += len(test_frame)
                        
                        # Read response
                        time.sleep(0.1)
                        response = ser.read(20)
                        bytes_received += len(response)
                        
                        # Check response validity
                        if response and len(response) >= 3:
                            if response[0] not in [0x5A, 0xAD]:  # Accept known SOF variants
                                errors += 1
                        
                        time.sleep(0.5)  # 2 frames per second
                        
                    except Exception as e:
                        errors += 1
                        print(f"   Error: {e}")
                
                elapsed = time.time() - start_time
                frames_sent = bytes_sent // len(test_frame)
                
                print(f"📊 Stress Test Results:")
                print(f"   Duration: {elapsed:.1f}s")
                print(f"   Frames sent: {frames_sent}")
                print(f"   Bytes sent: {bytes_sent}")
                print(f"   Bytes received: {bytes_received}")
                print(f"   Errors: {errors}")
                print(f"   Error rate: {errors/frames_sent*100:.1f}%")
                
                self.test_results['stress_test'] = {
                    'duration': elapsed,
                    'frames_sent': frames_sent,
                    'bytes_sent': bytes_sent,
                    'bytes_received': bytes_received,
                    'errors': errors,
                    'error_rate': errors/frames_sent*100 if frames_sent > 0 else 0
                }
                
                if errors == 0:
                    print(f"   ✅ Perfect reliability")
                elif errors < frames_sent * 0.01:  # < 1% error
                    print(f"   ✅ Good reliability")
                else:
                    print(f"   ⚠️  Reliability issues detected")
                
                return True
                
        except Exception as e:
            print(f"❌ Stress test failed: {e}")
            return False
    
    def generate_configuration_report(self):
        """Generate comprehensive configuration report"""
        print(f"\n📊 UART Configuration Report")
        print("=" * 60)
        
        report_content = f"""
# UART Configuration Verification Report
Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
Phase 5: Physical Layer Investigation

## Summary
Port: {self.port}
Target Configuration: 115200,8,N,1

## Test Results

### Baud Rate Accuracy
"""
        
        # Add baud rate results
        for key, result in self.test_results.items():
            if key.startswith('baud_'):
                report_content += f"- {result['target']} baud: {result['measured']:.0f} measured ({result['error_percent']:+.2f}% error) - {result['status']}\n"
        
        report_content += "\n### Parameter Combinations\n"
        
        # Add configuration results
        for key, result in self.test_results.items():
            if key.startswith('config_'):
                config = result.get('config', {})
                status = result.get('status', 'UNKNOWN')
                report_content += f"- {config.get('baud', '?')},{config.get('bytesize', '?')},{config.get('parity', '?')},{config.get('stopbits', '?')}: {status}\n"
        
        # Add stress test results
        if 'stress_test' in self.test_results:
            stress = self.test_results['stress_test']
            report_content += f"\n### Stress Test\n"
            report_content += f"- Duration: {stress['duration']:.1f}s\n"
            report_content += f"- Frames: {stress['frames_sent']}\n"
            report_content += f"- Error Rate: {stress['error_rate']:.1f}%\n"
        
        report_content += f"\n## Recommendations\n"
        report_content += f"TBD - Based on test results\n"
        
        # Save report
        with open("uart_configuration_report.md", "w") as f:
            f.write(report_content)
        
        print(f"✅ Report saved: uart_configuration_report.md")
    
    def run_comprehensive_test(self):
        """Run complete UART configuration verification"""
        print("🔧 UART Configuration & Timing Verification")
        print("=" * 60)
        print(f"Phase 5: Physical Layer Investigation")
        print(f"Objective: Verify UART configuration and timing accuracy")
        
        # Test sequence
        if not self.verify_port_availability():
            print(f"❌ Port verification failed")
            return False
        
        # Test baud rate accuracy
        self.test_baud_rate_accuracy(115200)
        
        # Test different configurations
        self.test_uart_parameter_combinations()
        
        # Analyze FPGA clock settings
        self.analyze_fpga_clock_settings()
        
        # Run stress test
        proceed_stress = input(f"\nRun 30-second stress test? (y/n): ")
        if proceed_stress.lower() == 'y':
            self.uart_stress_test(30)
        
        # Generate report
        self.generate_configuration_report()
        
        print(f"\n✅ UART configuration verification complete")
        return True

def main():
    """Main execution"""
    print("🎯 UART Configuration & Timing Verification Tool")
    print("Phase 5: Physical Layer Investigation")
    print("=" * 60)
    
    port = input(f"Enter UART port (default: COM3): ").strip() or "COM3"
    
    verifier = UartConfigVerifier(port)
    
    print(f"\n📋 Test Plan:")
    print(f"✅ Port availability verification")
    print(f"✅ Baud rate accuracy measurement")
    print(f"✅ Parameter combination testing")
    print(f"✅ FPGA clock analysis")
    print(f"✅ Optional stress testing")
    
    proceed = input(f"\nProceed with UART verification? (y/n): ")
    if proceed.lower() == 'y':
        success = verifier.run_comprehensive_test()
        if success:
            print(f"\n🎉 Verification completed successfully")
        else:
            print(f"\n❌ Verification failed")
    else:
        print(f"Test cancelled")

if __name__ == "__main__":
    main()