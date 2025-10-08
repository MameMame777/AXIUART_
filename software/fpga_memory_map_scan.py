#!/usr/bin/env python3
"""
FPGA Memory Map Scanner
FPGAに実装されている実際のメモリマップを詳細調査するツール
作業指示: fpga_register_debug_work_instructions_20251007.md - Phase 1, 作業1-1
"""

import serial
import time
from typing import Dict, List, Tuple, Any

class FPGAMemoryMapScanner:
    def __init__(self, port: str = "COM3", baudrate: int = 115200):
        self.port = port
        self.baudrate = baudrate
        self.serial = None
        
        # アドレス範囲定義（作業指示書に基づく）
        self.address_ranges = {
            "Standard_Registers": {
                "range": range(0x00001000, 0x00001020, 4),
                "description": "Control, Status, Config, Debug, Counters, Version"
            },
            "REG_TEST_Registers": {
                "range": range(0x00001020, 0x00001030, 4),
                "description": "Test registers for debugging"
            },
            "Extended_Range": {
                "range": range(0x00001030, 0x00001100, 4),
                "description": "Unknown/extended register range"
            },
            "High_Address_Test": {
                "range": range(0x00002000, 0x00002020, 4),
                "description": "High address range test"
            }
        }
        
    def connect(self) -> bool:
        """UART接続"""
        try:
            self.serial = serial.Serial(self.port, self.baudrate, timeout=2.0)
            time.sleep(0.1)
            print(f"✅ Connected to {self.port}")
            return True
        except Exception as e:
            print(f"❌ Failed to connect: {e}")
            return False
    
    def disconnect(self):
        """UART切断"""
        if self.serial and self.serial.is_open:
            self.serial.close()
            print("🔌 Disconnected")
    
    def crc8_calculate(self, data: bytes) -> int:
        """CRC8計算 (polynomial 0x07)"""
        crc = 0x00
        for byte in data:
            crc ^= byte
            for _ in range(8):
                if crc & 0x80:
                    crc = (crc << 1) ^ 0x07
                else:
                    crc = (crc << 1)
        return crc & 0xFF
    
    def read_register(self, address: int) -> Tuple[bool, bytes, Dict[str, Any]]:
        """レジスタ読み出しと詳細解析"""
        try:
            # コマンドフレーム構築
            frame = bytearray()
            frame.append(0xA5)  # SOF
            frame.append(0xA0)  # Read command
            frame.extend(address.to_bytes(4, 'little'))  # Address
            
            # CRC計算・追加
            crc = self.crc8_calculate(frame[1:])
            frame.append(crc)
            
            # 送信
            self.serial.reset_input_buffer()
            self.serial.write(frame)
            self.serial.flush()
            time.sleep(0.1)
            
            # 受信
            response = self.serial.read(20)
            
            # 解析
            analysis = self._analyze_response(address, frame, response)
            
            return len(response) > 0, response, analysis
            
        except Exception as e:
            return False, b'', {'error': str(e)}
    
    def _analyze_response(self, address: int, command: bytes, response: bytes) -> Dict[str, Any]:
        """応答詳細解析"""
        analysis = {
            'address': f"0x{address:08X}",
            'command_sent': command.hex(' ').upper(),
            'response_received': response.hex(' ').upper() if response else "No response",
            'response_length': len(response),
            'timestamp': time.time()
        }
        
        if len(response) >= 8:
            # 正常応答の場合
            sof = response[0]
            status = response[1]
            cmd_echo = response[2]
            data_bytes = response[3:7]
            crc_received = response[7]
            
            data_value = int.from_bytes(data_bytes, 'little')
            
            analysis.update({
                'sof': f"0x{sof:02X}",
                'sof_correct': sof == 0xAD,
                'status': f"0x{status:02X}",
                'status_ok': status == 0x80,
                'cmd_echo': f"0x{cmd_echo:02X}",
                'cmd_echo_correct': cmd_echo == 0x68,
                'data_value': f"0x{data_value:08X}",
                'data_bytes': data_bytes.hex(' ').upper(),
                'crc_received': f"0x{crc_received:02X}",
                'pattern_analysis': self._analyze_data_pattern(data_value, address)
            })
            
            # CRC検証
            expected_crc = self.crc8_calculate(response[1:7])
            analysis['crc_valid'] = crc_received == expected_crc
            analysis['expected_crc'] = f"0x{expected_crc:02X}"
            
        elif len(response) >= 4:
            # エラー応答の場合
            analysis.update({
                'sof': f"0x{response[0]:02X}",
                'status': f"0x{response[1]:02X}",
                'error_response': True,
                'short_response': True
            })
        else:
            # 応答なしまたは不完全応答
            analysis['incomplete_response'] = True
            
        return analysis
    
    def _analyze_data_pattern(self, data_value: int, address: int) -> Dict[str, Any]:
        """データパターン解析"""
        # 既知のパターン検出
        patterns = {
            0xDEADBEEF: "REG_TEST_0_INITIAL",
            0x12345678: "REG_TEST_1_INITIAL", 
            0xABCDEF00: "REG_TEST_2_INITIAL",
            0x00000000: "REG_TEST_3_INITIAL",
            0x00010000: "VERSION_REGISTER"
        }
        
        pattern_analysis = {
            'known_pattern': patterns.get(data_value, "UNKNOWN"),
            'is_zero': data_value == 0,
            'is_all_ones': data_value == 0xFFFFFFFF,
            'byte_pattern': self._detect_byte_pattern(data_value),
            'correlation_with_address': self._check_address_correlation(data_value, address)
        }
        
        # FPGAで観測された特殊パターンの検出
        if (data_value & 0xFFFFFF00) == 0xF0202200:
            pattern_analysis['fpga_test_pattern'] = True
            pattern_analysis['pattern_offset'] = data_value & 0xFF
            pattern_analysis['base_pattern'] = "0xF02022XX"
        
        return pattern_analysis
    
    def _detect_byte_pattern(self, value: int) -> str:
        """バイトパターン検出"""
        bytes_val = [(value >> (8*i)) & 0xFF for i in range(4)]
        
        if all(b == bytes_val[0] for b in bytes_val):
            return f"REPEATED_BYTE_0x{bytes_val[0]:02X}"
        elif bytes_val == [0x55, 0x55, 0x55, 0x55]:
            return "ALTERNATING_01"
        elif bytes_val == [0xAA, 0xAA, 0xAA, 0xAA]:
            return "ALTERNATING_10"
        else:
            return "MIXED"
    
    def _check_address_correlation(self, data_value: int, address: int) -> Dict[str, Any]:
        """アドレスとデータの相関分析"""
        correlation = {
            'data_contains_address': (address & 0xFFFFFFFF) in [
                data_value, data_value >> 8, data_value >> 16, data_value >> 24
            ],
            'data_offset_correlation': False,
            'sequential_pattern': False
        }
        
        # アドレスオフセットとの相関
        addr_offset = address & 0xFF
        data_low_byte = data_value & 0xFF
        if abs(addr_offset - data_low_byte) < 16:
            correlation['data_offset_correlation'] = True
            correlation['offset_difference'] = data_low_byte - addr_offset
            
        return correlation
    
    def scan_range(self, range_name: str, range_info: Dict) -> Dict[str, Any]:
        """指定範囲のスキャン実行"""
        print(f"\n📍 Scanning {range_name}")
        print(f"   Description: {range_info['description']}")
        print(f"   Address range: 0x{min(range_info['range']):08X} - 0x{max(range_info['range']):08X}")
        print("-" * 60)
        
        results = {
            'range_name': range_name,
            'description': range_info['description'],
            'addresses_scanned': [],
            'successful_reads': 0,
            'failed_reads': 0,
            'responses': {},
            'pattern_summary': {},
            'anomalies': []
        }
        
        for address in range_info['range']:
            success, response, analysis = self.read_register(address)
            
            results['addresses_scanned'].append(address)
            results['responses'][address] = analysis
            
            if success:
                results['successful_reads'] += 1
                print(f"   0x{address:08X}: {analysis.get('data_value', 'N/A')} - {analysis.get('pattern_analysis', {}).get('known_pattern', 'UNKNOWN')}")
            else:
                results['failed_reads'] += 1
                print(f"   0x{address:08X}: FAILED - {analysis.get('error', 'Unknown error')}")
            
            time.sleep(0.05)  # 連続アクセス間隔
        
        # パターンサマリ作成
        results['pattern_summary'] = self._create_pattern_summary(results['responses'])
        
        return results
    
    def _create_pattern_summary(self, responses: Dict) -> Dict[str, Any]:
        """スキャン結果のパターンサマリ作成"""
        summary = {
            'unique_data_values': set(),
            'fpga_test_patterns': [],
            'known_patterns': [],
            'error_responses': 0,
            'address_correlations': []
        }
        
        for address, analysis in responses.items():
            if 'data_value' in analysis:
                data_val = int(analysis['data_value'], 16)
                summary['unique_data_values'].add(data_val)
                
                # FPGAテストパターン検出
                pattern_info = analysis.get('pattern_analysis', {})
                if pattern_info.get('fpga_test_pattern'):
                    summary['fpga_test_patterns'].append({
                        'address': address,
                        'value': analysis['data_value'],
                        'offset': pattern_info.get('pattern_offset')
                    })
                
                # 既知パターン記録
                known = pattern_info.get('known_pattern')
                if known != 'UNKNOWN':
                    summary['known_patterns'].append({
                        'address': address,
                        'pattern': known,
                        'value': analysis['data_value']
                    })
            
            # エラー応答カウント
            if analysis.get('error_response') or analysis.get('incomplete_response'):
                summary['error_responses'] += 1
        
        summary['unique_data_values'] = list(summary['unique_data_values'])
        return summary
    
    def run_comprehensive_scan(self) -> Dict[str, Any]:
        """包括的メモリマップスキャンの実行"""
        if not self.connect():
            return {'error': 'Failed to connect to FPGA'}
        
        print("🔍 FPGA Memory Map Comprehensive Scan")
        print("=" * 60)
        print("Target: REG_TEST register implementation analysis")
        print("Objective: Identify actual FPGA memory map vs expected RTL")
        print("=" * 60)
        
        scan_results = {
            'scan_timestamp': time.time(),
            'ranges_scanned': {},
            'overall_summary': {},
            'recommendations': []
        }
        
        try:
            # 各範囲のスキャン実行
            for range_name, range_info in self.address_ranges.items():
                scan_results['ranges_scanned'][range_name] = self.scan_range(range_name, range_info)
            
            # 全体サマリ作成
            scan_results['overall_summary'] = self._create_overall_summary(scan_results['ranges_scanned'])
            
            # 推奨事項生成
            scan_results['recommendations'] = self._generate_recommendations(scan_results)
            
        except Exception as e:
            scan_results['scan_error'] = str(e)
        finally:
            self.disconnect()
        
        return scan_results
    
    def _create_overall_summary(self, range_results: Dict) -> Dict[str, Any]:
        """全体サマリ作成"""
        summary = {
            'total_addresses_scanned': 0,
            'total_successful_reads': 0,
            'total_failed_reads': 0,
            'all_unique_values': set(),
            'fpga_test_pattern_addresses': [],
            'register_function_evidence': {},
            'anomaly_count': 0
        }
        
        for range_name, range_result in range_results.items():
            summary['total_addresses_scanned'] += len(range_result['addresses_scanned'])
            summary['total_successful_reads'] += range_result['successful_reads']
            summary['total_failed_reads'] += range_result['failed_reads']
            
            # FPGAテストパターンの収集
            for pattern in range_result['pattern_summary']['fpga_test_patterns']:
                summary['fpga_test_pattern_addresses'].append(pattern)
            
            # ユニーク値の収集
            summary['all_unique_values'].update(range_result['pattern_summary']['unique_data_values'])
        
        summary['all_unique_values'] = list(summary['all_unique_values'])
        
        # パターン分析
        if summary['fpga_test_pattern_addresses']:
            summary['fpga_test_pattern_confirmed'] = True
            summary['register_implementation_status'] = 'TEST_PATTERN_GENERATOR'
        else:
            summary['fpga_test_pattern_confirmed'] = False
            summary['register_implementation_status'] = 'UNKNOWN'
        
        return summary
    
    def _generate_recommendations(self, scan_results: Dict) -> List[str]:
        """推奨事項生成"""
        recommendations = []
        
        overall = scan_results['overall_summary']
        
        if overall.get('fpga_test_pattern_confirmed'):
            recommendations.extend([
                "CRITICAL: FPGA contains test pattern generator instead of register implementation",
                "ACTION: Verify Register_Block.sv deployment to FPGA",
                "ACTION: Check FPGA bitstream generation date vs RTL update date",
                "ACTION: Coordinate with hardware team for RTL re-deployment"
            ])
        
        if overall['total_failed_reads'] > 0:
            recommendations.append(f"WARNING: {overall['total_failed_reads']} addresses failed to respond")
        
        if len(overall['all_unique_values']) < 4:
            recommendations.append("WARNING: Limited value diversity suggests non-functional registers")
        
        # REG_TEST範囲の特別チェック
        reg_test_results = scan_results['ranges_scanned'].get('REG_TEST_Registers')
        if reg_test_results:
            if reg_test_results['successful_reads'] == 0:
                recommendations.append("CRITICAL: REG_TEST registers completely non-responsive")
            elif reg_test_results['pattern_summary']['fpga_test_patterns']:
                recommendations.append("CONFIRMED: REG_TEST addresses return test pattern, not register values")
        
        return recommendations
    
    def print_detailed_report(self, scan_results: Dict):
        """詳細レポート出力"""
        print("\n" + "=" * 80)
        print("📊 DETAILED SCAN REPORT")
        print("=" * 80)
        
        # 全体サマリ
        overall = scan_results['overall_summary']
        print(f"Total addresses scanned: {overall['total_addresses_scanned']}")
        print(f"Successful reads: {overall['total_successful_reads']}")
        print(f"Failed reads: {overall['total_failed_reads']}")
        print(f"Success rate: {overall['total_successful_reads']/overall['total_addresses_scanned']*100:.1f}%")
        
        # FPGAテストパターン分析
        if overall.get('fpga_test_pattern_confirmed'):
            print(f"\n🚨 FPGA TEST PATTERN DETECTED:")
            for pattern in overall['fpga_test_pattern_addresses']:
                print(f"   Address 0x{pattern['address']:08X}: {pattern['value']} (offset: {pattern['offset']})")
        
        # 推奨事項
        print(f"\n📋 RECOMMENDATIONS:")
        for i, rec in enumerate(scan_results['recommendations'], 1):
            print(f"   {i}. {rec}")
        
        print("\n" + "=" * 80)

if __name__ == "__main__":
    scanner = FPGAMemoryMapScanner()
    
    print("Starting FPGA Memory Map Comprehensive Scan...")
    print("This tool implements Phase 1, Task 1-1 from fpga_register_debug_work_instructions_20251007.md")
    print()
    
    results = scanner.run_comprehensive_scan()
    
    if 'error' not in results:
        scanner.print_detailed_report(results)
        
        # 結果保存
        import json
        timestamp = time.strftime("%Y%m%d_%H%M%S")
        filename = f"fpga_memory_scan_results_{timestamp}.json"
        
        # JSON serializable形式に変換
        json_results = json.loads(json.dumps(results, default=str))
        
        with open(filename, 'w') as f:
            json.dump(json_results, f, indent=2)
        
        print(f"\n💾 Results saved to: {filename}")
    else:
        print(f"❌ Scan failed: {results['error']}")