#!/usr/bin/env python3
"""
FPGA Write Sequence Test Tool
書き込み→読み戻しシーケンステストでFPGAの実際の動作を詳細調査
作業指示: fpga_register_debug_work_instructions_20251007.md - Phase 1, 作業1-2
"""

import serial
import time
from typing import Dict, List, Tuple, Any

class FPGAWriteSequenceTest:
    def __init__(self, port: str = "COM3", baudrate: int = 115200):
        self.port = port
        self.baudrate = baudrate
        self.serial = None
        
        # テストパターン定義（作業指示書に基づく）
        self.test_patterns = [
            0x00000000,  # All zeros
            0xFFFFFFFF,  # All ones
            0x55555555,  # Alternating 01
            0xAAAAAAAA,  # Alternating 10
            0x12345678,  # Sequential pattern
            0x87654321,  # Reverse sequential
            0xDEADBEEF,  # Known test pattern
            0xCAFEBABE   # Another known pattern
        ]
        
        # REG_TESTアドレス
        self.reg_test_addresses = [
            0x00001020,  # REG_TEST_0
            0x00001024,  # REG_TEST_1  
            0x00001028,  # REG_TEST_2
            0x0000102C   # REG_TEST_3
        ]
        
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
    
    def send_command(self, cmd: int, addr: int, data: bytes = None) -> Tuple[bool, bytes, Dict[str, Any]]:
        """コマンド送信と応答解析"""
        try:
            # フレーム構築
            frame = bytearray()
            frame.append(0xA5)  # SOF
            frame.append(cmd)   # Command
            frame.extend(addr.to_bytes(4, 'little'))  # Address
            
            if data:
                frame.extend(data)  # Data for write commands
            
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
            analysis = self._analyze_response(cmd, addr, frame, response, data)
            
            return len(response) > 0, response, analysis
            
        except Exception as e:
            return False, b'', {'error': str(e)}
    
    def _analyze_response(self, cmd: int, addr: int, command: bytes, response: bytes, sent_data: bytes = None) -> Dict[str, Any]:
        """応答詳細解析"""
        analysis = {
            'command_type': 'READ' if cmd == 0xA0 else 'WRITE',
            'address': f"0x{addr:08X}",
            'command_sent': command.hex(' ').upper(),
            'response_received': response.hex(' ').upper() if response else "No response",
            'response_length': len(response),
            'timestamp': time.time()
        }
        
        if sent_data:
            analysis['data_sent'] = sent_data.hex(' ').upper()
            analysis['data_sent_value'] = f"0x{int.from_bytes(sent_data, 'little'):08X}"
        
        if len(response) >= 4:
            sof = response[0]
            status = response[1]
            
            analysis.update({
                'sof': f"0x{sof:02X}",
                'sof_correct': sof == 0xAD,
                'status': f"0x{status:02X}",
                'operation_success': status == 0x80
            })
            
            if cmd == 0xA0 and len(response) >= 8:  # Read command response
                cmd_echo = response[2]
                data_bytes = response[3:7]
                crc_received = response[7]
                
                data_value = int.from_bytes(data_bytes, 'little')
                
                analysis.update({
                    'cmd_echo': f"0x{cmd_echo:02X}",
                    'cmd_echo_correct': cmd_echo == 0x68,
                    'data_value': f"0x{data_value:08X}",
                    'data_bytes': data_bytes.hex(' ').upper(),
                    'crc_received': f"0x{crc_received:02X}"
                })
                
                # CRC検証
                expected_crc = self.crc8_calculate(response[1:7])
                analysis['crc_valid'] = crc_received == expected_crc
                analysis['expected_crc'] = f"0x{expected_crc:02X}"
                
            elif cmd == 0x20 and len(response) >= 4:  # Write command response
                if len(response) > 4:
                    analysis['cmd_echo'] = f"0x{response[2]:02X}"
                    analysis['write_crc'] = f"0x{response[3]:02X}"
        
        return analysis
    
    def write_register(self, addr: int, value: int) -> Tuple[bool, Dict[str, Any]]:
        """レジスタ書き込み"""
        data = value.to_bytes(4, 'little')
        success, response, analysis = self.send_command(0x20, addr, data)
        return success and analysis.get('operation_success', False), analysis
    
    def read_register(self, addr: int) -> Tuple[bool, int, Dict[str, Any]]:
        """レジスタ読み出し"""
        success, response, analysis = self.send_command(0xA0, addr)
        
        if success and 'data_value' in analysis:
            data_value = int(analysis['data_value'], 16)
            return True, data_value, analysis
        else:
            return False, 0, analysis
    
    def run_sequence_test(self, address: int) -> Dict[str, Any]:
        """指定アドレスでのシーケンステスト実行"""
        print(f"\n📍 Testing Address 0x{address:08X}")
        print("-" * 50)
        
        test_results = {
            'address': f"0x{address:08X}",
            'initial_read': {},
            'pattern_tests': [],
            'final_read': {},
            'summary': {
                'total_patterns': len(self.test_patterns),
                'successful_writes': 0,
                'successful_reads': 0,
                'data_matches': 0,
                'write_effects': 'NONE'  # NONE, PARTIAL, FULL
            }
        }
        
        # 1. 初期値読み出し
        print("1️⃣ Reading initial value...")
        success, initial_value, analysis = self.read_register(address)
        test_results['initial_read'] = analysis
        if success:
            print(f"   Initial value: 0x{initial_value:08X}")
        else:
            print("   ❌ Failed to read initial value")
            return test_results
        
        # 2. パターンテスト実行
        print("2️⃣ Running pattern tests...")
        
        for i, pattern in enumerate(self.test_patterns):
            print(f"   Pattern {i+1}/8: 0x{pattern:08X}")
            
            pattern_result = {
                'pattern': f"0x{pattern:08X}",
                'write_success': False,
                'read_success': False,
                'data_match': False,
                'write_analysis': {},
                'read_analysis': {},
                'readback_value': None
            }
            
            # 書き込み実行
            write_success, write_analysis = self.write_register(address, pattern)
            pattern_result['write_success'] = write_success
            pattern_result['write_analysis'] = write_analysis
            
            if write_success:
                test_results['summary']['successful_writes'] += 1
                print(f"     ✅ Write successful")
                
                # 読み戻し実行
                time.sleep(0.05)  # 書き込み完了待ち
                read_success, readback_value, read_analysis = self.read_register(address)
                pattern_result['read_success'] = read_success
                pattern_result['read_analysis'] = read_analysis
                pattern_result['readback_value'] = f"0x{readback_value:08X}"
                
                if read_success:
                    test_results['summary']['successful_reads'] += 1
                    data_match = (readback_value == pattern)
                    pattern_result['data_match'] = data_match
                    
                    if data_match:
                        test_results['summary']['data_matches'] += 1
                        print(f"     ✅ Read back: 0x{readback_value:08X} (MATCH)")
                    else:
                        print(f"     ❌ Read back: 0x{readback_value:08X} (MISMATCH - expected 0x{pattern:08X})")
                else:
                    print(f"     ❌ Read failed")
            else:
                print(f"     ❌ Write failed")
            
            test_results['pattern_tests'].append(pattern_result)
            time.sleep(0.1)  # パターン間隔
        
        # 3. 最終値読み出し
        print("3️⃣ Reading final value...")
        success, final_value, analysis = self.read_register(address)
        test_results['final_read'] = analysis
        if success:
            print(f"   Final value: 0x{final_value:08X}")
        
        # 4. サマリ作成
        summary = test_results['summary']
        if summary['data_matches'] == summary['total_patterns']:
            summary['write_effects'] = 'FULL'
        elif summary['data_matches'] > 0:
            summary['write_effects'] = 'PARTIAL'
        else:
            summary['write_effects'] = 'NONE'
        
        print(f"\n📊 Summary:")
        print(f"   Successful writes: {summary['successful_writes']}/{summary['total_patterns']}")
        print(f"   Successful reads: {summary['successful_reads']}/{summary['total_patterns']}")
        print(f"   Data matches: {summary['data_matches']}/{summary['total_patterns']}")
        print(f"   Write effect: {summary['write_effects']}")
        
        return test_results
    
    def run_comprehensive_test(self) -> Dict[str, Any]:
        """全REG_TESTアドレスでの包括的テスト"""
        if not self.connect():
            return {'error': 'Failed to connect to FPGA'}
        
        print("🧪 FPGA Write Sequence Comprehensive Test")
        print("=" * 60)
        print("Target: REG_TEST register write/read verification")
        print("Objective: Determine if writes affect readback values")
        print("=" * 60)
        
        comprehensive_results = {
            'test_timestamp': time.time(),
            'addresses_tested': {},
            'overall_analysis': {},
            'conclusions': []
        }
        
        try:
            # 各REG_TESTアドレスでテスト実行
            for addr in self.reg_test_addresses:
                comprehensive_results['addresses_tested'][f"0x{addr:08X}"] = self.run_sequence_test(addr)
            
            # 全体分析
            comprehensive_results['overall_analysis'] = self._create_overall_analysis(comprehensive_results['addresses_tested'])
            
            # 結論生成
            comprehensive_results['conclusions'] = self._generate_conclusions(comprehensive_results)
            
        except Exception as e:
            comprehensive_results['test_error'] = str(e)
        finally:
            self.disconnect()
        
        return comprehensive_results
    
    def _create_overall_analysis(self, address_results: Dict) -> Dict[str, Any]:
        """全体分析作成"""
        analysis = {
            'total_addresses_tested': len(address_results),
            'total_patterns_tested': 0,
            'total_successful_writes': 0,
            'total_successful_reads': 0,
            'total_data_matches': 0,
            'addresses_with_full_effect': [],
            'addresses_with_partial_effect': [],
            'addresses_with_no_effect': [],
            'consistent_behavior': True
        }
        
        write_effects = []
        
        for addr_str, result in address_results.items():
            summary = result['summary']
            analysis['total_patterns_tested'] += summary['total_patterns']
            analysis['total_successful_writes'] += summary['successful_writes']
            analysis['total_successful_reads'] += summary['successful_reads']
            analysis['total_data_matches'] += summary['data_matches']
            
            effect = summary['write_effects']
            write_effects.append(effect)
            
            if effect == 'FULL':
                analysis['addresses_with_full_effect'].append(addr_str)
            elif effect == 'PARTIAL':
                analysis['addresses_with_partial_effect'].append(addr_str)
            else:
                analysis['addresses_with_no_effect'].append(addr_str)
        
        # 一貫性チェック
        analysis['consistent_behavior'] = len(set(write_effects)) <= 1
        analysis['dominant_behavior'] = max(set(write_effects), key=write_effects.count) if write_effects else 'UNKNOWN'
        
        # 成功率計算
        if analysis['total_patterns_tested'] > 0:
            analysis['write_success_rate'] = analysis['total_successful_writes'] / analysis['total_patterns_tested'] * 100
            analysis['read_success_rate'] = analysis['total_successful_reads'] / analysis['total_patterns_tested'] * 100
            analysis['data_match_rate'] = analysis['total_data_matches'] / analysis['total_patterns_tested'] * 100
        
        return analysis
    
    def _generate_conclusions(self, test_results: Dict) -> List[str]:
        """結論生成"""
        conclusions = []
        
        analysis = test_results['overall_analysis']
        
        # 書き込み成功率
        if analysis.get('write_success_rate', 0) > 90:
            conclusions.append("✅ WRITE OPERATIONS: Highly successful (>90% success rate)")
        elif analysis.get('write_success_rate', 0) > 50:
            conclusions.append("⚠️ WRITE OPERATIONS: Partially successful (50-90% success rate)")
        else:
            conclusions.append("❌ WRITE OPERATIONS: Poor success rate (<50%)")
        
        # 読み戻し成功率
        if analysis.get('read_success_rate', 0) > 90:
            conclusions.append("✅ READ OPERATIONS: Highly successful (>90% success rate)")
        elif analysis.get('read_success_rate', 0) > 50:
            conclusions.append("⚠️ READ OPERATIONS: Partially successful (50-90% success rate)")
        else:
            conclusions.append("❌ READ OPERATIONS: Poor success rate (<50%)")
        
        # データ一致率
        if analysis.get('data_match_rate', 0) > 90:
            conclusions.append("✅ DATA CONSISTENCY: Written values correctly read back (>90% match rate)")
        elif analysis.get('data_match_rate', 0) > 10:
            conclusions.append("⚠️ DATA CONSISTENCY: Partial data persistence (10-90% match rate)")
        else:
            conclusions.append("❌ DATA CONSISTENCY: No data persistence (<10% match rate)")
        
        # 全体的な動作判定
        dominant = analysis.get('dominant_behavior', 'UNKNOWN')
        if dominant == 'FULL':
            conclusions.append("🎯 OVERALL: Registers appear to be fully functional")
        elif dominant == 'PARTIAL':
            conclusions.append("🔧 OVERALL: Registers show partial functionality - needs investigation")
        elif dominant == 'NONE':
            conclusions.append("🚨 OVERALL: Registers not functional - test pattern generator confirmed")
        
        # 一貫性判定
        if analysis.get('consistent_behavior', False):
            conclusions.append("📊 BEHAVIOR: Consistent across all tested addresses")
        else:
            conclusions.append("⚠️ BEHAVIOR: Inconsistent across addresses - mixed implementation")
        
        return conclusions
    
    def print_detailed_report(self, test_results: Dict):
        """詳細レポート出力"""
        print("\n" + "=" * 80)
        print("📊 WRITE SEQUENCE TEST DETAILED REPORT")
        print("=" * 80)
        
        analysis = test_results['overall_analysis']
        
        print(f"Total test executions: {analysis['total_patterns_tested']}")
        print(f"Write success rate: {analysis.get('write_success_rate', 0):.1f}%")
        print(f"Read success rate: {analysis.get('read_success_rate', 0):.1f}%")
        print(f"Data match rate: {analysis.get('data_match_rate', 0):.1f}%")
        print(f"Dominant behavior: {analysis.get('dominant_behavior', 'UNKNOWN')}")
        
        print("\n📋 CONCLUSIONS:")
        for i, conclusion in enumerate(test_results['conclusions'], 1):
            print(f"   {i}. {conclusion}")
        
        print("\n" + "=" * 80)

if __name__ == "__main__":
    tester = FPGAWriteSequenceTest()
    
    print("Starting FPGA Write Sequence Comprehensive Test...")
    print("This tool implements Phase 1, Task 1-2 from fpga_register_debug_work_instructions_20251007.md")
    print()
    
    results = tester.run_comprehensive_test()
    
    if 'error' not in results:
        tester.print_detailed_report(results)
        
        # 結果保存
        import json
        timestamp = time.strftime("%Y%m%d_%H%M%S")
        filename = f"fpga_write_sequence_results_{timestamp}.json"
        
        # JSON serializable形式に変換
        json_results = json.loads(json.dumps(results, default=str))
        
        with open(filename, 'w') as f:
            json.dump(json_results, f, indent=2)
        
        print(f"\n💾 Results saved to: {filename}")
    else:
        print(f"❌ Test failed: {results['error']}")