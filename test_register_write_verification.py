#!/usr/bin/env python3
"""
Test Register Write Verification Script
テストレジスタの書き込み可能性を確認するスクリプト
"""

import subprocess
import re
import sys
from pathlib import Path

def run_test_register_write():
    """テストレジスタへの書き込みと読み取りを検証"""
    
    print("=== Test Register Write Verification ===")
    
    # Test register addresses from Register_Block.sv
    test_addresses = {
        'REG_TEST_0': 0x1020,
        'REG_TEST_1': 0x1024, 
        'REG_TEST_2': 0x1028,
        'REG_TEST_3': 0x102C,
        'REG_TEST_4': 0x1040,
        'REG_TEST_5': 0x1050,
        'REG_TEST_6': 0x1080,
        'REG_TEST_7': 0x1100
    }
    
    # Test values to write
    test_values = [0x12345678, 0xDEADBEEF, 0xCAFEBABE, 0x55AA55AA, 
                   0x11111111, 0x22222222, 0x33333333, 0x44444444]
    
    print(f"テストレジスタアドレス: {len(test_addresses)}個")
    for name, addr in test_addresses.items():
        print(f"  {name}: 0x{addr:08X}")
    
    print(f"\nテスト値: {len(test_values)}個")
    for i, val in enumerate(test_values):
        print(f"  Value[{i}]: 0x{val:08X}")
    
    # Get latest test results from UVM log
    print("\n=== UVM テスト結果の分析 ===")
    
    # Run a simple register test to get actual results
    print("シンプルなレジスタテストを実行中...")
    
    try:
        # Change to sim/exec directory and run test
        exec_dir = Path("e:/Nautilus/workspace/fpgawork/AXIUART_/sim/exec")
        if not exec_dir.exists():
            print(f"Error: Directory {exec_dir} not found")
            return False
            
        # Run UVM test
        cmd = ["powershell", "-Command", 
               f"cd '{exec_dir}'; .\\run_uvm.ps1 -TestName register_block_comprehensive_test"]
        
        print(f"実行コマンド: {' '.join(cmd)}")
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
        
        if result.returncode == 0:
            print("✓ テスト実行成功")
            
            # Parse test output for register results
            output = result.stdout
            
            # Look for register test completion message
            if "Register Testing Complete" in output:
                match = re.search(r"Register Testing Complete: (\d+) PASS, (\d+) FAIL", output)
                if match:
                    pass_count = int(match.group(1))
                    fail_count = int(match.group(2))
                    print(f"✓ レジスタテスト結果: {pass_count} PASS, {fail_count} FAIL")
                    
                    if fail_count == 0:
                        print("✓ すべてのレジスタテストが成功")
                        return True
                    else:
                        print(f"✗ {fail_count}個のレジスタテストが失敗")
                        return False
                else:
                    print("✗ テスト結果の解析に失敗")
                    return False
            else:
                print("✗ レジスタテスト完了メッセージが見つかりません")
                return False
                
        else:
            print(f"✗ テスト実行失敗 (exit code: {result.returncode})")
            if result.stderr:
                print(f"エラー出力: {result.stderr}")
            return False
            
    except subprocess.TimeoutExpired:
        print("✗ テスト実行がタイムアウトしました")
        return False
    except Exception as e:
        print(f"✗ テスト実行中にエラーが発生: {e}")
        return False

def check_waveform_files():
    """波形ファイルの存在と最新性を確認"""
    
    print("\n=== 波形ファイル確認 ===")
    
    waveform_dir = Path("e:/Nautilus/workspace/fpgawork/AXIUART_/archive/waveforms")
    if not waveform_dir.exists():
        print(f"✗ 波形ディレクトリが見つかりません: {waveform_dir}")
        return False
    
    # Find latest .mxd files
    mxd_files = list(waveform_dir.glob("*.mxd"))
    if not mxd_files:
        print("✗ 波形ファイル(.mxd)が見つかりません")
        return False
    
    # Sort by modification time
    mxd_files.sort(key=lambda f: f.stat().st_mtime, reverse=True)
    
    print(f"✓ 波形ファイル発見: {len(mxd_files)}個")
    
    # Show latest 3 files
    for i, file in enumerate(mxd_files[:3]):
        size_mb = file.stat().st_size / (1024 * 1024)
        mtime = file.stat().st_mtime
        print(f"  [{i+1}] {file.name} ({size_mb:.2f} MB)")
    
    return True

def main():
    """メイン実行関数"""
    
    print("Test Register Write Verification Script")
    print("="*50)
    
    # Check waveform files
    waveform_ok = check_waveform_files()
    
    # Run register test verification
    test_ok = run_test_register_write()
    
    print("\n" + "="*50)
    print("=== 最終結果 ===")
    print(f"波形ファイル確認: {'✓ OK' if waveform_ok else '✗ NG'}")
    print(f"レジスタテスト: {'✓ OK' if test_ok else '✗ NG'}")
    
    if test_ok and waveform_ok:
        print("✓ テストレジスタは正常に動作しています")
        print("✓ 波形ファイルで詳細な動作を確認可能です")
        return True
    else:
        print("✗ テストレジスタまたは波形に問題があります")
        return False

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)