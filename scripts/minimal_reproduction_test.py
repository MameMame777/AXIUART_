#!/usr/bin/env python3
"""
最小再現ケース: UART Driver タイミングバグ検証
単一 Write コマンド (ADDR=0x00001000, DATA=0x42) を実行
"""

import subprocess
import sys
import time
from pathlib import Path

def run_minimal_test():
    """Run minimal UART driver timing test"""
    
    workspace = Path("e:/Nautilus/workspace/fpgawork/AXIUART_")
    
    print("=" * 80)
    print("MINIMAL REPRODUCTION CASE: UART Driver Timing Bug Verification")
    print("=" * 80)
    print(f"Workspace: {workspace}")
    print(f"Test: uart_axi4_basic_test (single write command)")
    print(f"Expected: SOF=0x5A in driver logs (before patch: 0xAD)")
    print("=" * 80)
    
    # MCP client command
    cmd = [
        "python",
        "mcp_server/mcp_client.py",
        "--workspace", str(workspace),
        "--tool", "run_uvm_simulation",
        "--test-name", "uart_axi4_basic_test",
        "--mode", "run",
        "--verbosity", "UVM_LOW",  # Reduce log noise
        "--waves",  # Enable for debug
        "--timeout", "300"
    ]
    
    print("\nExecuting command:")
    print(" ".join(cmd))
    print()
    
    start_time = time.time()
    
    try:
        result = subprocess.run(
            cmd,
            cwd=workspace,
            capture_output=True,
            text=True,
            timeout=600  # 10 min wall-clock timeout
        )
        
        elapsed = time.time() - start_time
        
        print("\n" + "=" * 80)
        print(f"Execution completed in {elapsed:.1f} seconds")
        print("=" * 80)
        
        # Parse output
        output = result.stdout + result.stderr
        
        # Critical markers
        markers = {
            "collected_sof": "Collected SOF byte:",
            "sof_expected": "expected 0x5A",
            "monitor_reports": "Monitor reported",
            "test_passed": "status\": \"success",
            "test_failed": "status\": \"failure"
        }
        
        findings = {}
        for key, marker in markers.items():
            if marker in output:
                # Extract surrounding context
                idx = output.find(marker)
                context = output[max(0, idx-100):idx+200]
                findings[key] = context
        
        # Report
        print("\n### FINDINGS ###")
        if "collected_sof" in findings:
            print(f"✅ Driver collected SOF byte:")
            print(f"   {findings['collected_sof']}")
        else:
            print("❌ Driver did not log SOF collection")
        
        if "test_passed" in findings:
            print("✅ Test PASSED")
        elif "test_failed" in findings:
            print("❌ Test FAILED")
        else:
            print("⚠️  Test status unclear")
        
        print("\n### VERIFICATION ###")
        print("Expected behavior (after patch):")
        print("  - Driver logs: 'Collected SOF byte: 0x5A (expected 0x5A)'")
        print("  - Test status: success")
        print("  - CRC validation: passed")
        
        print("\nBefore patch:")
        print("  - Driver read: 0xAD (1-bit shift error)")
        print("  - Monitor read: 0x5A (correct)")
        print("  - Test status: failure")
        
        return result.returncode == 0
        
    except subprocess.TimeoutExpired:
        print("❌ TIMEOUT: Simulation exceeded 10 minutes")
        return False
    except Exception as e:
        print(f"❌ ERROR: {e}")
        return False

if __name__ == "__main__":
    success = run_minimal_test()
    sys.exit(0 if success else 1)
