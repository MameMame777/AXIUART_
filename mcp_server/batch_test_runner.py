#!/usr/bin/env python3
"""
Batch Test Execution Script
Execute multiple UVM tests and collect timeout statistics
"""

import asyncio
import json
import sys
from pathlib import Path
from datetime import datetime

# Add mcp_server to path
sys.path.insert(0, str(Path(__file__).parent / "mcp_server"))

# Import and configure workspace BEFORE using tools
from dsim_uvm_server import run_uvm_simulation
import dsim_uvm_server

# Set workspace root for dsim_uvm_server module
dsim_uvm_server.workspace_root = Path(__file__).parent.parent
print(f"[CONFIG] Workspace: {dsim_uvm_server.workspace_root}")

# Test list - representative samples from each category
TESTS_TO_RUN = [
    # Category 1: Minimal/Basic
    ("uart_axi4_minimal_test", "Minimal test - no sequences", 60),
    ("uart_axi4_basic_test", "Basic functional test - VERSION 5 sequence", 120),
    
    # Category 2: Simple operations
    ("uart_axi4_simple_write_test", "Simple write operation", 120),
    ("uart_axi4_single_read_test", "Simple read operation", 120),
    
    # Category 3: QA/Verification
    ("uart_axi4_qa_basic_test", "QA basic verification", 120),
    
    # Category 4: Protocol tests
    ("uart_axi4_write_protocol_test", "Write protocol verification", 150),
    ("uart_axi4_read_protocol_test", "Read protocol verification", 150),
    
    # Category 5: Error handling
    ("uart_axi4_error_protocol_test", "Error protocol test", 120),
    
    # Category 6: Register access
    ("uart_axi4_register_block_test", "Register block test", 150),
    ("simple_register_test", "Simple register access", 90),
]

async def run_single_test(test_name: str, description: str, timeout: int) -> dict:
    """Run a single test and return results"""
    print(f"\n{'='*80}")
    print(f"[TEST] {test_name}")
    print(f"[DESC] {description}")
    print(f"[TIMEOUT] {timeout}s")
    print(f"{'='*80}")
    
    start_time = datetime.now()
    
    try:
        result_text = await run_uvm_simulation(
            test_name=test_name,
            mode="run",
            verbosity="UVM_MEDIUM",
            timeout=timeout,
            waves=False,
            coverage=False
        )
        
        end_time = datetime.now()
        duration = (end_time - start_time).total_seconds()
        
        # Initialize defaults
        status = "unknown"
        is_timeout = False
        
        # Parse JSON result
        try:
            result_json = json.loads(result_text)
            json_status = result_json.get("status", "unknown")
            analysis = result_json.get("analysis", {})
            
            # Check for $finish (normal termination)
            has_finish = "$finish" in result_text
            
            # Check for timeout indicators
            has_timeout = (
                "TimeoutExpired" in result_text or
                duration >= timeout - 1 or
                "Simulation terminated after specified run time" in result_text or
                json_status == "timeout"
            )
            
            # SUCCESS: $finish with no timeout
            # TIMEOUT: timeout occurred regardless of errors
            # FAILED: neither success nor timeout
            if has_timeout:
                status = "timeout"
                is_timeout = True
            elif has_finish:
                # $finish = simulation completed, regardless of UVM errors
                status = "success"
                is_timeout = False
            else:
                status = "failed"
                is_timeout = False
                
        except json.JSONDecodeError:
            # Fallback to text parsing if not JSON
            is_success = "$finish" in result_text
            is_timeout = "TimeoutExpired" in result_text or duration >= timeout - 1
            status = "success" if is_success else ("timeout" if is_timeout else "failed")
        
        test_result = {
            "test_name": test_name,
            "description": description,
            "timeout_setting": timeout,
            "status": status,
            "is_timeout": is_timeout,
            "duration_seconds": duration,
            "result": result_text
        }
        
        if status == "success":
            print(f"[✅ SUCCESS] Test completed in {duration:.1f}s")
        elif is_timeout:
            print(f"[❌ TIMEOUT] Test timed out after {timeout}s")
        else:
            print(f"[❌ FAILED] Test failed")
        
        return test_result
        
    except Exception as e:
        end_time = datetime.now()
        duration = (end_time - start_time).total_seconds()
        
        print(f"[💥 EXCEPTION] {str(e)}")
        
        return {
            "test_name": test_name,
            "description": description,
            "timeout_setting": timeout,
            "status": "exception",
            "is_timeout": False,
            "duration_seconds": duration,
            "exception": str(e)
        }

async def main():
    """Main execution function"""
    print(f"""
╔══════════════════════════════════════════════════════════════╗
║  UVM Test Suite - Batch Execution & Timeout Analysis        ║
║  Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}                              ║
╚══════════════════════════════════════════════════════════════╝
    """)
    
    all_results = []
    
    for test_name, description, timeout in TESTS_TO_RUN:
        result = await run_single_test(test_name, description, timeout)
        all_results.append(result)
        
        # Small delay between tests to allow license cleanup
        await asyncio.sleep(5)
    
    # Generate report
    print(f"\n\n{'='*80}")
    print("BATCH EXECUTION SUMMARY")
    print(f"{'='*80}\n")
    
    success_count = sum(1 for r in all_results if r["status"] == "success")
    timeout_count = sum(1 for r in all_results if r["is_timeout"])
    failed_count = sum(1 for r in all_results if r["status"] not in ["success", "unknown"] and not r["is_timeout"])
    exception_count = sum(1 for r in all_results if r["status"] == "exception")
    
    print(f"Total Tests: {len(all_results)}")
    print(f"✅ Success:   {success_count}")
    print(f"❌ Timeout:   {timeout_count}")
    print(f"❌ Failed:    {failed_count}")
    print(f"💥 Exception: {exception_count}")
    
    print(f"\n{'='*80}")
    print("DETAILED RESULTS")
    print(f"{'='*80}\n")
    
    for i, result in enumerate(all_results, 1):
        status_icon = "✅" if result["status"] == "success" else "⏱️" if result["is_timeout"] else "❌"
        print(f"{i:2d}. {status_icon} {result['test_name']}")
        print(f"    Duration: {result['duration_seconds']:.1f}s / {result['timeout_setting']}s")
        print(f"    Status: {result['status']}")
        if result["is_timeout"]:
            print(f"    ⚠️  TIMEOUT - Test did not complete")
        print()
    
    # Save results to JSON
    output_file = Path("sim/exec/logs/batch_test_results.json")
    output_file.parent.mkdir(parents=True, exist_ok=True)
    
    report_data = {
        "execution_time": datetime.now().isoformat(),
        "summary": {
            "total": len(all_results),
            "success": success_count,
            "timeout": timeout_count,
            "failed": failed_count,
            "exception": exception_count
        },
        "results": all_results
    }
    
    with open(output_file, 'w') as f:
        json.dump(report_data, f, indent=2)
    
    print(f"[INFO] Full results saved to: {output_file}")
    
    # Timeout analysis
    if timeout_count > 0:
        print(f"\n{'='*80}")
        print("TIMEOUT ANALYSIS")
        print(f"{'='*80}\n")
        
        timeout_tests = [r for r in all_results if r["is_timeout"]]
        print(f"Tests with timeout ({len(timeout_tests)}):")
        for r in timeout_tests:
            print(f"  - {r['test_name']}: {r['description']}")
        
        print(f"\n[FINDING] {timeout_count}/{len(all_results)} tests timed out ({timeout_count/len(all_results)*100:.1f}%)")
        
        if timeout_count == len(all_results):
            print("[CRITICAL] ALL tests timed out - systemic issue likely")
        elif timeout_count > len(all_results) / 2:
            print("[WARNING] Majority of tests timeout - common root cause suspected")
        else:
            print("[INFO] Selective timeouts - test-specific issues")

if __name__ == "__main__":
    asyncio.run(main())
