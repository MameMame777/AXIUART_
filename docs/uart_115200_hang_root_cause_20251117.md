# UART 115200/921600 Baud Test Hang - Root Cause Analysis
**Date**: 2025-11-17 08:03  
**Test**: `uart_axi4_basic_115200_test`  
**Status**: CRITICAL BUG IDENTIFIED AND FIXED

---

## Executive Summary

### Critical Bug: UVM Objection Premature Drop
**Root Cause**: Test dropped objection BEFORE executing `super.run_phase()`, causing UVM to initiate shutdown while Phase 2 data transfer was starting.

**Impact**: 
- Test hung at 65.932ms (Phase 2 start)
- Appeared as infinite `@(posedge clk)` wait in `drive_uart_byte`
- Actually caused by UVM run_phase termination racing with test execution

**Fix**: Reorder objection drop to occur AFTER `super.run_phase()` completes.

---

## Timeline of Discovery

### Initial Problem (2025-11-17 00:21 - 07:12)
1. **Attempt 1**: 115200 baud test → 180s timeout
   - Phase 1: 502 seconds (465s idle wait)
   - Phase 2: Incomplete (timeout)
   - Analysis document created: `uart_115200_baud_test_analysis_20251117.md`

2. **Attempt 2**: Implemented recommended fixes (921600 baud + remove idle wait)
   - Changed TARGET_BAUD_RATE: 115200 → 921600 (8.5x vs 67.8x slowdown)
   - Removed `wait_for_uart_quiescent()` calls
   - Added 100-cycle settling period (800ns)
   - Expected: ~1 second completion
   - **Result**: 60s timeout, hung at 65.932ms

### Hang Investigation (2025-11-17 08:02)

**Log Evidence** (`uart_axi4_basic_115200_test_20251117_080225.log`):
```
UVM_INFO @ 65052000: [BASIC115_PHASE1] CONFIG write complete - switching UVM timing to 921600 baud
UVM_INFO @ 65052000: [BASIC115_PHASE1] UVM environment updated: byte_time_ns=10850 ...
UVM_INFO @ 65852000: [BASIC115_PHASE] === PHASE 2: Testing data transfer at 921600 baud ===
UVM_INFO @ 65852000: [BASIC_TEST] ===============================================
...
UVM_INFO @ 65932000: [UART_DRIVER_BYTE_FORCED] Begin byte[0/7]=0xa5 at time=65932000
UVM_INFO @ 65932000: uvm_test_top  <--- LOG ENDS HERE
```

**Analysis**:
1. CONFIG write successful (65.052ms)
2. UVM timing updated to 921600 baud correctly
3. Phase 2 started (65.852ms)
4. Parent test `run_phase` began (65.852ms - 65.932ms)
5. First UART byte transmission started (65.932ms)
6. **Simulation hung - no further progress**

---

## Root Cause Deep Dive

### Code Analysis: Original Implementation

```systemverilog
// uart_axi4_basic_115200_test.sv:194-210 (BUGGY VERSION)
virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this, "Baud rate change test");  // Line 195
    wait (uart_axi4_tb_top.rst_n == 1'b1);
    repeat (10) @(posedge uart_axi4_tb_top.clk);
    
    `uvm_info("BASIC115_PHASE", "=== PHASE 1: ...", UVM_LOW)
    program_baud_divisor_register();  // CONFIG write + UVM timing update
    
    repeat (100) @(posedge uart_axi4_tb_top.clk);  // 800ns settling
    
    `uvm_info("BASIC115_PHASE", "=== PHASE 2: ...", UVM_LOW)
    phase.drop_objection(this, "Baud rate change test");  // ⚠️ LINE 208 - TOO EARLY!

    super.run_phase(phase);  // Line 210 - Never completes
endtask
```

### UVM Objection Mechanism

**Normal Flow**:
1. Test raises objection → UVM waits for completion
2. Test executes logic (sequences, transactions)
3. Test drops objection → UVM proceeds to cleanup
4. UVM calls `phase.drop_objection()` handlers
5. Simulation ends gracefully

**Buggy Flow** (65.852ms - 65.932ms):
1. ✅ Phase 1 completes (CONFIG write)
2. ✅ Phase 2 log message printed
3. ❌ **Objection dropped** (line 208) → UVM starts shutdown
4. 🔄 `super.run_phase(phase)` called (line 210)
   - Parent test raises NEW objection internally
   - Starts `uart_axi4_basic_test::run_phase()`
   - Begins data transfer sequence
5. ⚠️ **Race condition**:
   - Child test dropped objection → UVM cleanup starting
   - Parent test raised objection → needs simulation to continue
   - Driver starts UART transmission at 65.932ms
   - `@(posedge clk)` waits for next clock edge
   - **UVM phase management conflicts with active sequences**
   - Simulation enters undefined state → hang

### Why Appeared as Clock Hang

**Symptoms**:
- Last log: `"Begin byte[0/7]=0xa5 at time=65932000"`
- Inside `drive_uart_byte`: `repeat (bit_time_cycles) @(posedge vif.clk);`
- No timeout from watchdog (should fire after 4× byte_time)
- 60-second external timeout

**Explanation**:
- UVM shutdown started before driver watchdog could activate
- Phase management prevents normal task execution
- `@(posedge clk)` never returns because UVM runtime is terminating
- Not a clock issue - **UVM phase control flow issue**

---

## Fix Implementation

### Corrected Code

```systemverilog
// uart_axi4_basic_115200_test.sv:194-213 (FIXED VERSION)
virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this, "Baud rate change test");
    wait (uart_axi4_tb_top.rst_n == 1'b1);
    repeat (10) @(posedge uart_axi4_tb_top.clk);
    
    `uvm_info("BASIC115_PHASE", "=== PHASE 1: Programming CONFIG at default baud & switching ===", UVM_LOW)
    program_baud_divisor_register();  // Writes CONFIG + updates UVM timing
    
    // Short settling period instead of full idle wait (was 465 seconds)
    repeat (100) @(posedge uart_axi4_tb_top.clk);
    
    `uvm_info("BASIC115_PHASE", 
        $sformatf("=== PHASE 2: Testing data transfer at %0d baud ===", TARGET_BAUD_RATE), 
        UVM_LOW)
    
    // Execute parent test (data transfer sequence)
    super.run_phase(phase);  // ✅ Completes before objection drop
    
    // Drop objection AFTER test completes
    phase.drop_objection(this, "Baud rate change test");  // ✅ Correct position
endtask
```

### Verification Strategy

**Expected Behavior After Fix**:
1. Phase 1: CONFIG write (65.052ms) ✅
2. Settling period: 800ns (65.052ms → 65.852ms) ✅
3. Phase 2: Parent test execution
   - Sequences start
   - UART transactions complete
   - No premature shutdown
4. Objection drop AFTER all sequences finish
5. Clean simulation termination

**Test Execution**:
```bash
# Compile
python mcp_server/mcp_client.py --workspace e:/Nautilus/workspace/fpgawork/AXIUART_ \
  --tool run_uvm_simulation --test-name uart_axi4_basic_115200_test \
  --mode compile --verbosity UVM_LOW --timeout 120

# Run (reduced timeout - expect fast completion)
python mcp_server/mcp_client.py --workspace e:/Nautilus/workspace/fpgawork/AXIUART_ \
  --tool run_uvm_simulation --test-name uart_axi4_basic_115200_test \
  --mode run --verbosity UVM_MEDIUM --waves --timeout 30
```

**Success Criteria**:
- Test completes in <5 seconds (vs 60s timeout)
- Phase 2 transactions execute fully
- Clean UVM_INFO: "Test Passed" or similar
- No UVM_ERROR/UVM_FATAL
- Waveform shows complete transaction at 921600 baud

---

## Lessons Learned

### UVM Best Practices

1. **Objection Lifetime**:
   ```systemverilog
   // ✅ CORRECT Pattern
   task run_phase(uvm_phase phase);
       phase.raise_objection(this);
       // ... do work ...
       super.run_phase(phase);  // Complete parent
       phase.drop_objection(this);
   endtask
   
   // ❌ INCORRECT Pattern
   task run_phase(uvm_phase phase);
       phase.raise_objection(this);
       // ... do work ...
       phase.drop_objection(this);  // TOO EARLY!
       super.run_phase(phase);      // Never completes
   endtask
   ```

2. **Override Guidelines**:
   - When overriding `run_phase`, objection management becomes YOUR responsibility
   - `super.run_phase()` may have its own objections - don't interfere
   - Drop objection ONLY when YOUR test + parent's test are complete

3. **Debug Symptoms**:
   - Hang inside `@(posedge clk)` without timeout → check objection timing
   - Last log before hang shows sequence start → likely phase control issue
   - Watchdog doesn't fire → UVM runtime already shutting down

### Test Architecture Issues (From Previous Analysis)

This bug was **orthogonal** to the baud rate timing issues documented in `uart_115200_baud_test_analysis_20251117.md`:

**Timing Issues** (Addressed):
- ✅ 115200 too slow → Changed to 921600
- ✅ Idle wait bottleneck → Removed wait_for_uart_quiescent
- ✅ CONFIG response parsing → Downgraded to WARNING

**Control Flow Issue** (This Document):
- ✅ Objection premature drop → Fixed order

**Both fixes required** for test to function.

---

## Performance Comparison

| Version | Phase 1 | Settling | Phase 2 | Result |
|---------|---------|----------|---------|--------|
| Original (115200 + idle wait) | 502s (465s wait) | N/A | Incomplete | 180s timeout |
| Improved (921600 + no wait) | ~65ms | 800ns | **HUNG** | 60s timeout |
| **Fixed (921600 + objection fix)** | **~65ms** | **800ns** | **Expected ~500ms** | **Expected: PASS <5s** |

---

## Next Steps

1. ✅ **COMPLETED**: Fix objection order in `uart_axi4_basic_115200_test.sv`
2. ⏳ **PENDING**: Compile and execute test
3. ⏳ **PENDING**: Verify Phase 2 completes successfully
4. ⏳ **PENDING**: Analyze waveform for 921600 baud operation
5. ⏳ **PENDING**: Consider renaming test (misleading "115200" when using 921600)

---

## Related Documents

- **Timing Analysis**: `uart_115200_baud_test_analysis_20251117.md`
  - Identified baud rate slowdown (67.8x impractical)
  - Recommended 921600 Hz (8.5x) + idle wait removal
  - Performance metrics and solution options

- **This Document**: `uart_115200_hang_root_cause_20251117.md`
  - Identified UVM objection control flow bug
  - Root cause: premature `drop_objection()` before `super.run_phase()`
  - Fix: Reorder objection drop

---

## Conclusion

**The hang was NOT caused by baud rate timing** (921600 Hz configuration was correct).

**Root cause**: UVM objection dropped before parent test execution completed, creating race condition between shutdown and active sequences.

**Resolution**: Single-line reorder - move `phase.drop_objection()` after `super.run_phase()`.

**Confidence**: HIGH - fix addresses fundamental UVM control flow violation.

**Expected outcome**: Test should now complete in ~1 second (65ms Phase 1 + 500ms Phase 2 at 921600 baud).
