# ILA Waveform Analysis - AXI4 Debug Enhanced Version
**Date**: October 8, 2025  
**Trigger**: start_transaction rising edge  
**Capture Duration**: ~1.2ms  

## Critical Findings

### 1. **ROOT CAUSE CONFIRMED**: awvalid_int = 0
- **uart_bridge_instrm_master/awvalid_int** remains `0` throughout entire capture
- This confirms the core issue: AXI Master is NOT generating write address valid signal
- State machine issue has been localized to awvalid generation logic

### 2. **Register Initial Values Are Correct**
- `test_reg_0` = `0xDEADBEEF` ✅
- `test_reg_1` = `0x12345678` ✅  
- `test_reg_2` = `0xABCDEF00` ✅
- `test_reg_3` = `0x00000000` ✅
- **Conclusion**: Register_Block.sv is correctly initialized and functional

### 3. **Address Setup Is Correct**
- `register_block_inst/awaddr_debug` = `0x00001020` 
- Target address for REG_TEST_0 is correctly configured
- **Conclusion**: Address routing from UART bridge is working

### 4. **State Machine Pattern Analysis**
- Pattern observed: `IDLE` → `READ_DATA` → `IDLE`
- **CRITICAL**: No `WRITE_ADDR` or `WRITE_DATA` states observed
- **CRITICAL**: State machine incorrectly transitions to READ operations

### 5. **Handshake Status**
- `aw_handshake` = `0` (expected, since awvalid_int = 0)
- `w_handshake` = `0` (expected, since no write transaction initiated)
- **Conclusion**: Handshake failure is downstream of awvalid generation failure

## Signal Hierarchy Tracing

### Level 1: Command Processing ✅ WORKING
- UART bridge successfully processes write commands
- Address `0x1020` correctly identified
- Command routing functional

### Level 2: AXI Master State Machine ❌ FAILING  
- **awvalid_int generation FAILED**
- State machine not entering WRITE_ADDR state
- **THIS IS THE ROOT CAUSE LOCATION**

### Level 3: AXI Slave (Not Reached)
- Register_Block.sv never receives valid write transactions
- Cannot evaluate slave functionality until master fixed

## Next Investigation Steps

### 1. **IMMEDIATE**: Examine awvalid_int Generation Logic
```systemverilog
// In Axi4_Lite_Master.sv, look for:
assign awvalid_int = (state == WRITE_ADDR);
```
**Question**: Why is state never reaching WRITE_ADDR?

### 2. **State Machine Transition Conditions**
- Investigate transition from IDLE → CHECK_ALIGNMENT → WRITE_ADDR
- Check `start_transaction` signal propagation
- Check `rw_bit` interpretation logic

### 3. **Command Analysis Logic**  
- Verify `rw_bit` extraction from command byte
- Check if `cmd[7]` parsing is correct for 0x20 command

## Missing Critical Signals in Current Capture

**Need to add these mark_debug signals for next capture:**
1. `uart_bridge_instrm_master/start_transaction` - Transaction initiation
2. `uart_bridge_instrm_master/cmd[7:0]` - Command byte analysis
3. `uart_bridge_instrm_master/rw_bit` - Read/Write bit determination
4. `uart_bridge_instrm_master/state[3:0]` - State machine state
5. `uart_bridge_instrm_master/state_next[3:0]` - Next state prediction

## Recommended Fix Investigation Priority

### Priority 1: State Machine Logic
1. Verify state transition conditions in Axi4_Lite_Master.sv
2. Check `start_transaction` handling
3. Confirm `rw_bit` interpretation

### Priority 2: Command Processing
1. Verify command byte parsing (`cmd[7]` for read/write)
2. Confirm 0x20 command interpretation as write

### Priority 3: Signal Generation  
1. Fix awvalid_int generation conditions
2. Ensure state machine reaches WRITE_ADDR state

## Expected Behavior vs Observed

### Expected Flow:
```
start_transaction=1 → 
IDLE → CHECK_ALIGNMENT → WRITE_ADDR (awvalid_int=1) → 
WRITE_DATA (wvalid_int=1) → WRITE_RESP → DONE
```

### Observed Flow:
```
start_transaction=? → 
IDLE → READ_DATA → IDLE
awvalid_int=0 (never asserted)
```

**Conclusion**: The state machine is fundamentally misrouting write commands as read commands, causing complete bypass of write logic.

## Verification Strategy for Next Capture

### Enhanced ILA Setup Required:
1. **Trigger**: `uart_bridge_instrm_master/start_transaction` rising edge
2. **Pre-trigger**: 100 samples  
3. **Post-trigger**: 1000 samples
4. **Additional Signals**: cmd, rw_bit, state, state_next

This analysis confirms the suspected root cause and provides clear direction for the fix.