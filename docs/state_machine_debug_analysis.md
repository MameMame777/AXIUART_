# Critical Issue Analysis - AXI4 State Machine Debug
**Date**: October 8, 2025  
**Issue**: cmd=0x20 transitions to READ_DATA instead of WRITE_ADDR  

## Root Cause Analysis

### Command Protocol Verification ✅
- **Write Command**: `0x20` → `cmd[7] = 0` → `rw_bit = 0` → **WRITE** (CORRECT)
- **Read Command**: `0xA0` → `cmd[7] = 1` → `rw_bit = 1` → **READ** (CORRECT)

### State Machine Logic ✅  
```systemverilog
// In CHECK_ALIGNMENT state:
if (!addr_ok) begin
    state_next = ERROR;
end else if (rw_bit) begin  // Read
    state_next = READ_ADDR;
end else begin  // Write  
    state_next = WRITE_ADDR;
end
```
**Logic is CORRECT**: `rw_bit=0` should go to `WRITE_ADDR`

### Observed Issue ❌
- Wave shows: `IDLE` → `READ_DATA` → `IDLE`
- **Missing States**: No `CHECK_ALIGNMENT`, `WRITE_ADDR`, `WRITE_DATA` observed
- **Critical**: State machine appears to skip normal flow

## Hypothesis: start_transaction Signal Issue

### Missing Debug Signals in Current Capture:
1. **start_transaction** - Transaction trigger (CRITICAL)
2. **state[3:0]** - Current state machine state  
3. **cmd[7:0]** - Command byte at capture time
4. **addr[31:0]** - Address at capture time

### Suspected Issues:

#### Issue 1: start_transaction Not Triggering
- State machine may not be receiving `start_transaction=1`
- Without trigger, state remains in IDLE
- Default state may fallback to READ path

#### Issue 2: Command Corruption
- `cmd` register may be corrupted during capture
- `cmd_reg` update may be timing-dependent
- Need to verify `cmd` vs `cmd_reg` values

#### Issue 3: State Machine Reset/Initialization
- State machine may be resetting mid-transaction
- Reset timing could interfere with state transitions

#### Issue 4: Clock Domain Issues
- UART bridge and AXI master may have clock domain crossing issues
- `start_transaction` pulse may be missed

## Debugging Strategy: Add Critical Missing Signals

### Required Additional mark_debug Signals:
```systemverilog
// In Axi4_Lite_Master.sv, add these mark_debug attributes:
(* mark_debug = "true" *) input  logic        start_transaction,  // ALREADY PRESENT
(* mark_debug = "true" *) wire [3:0]          state,             // ADD THIS  
(* mark_debug = "true" *) wire [3:0]          state_next,        // ADD THIS
(* mark_debug = "true" *) input  logic [7:0]  cmd,               // ALREADY PRESENT
(* mark_debug = "true" *) wire [7:0]          cmd_reg,           // ADD THIS
```

### Enhanced ILA Trigger Setup:
1. **Primary Trigger**: `start_transaction` rising edge
2. **Secondary Conditions**: `cmd[7:0] == 0x20` AND `addr[31:0] == 0x1020`  
3. **Pre-trigger**: 200 samples to see setup
4. **Post-trigger**: 2000 samples to see full transaction

### Expected Correct Flow:
```
start_transaction=1 → 
IDLE → CHECK_ALIGNMENT (rw_bit=0) → WRITE_ADDR (awvalid_int=1) → 
WRITE_DATA (wvalid_int=1) → WRITE_RESP → DONE
```

### If start_transaction is the issue:
- Check UART bridge → AXI master interface
- Verify Frame_Parser generates proper transaction trigger
- Check for clock domain crossing issues

## Immediate Action Plan:

1. **Add missing debug signals** to both Axi4_Lite_Master.sv 
2. **Re-compile and re-deploy** FPGA with enhanced debug
3. **Capture new waveform** with start_transaction trigger
4. **Analyze transaction initiation** and state flow

This will definitively identify whether:
- start_transaction is never asserted
- State machine transitions are blocked  
- Command/address corruption occurs
- Clock domain issues exist

The current waveform shows symptoms but lacks the critical signals needed to diagnose the actual trigger failure point.