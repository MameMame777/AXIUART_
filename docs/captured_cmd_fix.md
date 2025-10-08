# CRITICAL BUG FIX - captured_cmd Fixed Value Issue
**Date**: October 8, 2025  
**Issue**: uart_bridge_inst/axi_master/cmd stuck at 0xA0
**Root Cause**: captured_cmd update condition too restrictive

## Problem Analysis

### Observed Behavior:
- **Reset state**: cmd = 0x00 ✅ (correct)
- **Runtime**: cmd = 0xA0 (fixed) ❌ (stuck value)

### Root Cause Identified:
```systemverilog
// BEFORE (Line 333): Too restrictive condition
if (parser_frame_valid && (main_state == MAIN_IDLE)) begin
    captured_cmd <= parser_cmd;
end
```

**Issue**: 
1. First frame (read 0xA0) captures correctly when main_state == MAIN_IDLE
2. Subsequent frames cannot update captured_cmd because main_state is not MAIN_IDLE
3. captured_cmd remains stuck at 0xA0 regardless of actual commands sent

## Fix Applied

### Modified Code:
```systemverilog
// AFTER (Line 333): Allow capture during state transitions
if (parser_frame_valid && ((main_state == MAIN_IDLE) || (main_state_next == MAIN_IDLE))) begin
    captured_cmd <= parser_cmd;
end
```

### Fix Logic:
- **Original**: Only capture when currently in MAIN_IDLE
- **Fixed**: Capture when currently in MAIN_IDLE OR transitioning to MAIN_IDLE
- **Result**: New frames can update captured_cmd during state transitions

## Expected Behavior After Fix

### Write Command Sequence:
1. **Frame 1**: Read command 0xA0 → captured_cmd = 0xA0
2. **Frame 2**: Write command 0x20 → captured_cmd = 0x20 (now updates correctly)
3. **AXI Master**: Receives cmd = 0x20 → rw_bit = 0 → WRITE_ADDR state
4. **Result**: Register write occurs successfully

### Key Benefits:
- ✅ captured_cmd updates for each new frame
- ✅ Write commands (0x20) properly processed
- ✅ State machine receives correct command values
- ✅ Read/Write decision based on actual command

## Test Verification Required

### Test Sequence:
1. **Send read command** → Verify cmd updates to 0xA0
2. **Send write command** → Verify cmd updates to 0x20
3. **Verify state machine** → Should go to WRITE_ADDR for cmd=0x20
4. **Verify register write** → REG_TEST_0 should contain written value

This fix addresses the fundamental issue preventing write commands from being processed correctly by the AXI master state machine.