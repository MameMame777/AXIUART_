# Critical Frame Valid Analysis - October 13, 2025

## Problem Summary
- Frame_consumed pulse detected at 1724250000
- frame_valid_hold cleared at 1724270000 
- Fatal assertion failure immediately after frame_valid_hold clear
- Error: Frame valid should only be '1' in VALIDATE state

## Root Cause Analysis

### Timing Analysis
```
1724250000: [FP_DIAG] FRAME_CONSUMED PULSE: frame_valid_hold=1, state=8
1724250000: [DEBUG_FRAME_CONSUMED] FRAME_CONSUMED PULSE: frame_valid=1, bridge_state=3
1724270000: [FP_DIAG] STATE TRANSITION: 8 -> 0  
1724270000: [FP_DIAG] FRAME_VALID_HOLD CHANGED: 1 -> 0, state=0
1724270000: FATAL: Frame valid should only be '1' in VALIDATE state
```

### Critical Issue Identified
1. **State Transition**: State 8 (VALIDATE) -> State 0 (IDLE)
2. **frame_valid_hold**: Clears when transitioning to IDLE
3. **frame_valid assignment**: Still '1' when state=IDLE
4. **Assertion violation**: frame_valid='1' in IDLE state (not VALIDATE)

## Root Cause: frame_valid Logic Error

The frame_valid assignment logic is incorrect:
```systemverilog
assign frame_valid = frame_valid_hold && (state == VALIDATE);
```

But the actual implementation might be:
```systemverilog  
assign frame_valid = frame_valid_hold;  // WRONG - missing state check
```

## Required Fix
Ensure frame_valid is ONLY active when:
1. frame_valid_hold == 1'b1 
2. state == VALIDATE
3. No other state should have frame_valid='1'

## Implementation Strategy
1. Fix frame_valid assignment with proper state checking
2. Ensure state machine transitions properly clear frame_valid
3. Add assertion to verify frame_valid only in VALIDATE state