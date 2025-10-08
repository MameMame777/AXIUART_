# Alternative ILA Trigger Strategy
**Date**: October 8, 2025  
**Issue**: start_trans_detected did not trigger - need alternative trigger approach

## Alternative Trigger Options

### Option 1: Register Test Write Trigger (Recommended)
**Signal**: `register_block_inst/reg_test_write_trigger`
**Advantage**: Already confirmed active in previous captures
**Setup**:
```tcl
set_property trigger_condition {
    register_block_inst/reg_test_write_trigger == 1'b1
} [get_debug_cores]
```
**Expected**: Should capture complete transaction sequence

### Option 2: State Machine Transition Trigger
**Signal**: `uart_bridge_instrm_master/state[3:0]`
**Condition**: Transition from IDLE (0) to any other state
**Setup**:
```tcl
set_property trigger_condition {
    uart_bridge_instrm_master/state[3:0] != 4'h0
} [get_debug_cores]
```
**Advantage**: Captures state machine activity regardless of start_transaction

### Option 3: Command Change Trigger
**Signal**: `uart_bridge_instrm_master/cmd[7:0]`
**Condition**: Change from 0x00 to any other value
**Setup**:
```tcl
set_property trigger_condition {
    uart_bridge_instrm_master/cmd[7:0] != 8'h00
} [get_debug_cores]
```
**Advantage**: Captures command processing activity

### Option 4: Multiple Signal Combination Trigger
**Signals**: Combination of multiple indicators
**Setup**:
```tcl
set_property trigger_condition {
    (register_block_inst/reg_test_write_trigger == 1'b1) OR
    (uart_bridge_instrm_master/state[3:0] != 4'h0) OR  
    (uart_bridge_instrm_master/cmd[7:0] != 8'h00)
} [get_debug_cores]
```
**Advantage**: Multiple trigger opportunities

### Option 5: Always Running Capture
**Method**: Continuous capture with manual stop
**Setup**: Start ILA without specific trigger, let it run, then manually stop after sending test command
**Advantage**: Guaranteed to capture all activity
**Disadvantage**: Need to find relevant data in large capture

## Recommended Approach: Option 1 + Enhanced Pre-trigger

### Primary Setup:
- **Trigger**: `register_block_inst/reg_test_write_trigger == 1'b1`
- **Pre-trigger**: 500 samples (capture setup phase)
- **Post-trigger**: 1000 samples (capture complete transaction)
- **Position**: 33% (more pre-trigger data)

### Enhanced Signal List (17 signals):
1. `register_block_inst/reg_test_write_trigger` (trigger signal)
2. `uart_bridge_instrm_master/start_transaction`
3. `uart_bridge_instrm_master/start_trans_detected` (our new signal)
4. `uart_bridge_instrm_master/cmd[7:0]`
5. `uart_bridge_instrm_master/cmd_reg[7:0]` (critical)
6. `uart_bridge_instrm_master/rw_bit` (critical)
7. `uart_bridge_instrm_master/state[3:0]`
8. `uart_bridge_instrm_master/state_next[3:0]`
9. `uart_bridge_instrm_master/in_idle_state`
10. `uart_bridge_instrm_master/check_alignment_state`
11. `uart_bridge_instrm_master/cmd_reg_updated`
12. `uart_bridge_instrm_master/rw_decision_made`
13. `uart_bridge_instrm_master/addr_ok_debug`
14. `uart_bridge_instrm_master/awvalid_int`
15. `uart_bridge_instrm_master/wvalid_int`
16. `uart_bridge_instrm_master/aw_handshake`
17. `uart_bridge_instrm_master/w_handshake`

## Why start_trans_detected Might Not Trigger

### Possible Reasons:
1. **Signal Name Mismatch**: ILA doesn't see the new signal
2. **Compilation Issue**: New signals not properly synthesized
3. **Timing Issue**: Signal pulse too narrow to be captured
4. **Connection Issue**: Signal not connected to ILA core

### Verification Steps:
1. Check ILA signal list in Vivado to confirm new signals are present
2. Verify signal appears in netlist after synthesis
3. Use simpler, known-working trigger first

## Immediate Action Plan:

### Step 1: Use reg_test_write_trigger (Proven)
- This signal is confirmed active from previous captures
- Should reliably trigger when test command is sent

### Step 2: Verify New Debug Signals
- Check if cmd_reg, rw_bit, and other new signals appear in capture
- If not visible, may need to re-synthesize design

### Step 3: Analyze Complete Transaction
- Focus on cmd_reg vs cmd timing
- Verify rw_bit calculation
- Trace complete state machine sequence

### Step 4: Fallback Options
- If Option 1 fails, try Option 2 (state transition)
- If all specific triggers fail, use Option 5 (always running)

The reg_test_write_trigger is our most reliable option since it's already proven to work in your test environment.