# Enhanced Debug Signals Added to Axi4_Lite_Master.sv
**Date**: October 8, 2025  
**Purpose**: Diagnose cmd_reg and state transition decision logic

## Added Debug Signals (Total: 15 Critical Signals)

### Existing Signals (Already Present):
1. `cmd[7:0]` - Command input from UART bridge
2. `addr[31:0]` - Address input from UART bridge
3. `start_transaction` - Transaction trigger signal
4. `cmd_reg[7:0]` - **CRITICAL**: Internal command register
5. `rw_bit` - **CRITICAL**: Read/Write bit extraction
6. `state[3:0]` - Current state machine state
7. `state_next[3:0]` - Next state prediction
8. `awvalid_int` - Write address valid generation
9. `wvalid_int` - Write data valid generation
10. `aw_handshake` - Write address handshake
11. `w_handshake` - Write data handshake

### Newly Added Signals:
12. `cmd_reg_updated` - **NEW**: Flags when cmd_reg is being updated
13. `start_trans_detected` - **NEW**: Direct start_transaction detection
14. `in_idle_state` - **NEW**: IDLE state detection
15. `check_alignment_state` - **NEW**: CHECK_ALIGNMENT state flag
16. `addr_ok_debug` - **NEW**: Address alignment check result
17. `rw_decision_made` - **NEW**: Read/Write decision point flag

## Debug Signal Assignments

### Command Processing Monitoring:
```systemverilog
assign cmd_reg_updated = (start_transaction && (state == IDLE));
assign start_trans_detected = start_transaction;
assign in_idle_state = (state == IDLE);
```

### Critical Decision Point Monitoring:
```systemverilog
assign check_alignment_state = (state == CHECK_ALIGNMENT);
assign addr_ok_debug = addr_ok;
assign rw_decision_made = (state == CHECK_ALIGNMENT) && addr_ok;
```

## Expected ILA Capture Analysis

### Transaction Initiation Phase:
```
Time T: start_trans_detected = 1, in_idle_state = 1
Time T: cmd_reg_updated = 1 (cmd_reg <= cmd should occur)
Time T+1: cmd_reg[7:0] = ? (verify correct value loaded)
Time T+1: rw_bit = cmd_reg[7] (verify correct extraction)
```

### State Transition Decision Phase:
```
Time T+1: check_alignment_state = 1
Time T+1: addr_ok_debug = ? (verify address alignment check)
Time T+1: rw_decision_made = 1 (decision point reached)
Time T+1: rw_bit = ? (critical decision input)
Time T+2: state transitions based on rw_bit value
```

## Analysis Checklist for Next Capture

### Phase 1: Command Registration Verification
- [ ] Verify `start_trans_detected = 1` timing
- [ ] Confirm `cmd_reg_updated = 1` occurs simultaneously
- [ ] Check `cmd_reg[7:0]` receives correct value from `cmd[7:0]`
- [ ] Verify `rw_bit = cmd_reg[7]` extraction timing

### Phase 2: State Machine Decision Verification
- [ ] Confirm `check_alignment_state = 1` transition
- [ ] Verify `addr_ok_debug = 1` (address alignment passes)
- [ ] Check `rw_decision_made = 1` timing
- [ ] Correlate `rw_bit` value with actual state transition

### Phase 3: Logic Contradiction Resolution
- [ ] If `cmd_reg = 0x00` and `rw_bit = 0` but state goes to READ path:
  - Check for logic inversion
  - Verify state enumeration values
  - Look for intermediate state corruption

## Predicted Findings

### Scenario 1: cmd_reg Registration Issue
**If cmd_reg ≠ expected value:**
- Setup/hold timing violation
- Clock domain crossing issue
- Interface connection problem

### Scenario 2: State Machine Logic Error
**If cmd_reg = 0x00, rw_bit = 0 but READ path taken:**
- Logic inversion in state machine
- Incorrect state enumeration
- Combinational logic error

### Scenario 3: Debug Signal Timing Issue
**If signals appear correct but timing is off:**
- Clock skew between debug signals
- Metastability in state transitions
- Race condition in decision logic

This enhanced debug configuration will definitively identify the root cause of the cmd=0x00 → read state contradiction.