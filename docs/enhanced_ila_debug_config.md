# Enhanced ILA Debug Configuration
**Target**: Diagnose start_transaction and state machine flow  
**Date**: October 8, 2025

## Required ILA Configuration

### Enhanced Debug Signals (Total: 12 Critical Signals)

#### Transaction Control Signals:
1. `uart_bridge_instrm_master/start_transaction` - **CRITICAL**: Transaction trigger
2. `uart_bridge_instrm_master/transaction_done` - Transaction completion
3. `uart_bridge_instrm_master/cmd[7:0]` - Command from UART bridge
4. `uart_bridge_instrm_master/cmd_reg[7:0]` - **NEW**: Stored command in state machine

#### State Machine Analysis:
5. `uart_bridge_instrm_master/state[3:0]` - Current state machine state  
6. `uart_bridge_instrm_master/state_next[3:0]` - Next state prediction
7. `uart_bridge_instrm_master/rw_bit` - Read/Write bit interpretation

#### AXI Signal Generation:
8. `uart_bridge_instrm_master/awvalid_int` - Write address valid generation
9. `uart_bridge_instrm_master/wvalid_int` - Write data valid generation  
10. `uart_bridge_instrm_master/aw_handshake` - Write address handshake
11. `uart_bridge_instrm_master/w_handshake` - Write data handshake

#### Address/Data Context:
12. `uart_bridge_instrm_master/addr[31:0]` - Address from UART bridge

### ILA Trigger Strategy

#### Primary Trigger Configuration:
```tcl
# Trigger on write command reception
set_property trigger_condition {
    uart_bridge_instrm_master/cmd[7:0] == 8'h20 AND
    uart_bridge_instrm_master/addr[31:0] == 32'h00001020
} [get_debug_cores]

# Alternative: Trigger on start_transaction
set_property trigger_condition {
    uart_bridge_instrm_master/start_transaction == 1'b1
} [get_debug_cores]
```

#### Capture Configuration:
- **Pre-trigger**: 300 samples (see command setup)
- **Post-trigger**: 2000 samples (full transaction analysis)
- **Trigger Position**: 20% (capture setup phase)

### Expected Debugging Scenarios

#### Scenario 1: start_transaction Never Asserted
**Symptoms**: 
- `start_transaction` remains 0 throughout capture
- `state` stays in IDLE
- No state transitions observed

**Root Cause**: UART bridge → AXI master interface broken

#### Scenario 2: Command Corruption
**Symptoms**:
- `cmd[7:0] = 0x20` but `cmd_reg[7:0] ≠ 0x20`  
- `rw_bit` incorrect value
- State machine uses corrupted command

**Root Cause**: Command registration timing issue

#### Scenario 3: State Machine Blocked
**Symptoms**:
- `start_transaction = 1` observed
- `cmd_reg = 0x20`, `rw_bit = 0` correct  
- `state` transitions incorrectly or gets stuck

**Root Cause**: State machine logic error or reset interference

#### Scenario 4: Clock Domain Crossing
**Symptoms**:
- `start_transaction` pulse too short to be captured
- Metastability in control signals
- Inconsistent state transitions

**Root Cause**: Clock domain synchronization failure

### Analysis Checklist

#### Phase 1: Transaction Initiation
- [ ] Verify `start_transaction` assertion timing
- [ ] Check `cmd[7:0]` value at transaction start
- [ ] Confirm `addr[31:0]` setup before transaction

#### Phase 2: Command Processing  
- [ ] Verify `cmd_reg` stores correct value
- [ ] Check `rw_bit` extraction timing
- [ ] Confirm state transition from IDLE

#### Phase 3: State Machine Flow
- [ ] Trace state sequence: IDLE → CHECK_ALIGNMENT → WRITE_ADDR
- [ ] Verify state transition conditions
- [ ] Check for unexpected ERROR or reset states

#### Phase 4: AXI Signal Generation
- [ ] Confirm `awvalid_int = 1` in WRITE_ADDR state
- [ ] Verify `wvalid_int = 1` in WRITE_DATA state  
- [ ] Check handshake signal timing

### Critical Timing Relationships

```
Time 0:    cmd=0x20, addr=0x1020 setup
Time 1:    start_transaction = 1 (rising edge)
Time 2:    cmd_reg <= 0x20, state <= CHECK_ALIGNMENT  
Time 3:    rw_bit = 0, state <= WRITE_ADDR
Time 4:    awvalid_int = 1
Time 5+:   aw_handshake when awready asserted
```

This enhanced configuration will definitively identify the root cause of the state machine bypass issue.