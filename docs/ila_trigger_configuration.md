## ILA Trigger Configuration for AXI4 Write Debug
## Purpose: Diagnose "Write command transitions to READ state" issue

### Available Debug Signals Summary

#### AXI Master (Axi4_Lite_Master.sv):
- `cmd[7:0]` - Command byte from UART bridge
- `addr[31:0]` - Address from UART bridge  
- `start_transaction` - Transaction start signal
- `rw_bit` - Read/Write bit (CRITICAL)
- `state[3:0]` - State machine state (CRITICAL)
- `awvalid_int` - Write address valid generation (CRITICAL)
- `wvalid_int` - Write data valid generation (CRITICAL)
- `aw_handshake` - Write address handshake
- `w_handshake` - Write data handshake

#### AXI Slave (Register_Block.sv):
- `test_reg_0[31:0]` to `test_reg_3[31:0]` - Target registers
- `write_enable` - Write enable signal
- `write_addr_reg[31:0]` - Write address tracking
- `aw_handshake` - Slave side address handshake
- `w_handshake` - Slave side data handshake  
- `axi_awvalid_debug` - awvalid received by slave
- `axi_wvalid_debug` - wvalid received by slave
- `axi_awaddr_debug[31:0]` - Write address value
- `axi_wdata_debug[31:0]` - Write data value
- `reg_test_write_trigger` - REG_TEST write trigger

---

## Recommended ILA Trigger Scenarios

### Scenario 1: Primary Problem Detection
**Goal**: Capture the moment when write command incorrectly transitions to READ state

**Trigger Setup**:
```
Trigger Mode: BASIC
Trigger Condition: 
  (uart_bridge_instrm_master.start_transaction == 1'b1) AND
  (uart_bridge_instrm_master.cmd == 8'h20) AND
  (uart_bridge_instrm_master.state == 4'd5)    // READ_ADDR state
```

**Key Signals to Monitor**:
- `uart_bridge_instrm_master.start_transaction`
- `uart_bridge_instrm_master.cmd[7:0]`
- `uart_bridge_instrm_master.rw_bit`
- `uart_bridge_instrm_master.state[3:0]`
- `uart_bridge_instrm_master.awvalid_int`
- `uart_bridge_instrm_master.wvalid_int`

**Expected Result**: Should NOT trigger (write commands should not go to READ state)
**If Triggered**: Root problem confirmed - investigate state machine logic

---

### Scenario 2: Start Transaction Analysis
**Goal**: Capture all transaction starts and verify correct state transitions

**Trigger Setup**:
```
Trigger Mode: BASIC
Trigger Condition:
  uart_bridge_instrm_master.start_transaction (Rising Edge)
```

**Key Signals to Monitor**:
- `uart_bridge_instrm_master.start_transaction`
- `uart_bridge_instrm_master.cmd[7:0]`
- `uart_bridge_instrm_master.addr[31:0]`
- `uart_bridge_instrm_master.rw_bit`
- `uart_bridge_instrm_master.state[3:0]`
- `uart_bridge_instrm_master.awvalid_int`
- `uart_bridge_instrm_master.wvalid_int`

**Analysis Points**:
1. Verify `cmd == 0x20` for write commands
2. Verify `rw_bit == 0` for write commands  
3. Track state transitions: IDLE → CHECK_ALIGNMENT → WRITE_ADDR
4. Verify `awvalid_int` and `wvalid_int` generation

---

### Scenario 3: AXI Signal Generation Failure
**Goal**: Detect when start_transaction occurs but AXI signals are not generated

**Trigger Setup**:
```
Trigger Mode: ADVANCED
Trigger Condition:
  (uart_bridge_instrm_master.start_transaction == 1'b1) AND
  (uart_bridge_instrm_master.rw_bit == 1'b0) AND
  (uart_bridge_instrm_master.awvalid_int == 1'b0)
```

**Key Signals to Monitor**:
- All from Scenario 2, plus:
- `uart_bridge_instrm_master.aw_handshake`
- `uart_bridge_instrm_master.w_handshake`

**Analysis**: If this triggers, AXI master is not generating valid signals despite write command

---

### Scenario 4: AXI Master-Slave Communication
**Goal**: Verify AXI signals reach from master to slave

**Trigger Setup**:
```
Trigger Mode: BASIC
Trigger Condition:
  uart_bridge_instrm_master.awvalid_int (Rising Edge)
```

**Key Signals to Monitor**:
- Master side: `awvalid_int`, `wvalid_int`, `aw_handshake`, `w_handshake`
- Slave side: `axi_awvalid_debug`, `axi_wvalid_debug`, `aw_handshake`, `w_handshake`
- Address/Data: `axi_awaddr_debug[31:0]`, `axi_wdata_debug[31:0]`

**Analysis**: Verify master signals properly reach slave

---

### Scenario 5: REG_TEST Write Success Detection  
**Goal**: Confirm when REG_TEST writes actually succeed

**Trigger Setup**:
```
Trigger Mode: BASIC
Trigger Condition:
  register_block_inst.reg_test_write_trigger (Rising Edge)
```

**Key Signals to Monitor**:
- `register_block_inst.reg_test_write_trigger`
- `register_block_inst.write_enable`
- `register_block_inst.axi_awaddr_debug[31:0]`
- `register_block_inst.axi_wdata_debug[31:0]`
- `register_block_inst.test_reg_0[31:0]` to `test_reg_3[31:0]`

**Analysis**: This should trigger on successful REG_TEST writes (currently not happening)

---

## Debugging Sequence Recommendation

### Phase 1: Start with Scenario 2
- Use simple `start_transaction` rising edge trigger
- Capture 5-10 write attempts
- Analyze state machine transitions and signal generation

### Phase 2: If State Machine Issues Found
- Use Scenario 1 to specifically catch incorrect READ state transitions
- Focus on `rw_bit` analysis and command parsing

### Phase 3: If AXI Signal Issues Found  
- Use Scenario 3 to catch missing `awvalid`/`wvalid` generation
- Examine state machine conditions for signal generation

### Phase 4: If Master-Slave Issues Found
- Use Scenario 4 to verify signal propagation
- Check for timing or connectivity issues

### Phase 5: Success Verification
- Use Scenario 5 to confirm when fixes work
- Should see `reg_test_write_trigger` activating

---

## Critical Signal Hierarchy for Analysis

**Priority 1 (Root Cause)**:
- `uart_bridge_instrm_master.rw_bit` (command interpretation)
- `uart_bridge_instrm_master.state[3:0]` (state machine behavior)

**Priority 2 (AXI Generation)**:
- `uart_bridge_instrm_master.awvalid_int`
- `uart_bridge_instrm_master.wvalid_int`

**Priority 3 (Signal Propagation)**:
- `register_block_inst.axi_awvalid_debug`
- `register_block_inst.axi_wvalid_debug`

**Priority 4 (Final Result)**:
- `register_block_inst.reg_test_write_trigger`
- `register_block_inst.test_reg_0[31:0]` (register contents)

This hierarchy guides the debugging process from command interpretation down to final register writes.