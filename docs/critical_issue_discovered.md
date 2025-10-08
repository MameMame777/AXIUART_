# CRITICAL ISSUE DISCOVERED - Root Cause Analysis
**Date**: October 8, 2025  
**Issue**: start_transaction never asserted - AXI Master not triggered

## Root Cause Confirmed: start_transaction = 0

### Wave Analysis Results

#### Signal Observations:
- **start_transaction** (Signal #19): **REMAINS 0 throughout capture**
- **cmd[7:0]** (Signal #21): Changes from `0x00` to `0xA0` 
- **state[3:0]** (Signal #17): `IDLE` → `READ_DATA` → `IDLE`
- **register_block_inst/reg_test_write_trigger**: `1` (trigger signal active)

### Critical Discovery

**THE FUNDAMENTAL PROBLEM**: 
- AXI Master state machine is **NEVER TRIGGERED**
- `start_transaction` signal **NEVER ASSERTS** (`= 0` constantly)
- Without `start_transaction=1`, AXI Master remains in IDLE state
- State transitions to `READ_DATA` are **NOT from AXI Master state machine**

### Signal Analysis

#### Command Processing:
- `cmd[7:0]` shows: `0x00` → `0xA0`
- **0xA0** = `0b1010_0000` = Read command (cmd[7]=1)
- **Missing**: Write command `0x20` should appear

#### State Machine Behavior:
- AXI Master `state` shows transitions but **without start_transaction trigger**
- This suggests **different state machine** is transitioning
- Likely Frame_Parser or Frame_Builder state machine in READ mode

#### Address Configuration:
- `register_block_inst/awaddr_debug[31:0]` = `0x00001020` (correct)
- Address setup exists but **no AXI transaction initiated**

## Root Cause Chain Analysis

### Level 1: UART Communication ✅ WORKING
- UART bridge receives data correctly
- Protocol parsing appears functional
- Command bytes reach system

### Level 2: Command Interpretation ❌ FAILING  
- **Expected**: Write command `0x20`
- **Observed**: Read command `0xA0`
- **Issue**: Command misinterpretation in Frame_Parser

### Level 3: AXI Master Interface ❌ NOT REACHED
- `start_transaction` never asserted
- AXI Master never activated
- No write transactions generated

## Suspected Issues

### Issue 1: Frame_Parser Command Processing
**Hypothesis**: Frame_Parser misinterprets write commands as read commands
- Input: `0x20` (write)
- Processing: Converted to `0xA0` (read)
- Output: Wrong command to AXI Master

### Issue 2: start_transaction Generation Logic
**Hypothesis**: Condition for `start_transaction` assertion never met
- Write command path broken in Frame_Parser
- Only read commands trigger AXI Master
- Write path bypassed or corrupted

### Issue 3: Protocol State Machine Error
**Hypothesis**: Frame_Parser state machine has fundamental logic error
- Write commands processed differently than expected
- State transitions force read mode
- Command echo/response logic interfering

## Immediate Investigation Required

### Priority 1: Frame_Parser Command Analysis
```systemverilog
// Need to examine Frame_Parser.sv:
// 1. How does it process cmd=0x20?
// 2. When does it assert start_transaction?
// 3. What command does it send to AXI Master?
```

### Priority 2: Interface Connection Verification
```systemverilog
// Verify connection between Frame_Parser and AXI Master:
// Frame_Parser.start_transaction_out → Axi4_Lite_Master.start_transaction
// Frame_Parser.cmd_out → Axi4_Lite_Master.cmd
```

### Priority 3: Write vs Read Path Differentiation
- Trace complete write command path through Frame_Parser
- Identify where `0x20` becomes `0xA0`
- Find missing write logic or incorrect branching

## Expected vs Observed Behavior

### Expected Write Flow:
```
PC sends: A5 20 20 10 00 00 [DATA] [CRC]
Frame_Parser: cmd=0x20 → start_transaction=1 → AXI Write
AXI Master: IDLE → CHECK_ALIGNMENT → WRITE_ADDR → WRITE_DATA
Result: Register updated
```

### Observed Flow:
```
PC sends: A5 20 20 10 00 00 [DATA] [CRC]  
Frame_Parser: cmd=0x20 → ??? → cmd=0xA0 → start_transaction=0
AXI Master: Remains in IDLE (never triggered)
Something else: State transitions to READ mode
Result: No register update, test pattern generator active
```

## Next Investigation Steps

1. **Examine Frame_Parser.sv**: Focus on write command processing logic
2. **Trace start_transaction generation**: Find conditions for assertion
3. **Identify command transformation**: Where 0x20 becomes 0xA0
4. **Interface verification**: Confirm signal connections

This analysis definitively shows the issue is **upstream** of AXI Master in the Frame_Parser command processing logic.