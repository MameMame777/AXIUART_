# Protocol and Trigger Analysis
**Date**: October 8, 2025  
**Issue**: ILA trigger not firing - analyzing protocol and test scripts

## Python Script Analysis

### Current Test Scripts:
1. **test_registers_updated.py** - Uses commands 0xA0 (read) and 0x20 (write)
2. **reg_test_working_protocol.py** - Uses same command format

### Command Protocol Verification:

#### Write Command Construction:
```python
# From reg_test_working_protocol.py line 85:
elif cmd == 0x20:  # Write command  
    frame.extend(data)       # Data

# Frame structure:
frame = [0xA5, 0x20, addr[3:0], data[3:0], CRC]
```

#### Read Command Construction:
```python
# From test_registers_updated.py line 101:
response = self.send_command(0xA0, addr)  # Read command

# Frame structure: 
frame = [0xA5, 0xA0, addr[3:0], CRC]
```

## Register_Block.sv Trigger Analysis

### reg_test_write_trigger Definition:
```systemverilog
wire reg_test_write_trigger = write_enable && 
    ((write_addr_reg[11:0] >= 12'h020) && (write_addr_reg[11:0] <= 12'h02C));
```

### Trigger Conditions:
1. **write_enable** must be HIGH
2. **write_addr_reg[11:0]** must be in range 0x020-0x02C
3. Target address 0x1020 → write_addr_reg[11:0] = 0x020 ✓

## Root Cause Analysis

### Issue 1: Write Transaction Not Reaching Register_Block
**Hypothesis**: Write transactions are not reaching the register block, so write_enable never asserts

**Evidence**: 
- Previous waveforms showed awvalid_int = 0 (no AXI write address)
- State machine goes to read path instead of write path
- cmd=0x00 when start_transaction occurs

### Issue 2: Address Mapping Issue
**Hypothesis**: Address 0x1020 not properly mapped to write_addr_reg

**Verification Needed**:
```systemverilog
// Check if 0x1020 maps to write_addr_reg[11:0] = 0x020
// Expected: addr[11:0] = 0x020 for trigger condition
```

### Issue 3: Command Processing Timing
**Hypothesis**: Write command 0x20 not properly processed by Frame_Parser

**Evidence**:
- cmd changes from 0x00 → 0xA0 (read command) in waveforms
- Write command 0x20 never appears in AXI Master interface

## Alternative Trigger Strategies

### Strategy 1: Frame_Parser Activity Trigger
**Target**: UART receive activity
**Signal**: Frame_Parser state machine or UART RX activity
**Advantage**: Captures command processing before AXI interface

### Strategy 2: AXI Interface Activity Trigger  
**Signals**: Any AXI transaction (read or write)
**Condition**: 
```tcl
(uart_bridge_instrm_master/awvalid_int == 1'b1) OR
(uart_bridge_instrm_master/arvalid_int == 1'b1)
```

### Strategy 3: Command Reception Trigger
**Signal**: Frame_Parser command output
**Advantage**: Captures command processing regardless of type

### Strategy 4: Always Running Capture
**Method**: Start ILA, run test script, manually stop
**Advantage**: Guaranteed to capture activity
**Settings**: Large sample buffer (4096+ samples)

## Debugging Protocol Flow

### Test Sequence Verification:
1. **PC sends**: `A5 20 20 10 00 00 [DATA] [CRC]` (write to 0x1020)
2. **Frame_Parser should**: Parse command 0x20 as write
3. **AXI Master should**: Generate write transaction to 0x1020
4. **Register_Block should**: Assert write_enable with addr=0x020
5. **Trigger should**: Fire on reg_test_write_trigger

### Current Failure Point:
Based on previous analysis, failure occurs at step 2-3:
- Frame_Parser may be misprocessing command 0x20
- AXI Master receives cmd=0x00 instead of cmd=0x20
- No write transaction generated → no trigger

## Recommended Investigation Steps:

### Step 1: Verify Frame_Parser Output
Add Frame_Parser debug signals:
- cmd_out to AXI Master
- frame_valid 
- start_transaction generation

### Step 2: Use Upstream Trigger
Try triggering on UART RX activity or Frame_Parser state machine

### Step 3: Protocol Verification Test
Send known working read command (0xA0) first to verify basic connectivity

### Step 4: Manual Trigger Test
Use always-running capture to verify system is processing commands

The core issue appears to be that write commands are not properly reaching the register block, preventing the trigger from firing.