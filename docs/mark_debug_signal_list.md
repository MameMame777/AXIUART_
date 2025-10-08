# Mark Debug Signal List for FPGA Hardware Verification

## Overview
Added `mark_debug` attributes to critical signals in `Register_Block.sv` for hardware verification of register write operations.

## Debug Signals Added

### Test Registers (Primary Verification Target)
```systemverilog
(* mark_debug = "true" *) logic [31:0] test_reg_0;  // RW - Test register 0
(* mark_debug = "true" *) logic [31:0] test_reg_1;  // RW - Test register 1  
(* mark_debug = "true" *) logic [31:0] test_reg_2;  // RW - Test register 2
(* mark_debug = "true" *) logic [31:0] test_reg_3;  // RW - Test register 3
```

### Internal Control Signals
```systemverilog
(* mark_debug = "true" *) logic [11:0] addr_offset;      // Address offset calculation
(* mark_debug = "true" *) logic       write_enable;     // Write enable signal
(* mark_debug = "true" *) logic       read_enable;      // Read enable signal
(* mark_debug = "true" *) logic [31:0] read_data;       // Read data output
(* mark_debug = "true" *) logic [31:0] write_addr_reg;  // Write address register
(* mark_debug = "true" *) logic [31:0] read_addr_reg;   // Read address register
```

### AXI4-Lite Handshake Signals
```systemverilog
(* mark_debug = "true" *) wire aw_handshake;  // Address write handshake
(* mark_debug = "true" *) wire w_handshake;   // Write data handshake
(* mark_debug = "true" *) wire ar_handshake;  // Address read handshake
```

### State Machine
```systemverilog
(* mark_debug = "true" *) axi_state_t axi_state, axi_next_state;  // AXI state machine
```

### Write Operation Local Variables (in always_ff block)
```systemverilog
(* mark_debug = "true" *) logic [11:0] write_offset;   // Write address offset
(* mark_debug = "true" *) logic [11:0] aligned_offset; // Aligned address offset
(* mark_debug = "true" *) bit write_ok;                // Write validation result
(* mark_debug = "true" *) logic [31:0] masked_value;   // Masked write data
```

## AXI4-Lite Interface Signals to Monitor
When using ILA (Integrated Logic Analyzer), also monitor these AXI interface signals:
- `axi.awaddr` - Write address
- `axi.awvalid` - Write address valid
- `axi.awready` - Write address ready
- `axi.wdata` - Write data
- `axi.wvalid` - Write data valid
- `axi.wready` - Write data ready
- `axi.wstrb` - Write strobe
- `axi.bvalid` - Write response valid
- `axi.bready` - Write response ready
- `axi.bresp` - Write response

## Verification Strategy

### Expected Hardware Behavior
1. **Write Operations**: `test_reg_0-3` should store written values from `axi.wdata`
2. **Read Operations**: Should return stored values, not test pattern (0xF02022XX)
3. **Address Decoding**: `write_offset` should match register addresses (0x020-0x02C)
4. **State Machine**: Should transition through WRITE_ADDR → WRITE_DATA → WRITE_RESP

### Test Patterns for Hardware Verification
```
Address 0x1020 (test_reg_0): Write 0xDEADBEEF, Read back 0xDEADBEEF
Address 0x1024 (test_reg_1): Write 0x12345678, Read back 0x12345678
Address 0x1028 (test_reg_2): Write 0xABCDEF00, Read back 0xABCDEF00
Address 0x102C (test_reg_3): Write 0x55AA55AA, Read back 0x55AA55AA
```

### Current FPGA Issue
- Phase 1 investigation confirmed FPGA contains test pattern generator
- All reads return 0xF02022XX pattern instead of register contents
- Write operations appear successful but data not persisted
- Hardware re-programming required with correct Register_Block.sv

## ILA Configuration Recommendations

### Trigger Conditions
1. **Write Trigger**: `write_enable = 1` AND `aligned_offset = 0x020-0x02C`
2. **Address Trigger**: `axi.awaddr[11:0] = 0x020-0x02C`
3. **State Trigger**: `axi_state = WRITE_DATA`

### Capture Depth
- Recommended: 4096 samples
- Critical for capturing complete write/read sequences
- Multiple register access patterns

### Sample Rate
- Use fastest available clock (system clock)
- Capture all signal transitions for timing analysis

## Expected Results After FPGA Re-programming
- `test_reg_0-3` should show actual written values
- Read operations should return stored data, not 0xF02022XX
- State machine should operate normally
- Write handshakes should complete successfully

## Documentation
- Created: 2025-10-07
- Purpose: Hardware verification of register write operations
- Next Phase: Coordinate with hardware team for FPGA re-programming