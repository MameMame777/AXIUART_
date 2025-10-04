# ILA Data Analysis - UART RX Counter Debug
Date: October 5, 2025

## CSV Data Analysis Summary

### Key Observations from ILA Capture

#### 1. **System State Analysis**
- **RX State**: Consistently shows `"iSTATE2"` (=0x3) and `"iSTATE"` (=0x0)
- **Main State**: Always shows `0` (MAIN_IDLE state)
- **Bridge Enable**: Consistently `1` (enabled)
- **Bridge Busy**: Always `0` (not busy)

#### 2. **UART Physical Layer Status**
- **rx_sync**: Always `3` (both sync bits high = idle state)
- **sample_counter**: Varies between 0-8
- **bit_counter**: Always `8` 
- **baud_counter**: Incrementing normally (0x08-0x42)
- **baud_tick**: Always `0` (no activity seen)

#### 3. **Critical Signal States**
- **rx_valid**: Always `0` (no valid data received)
- **rx_error**: Always `0` (no framing errors)
- **rx_busy**: Alternates between `0` and `1`
- **rx_fifo_wr_en**: Always `0` (FIFO not being written)
- **rx_fifo_count**: Always `00` (FIFO empty)

#### 4. **Parser and Transaction Status**
- **parser_frame_valid**: Always `0` (no valid frames)
- **parser_busy**: Always `0` (parser idle)
- **rx_transaction_complete**: Always `0` (no completed transactions)
- **rx_count_reg**: Always `0000` (counter not incrementing)

#### 5. **Data Flow Analysis**
- **rx_data**: Shows values `01`, `6b` in different samples
- **rx_shift_reg**: Shows values `01`, `02` (some shifting activity)
- **rx_fifo_rd_data**: Always `00` (no data in FIFO)

## Root Cause Analysis

### **Primary Issue: No UART Input Activity**
The data clearly shows that:
1. **No UART RX transitions**: `rx_sync` = 3 (both bits high) indicates no start bits
2. **No baud tick activity**: `baud_tick` always 0 suggests timing issues
3. **No valid data reception**: `rx_valid` never asserts

### **Possible Causes**

#### 1. **Hardware Connection Issues**
- UART RX pin not connected to actual UART device
- Wrong pin assignment in constraints
- Signal polarity issues
- Open circuit or floating input

#### 2. **Clock/Timing Issues**
- System clock not running at expected 125MHz
- Baud rate generator misconfiguration
- Clock domain crossing problems

#### 3. **External Device Issues**
- UART transmitter not sending data
- Incorrect baud rate on transmitting device
- Flow control (CTS/RTS) blocking transmission

#### 4. **Design Issues**
- Input synchronizer not working correctly
- State machine stuck in wrong state
- Reset not being released properly

## Detailed Signal Analysis

### UART State Machine Behavior
```
rx_state transitions:
- "iSTATE2" (0x3) → "iSTATE" (0x0) → back to "iSTATE2"
- This suggests state machine is running but not detecting start bits
```

### Baud Rate Generator
```
baud_counter: 0x08 → 0x42 (incrementing correctly)
Expected: Counter should reset at BAUD_DIV-1
BAUD_DIV = 125MHz / (115200 * 16) = ~67.8 ≈ 68 (0x44)
Observation: Counter reaches 0x42 = 66, close to expected
```

### Shift Register Activity
```
rx_shift_reg: 0x01, 0x02 (some activity)
This suggests the shift register is receiving some bits
But rx_valid never asserts, indicating incomplete frames
```

## Recommendations for Further Debug

### 1. **Hardware Verification**
- **Check physical connections**: Verify UART RX pin connectivity
- **Oscilloscope analysis**: Probe UART RX pin for actual signal activity
- **Constraint verification**: Confirm pin assignments match hardware

### 2. **Clock Domain Analysis**
- **Clock frequency measurement**: Verify 125MHz system clock
- **Baud rate verification**: Check if baud tick generation is correct
- **Reset analysis**: Ensure clean reset release

### 3. **External Device Check**
- **Transmitter verification**: Confirm external device is transmitting
- **Baud rate matching**: Verify both sides use same baud rate
- **Signal level checking**: Confirm voltage levels (3.3V logic)

### 4. **Design Review**
- **State machine logic**: Review UART RX state transitions
- **Synchronizer effectiveness**: Check input synchronization depth
- **Timing constraints**: Verify proper timing constraints in XDC

## Expected vs Actual Behavior

| Signal | Expected | Actual | Status |
|--------|----------|--------|--------|
| `uart_rx` | Transitions 0↔1 | Always 1 | ❌ No activity |
| `baud_tick` | Periodic pulses | Always 0 | ❌ No timing |
| `rx_valid` | Pulses on byte RX | Always 0 | ❌ No reception |
| `rx_fifo_count` | >0 when data RX | Always 0 | ❌ No data |
| `rx_count_reg` | Increments | Always 0 | ❌ No transactions |

## Next Steps

### Immediate Actions (Priority 1)
1. **Physical verification**: Check UART connections with multimeter/scope
2. **Constraint review**: Verify XDC pin assignments match hardware
3. **External source**: Confirm UART transmitter is actually sending data

### Secondary Analysis (Priority 2)
1. **Clock verification**: Measure actual system clock frequency  
2. **Reset behavior**: Analyze reset timing and release
3. **State machine debug**: Review UART RX state logic

### Long-term Improvements (Priority 3)
1. **Enhanced debug**: Add more ILA probes for clock domain analysis
2. **Self-test capability**: Add internal UART loopback test mode
3. **Better diagnostics**: Implement runtime status reporting

## Conclusion

**Root Cause**: The primary issue is **no UART input activity** reaching the FPGA. The UART RX line appears to be stuck high (idle state), indicating either:
- Physical connection problems
- No external transmitter activity  
- Incorrect pin constraints

**Counter Not Incrementing Because**: No valid UART frames are being received, so the transaction completion logic never triggers.

**Recommended Fix Order**:
1. Verify hardware connections
2. Check external UART transmitter  
3. Validate pin constraints
4. Test with known good UART source