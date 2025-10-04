# UART RX Counter Debug Analysis
Date: October 5, 2025

## Problem Statement
The UART RX counter (`rx_transaction_count`) is not incrementing as expected during hardware operation. This suggests that RX transactions are not being properly detected or completed.

## Added Debug Signals for UART RX Investigation

### 1. UART Physical Layer Debug (Uart_Rx.sv)
```systemverilog
(* mark_debug = "true" *) logic [BAUD_WIDTH-1:0] baud_counter;    // Baud rate timing
(* mark_debug = "true" *) logic baud_tick;                       // Baud rate tick
(* mark_debug = "true" *) logic [SAMPLE_WIDTH-1:0] sample_counter; // Sample timing
(* mark_debug = "true" *) logic sample_tick;                     // Sample tick
(* mark_debug = "true" *) logic [3:0] bit_counter;               // Bit position counter
(* mark_debug = "true" *) rx_state_t rx_state, rx_state_next;    // RX state machine
(* mark_debug = "true" *) logic [7:0] rx_shift_reg;              // Data shift register
(* mark_debug = "true" *) logic [1:0] rx_sync;                   // Input synchronizer
(* mark_debug = "true" *) logic rx_synced;                       // Synchronized RX input
```

### 2. UART Bridge Layer Debug (Uart_Axi4_Bridge.sv)
```systemverilog
(* mark_debug = "true" *) logic [7:0] rx_data;                   // Received byte data
(* mark_debug = "true" *) logic rx_valid;                        // RX data valid pulse
(* mark_debug = "true" *) logic rx_error;                        // RX framing error
(* mark_debug = "true" *) logic rx_busy;                         // RX busy status
(* mark_debug = "true" *) logic rx_fifo_wr_en;                   // RX FIFO write enable
(* mark_debug = "true" *) logic [7:0] rx_fifo_rd_data;           // RX FIFO read data
(* mark_debug = "true" *) logic [RX_FIFO_WIDTH-1:0] rx_fifo_count; // RX FIFO level
```

### 3. Protocol Parser Debug
```systemverilog
(* mark_debug = "true" *) logic [7:0] parser_cmd;                // Parsed command
(* mark_debug = "true" *) logic [31:0] parser_addr;              // Parsed address
(* mark_debug = "true" *) logic [5:0] parser_data_count;         // Parsed data count
(* mark_debug = "true" *) logic parser_frame_valid;              // Frame valid flag
(* mark_debug = "true" *) logic parser_frame_error;              // Frame error flag
(* mark_debug = "true" *) logic parser_busy;                     // Parser busy status
```

### 4. Transaction Counter Debug
```systemverilog
(* mark_debug = "true" *) logic [15:0] rx_count_reg;             // RX counter register
(* mark_debug = "true" *) logic rx_transaction_complete;         // RX completion signal
(* mark_debug = "true" *) main_state_t main_state;               // Main state machine
```

## Debug Investigation Strategy

### Phase 1: UART Physical Layer Verification
**Objective**: Confirm UART RX is receiving data correctly

**Key Signals to Monitor**:
1. `uart_rx` - Raw input signal
2. `rx_sync` - Synchronized input
3. `rx_state` - State machine progression
4. `baud_tick` - Timing accuracy
5. `sample_counter` - Sample timing
6. `bit_counter` - Bit reception progress
7. `rx_shift_reg` - Data accumulation

**Expected Behavior**:
- `uart_rx` should show start/stop bit transitions
- `rx_state` should cycle: IDLE → START_BIT → DATA_BITS → STOP_BIT
- `baud_tick` should occur at correct intervals (~115200 * 16 Hz)
- `sample_counter` should count 0-15 during each bit period
- `bit_counter` should count 0-7 during data reception
- `rx_shift_reg` should accumulate received bits

### Phase 2: UART-to-FIFO Interface
**Objective**: Verify data flows from UART to RX FIFO

**Key Signals to Monitor**:
1. `rx_data` - Byte received from UART
2. `rx_valid` - Data valid pulse
3. `rx_error` - Reception errors
4. `rx_fifo_wr_en` - FIFO write enable
5. `rx_fifo_count` - FIFO fill level

**Expected Behavior**:
- `rx_valid` should pulse when byte is received
- `rx_fifo_wr_en` should follow `rx_valid`
- `rx_fifo_count` should increment with each write
- No `rx_error` should occur for valid frames

### Phase 3: Protocol Frame Processing
**Objective**: Verify frame parsing and validation

**Key Signals to Monitor**:
1. `parser_frame_valid` - Complete frame detected
2. `parser_cmd` - Extracted command byte
3. `parser_addr` - Extracted address
4. `parser_data_count` - Extracted data length
5. `parser_frame_error` - Frame validation errors

**Expected Behavior**:
- `parser_frame_valid` should pulse for complete valid frames
- `parser_cmd` bit 7 should be '1' for read commands
- `parser_addr` should match expected address ranges
- No `parser_frame_error` for valid protocol frames

### Phase 4: Transaction Completion Logic
**Objective**: Verify counter increment conditions

**Key Signals to Monitor**:
1. `main_state` - Main controller state
2. `rx_transaction_complete` - Counter increment condition
3. `rx_count_reg` - Actual counter value
4. `builder_response_complete` - Response completion
5. `parser_cmd[7]` - Read command indicator

**Expected Behavior**:
- `rx_transaction_complete` should pulse for read transactions
- Condition: `builder_response_complete && parser_cmd[7]`
- `rx_count_reg` should increment when condition is met

## Common RX Counter Issues and Debugging

### Issue 1: No UART Activity Detected
**Symptoms**: `rx_state` stays in IDLE, no `baud_tick` activity
**Debug Focus**: Clock generation, reset conditions
**Check**: `baud_counter`, system clock, reset release

### Issue 2: UART Receives But FIFO Empty
**Symptoms**: `rx_valid` pulses but `rx_fifo_count` = 0
**Debug Focus**: FIFO write enable logic
**Check**: `rx_fifo_wr_en` timing, FIFO full conditions

### Issue 3: FIFO Fills But No Frame Detection
**Symptoms**: `rx_fifo_count` > 0 but `parser_frame_valid` never asserts
**Debug Focus**: Frame parsing logic, protocol compliance
**Check**: Frame structure, CRC validation, command format

### Issue 4: Frames Valid But Counter Not Incrementing
**Symptoms**: `parser_frame_valid` pulses but `rx_count_reg` unchanged
**Debug Focus**: Transaction completion logic
**Check**: `rx_transaction_complete` conditions, state machine progression

## ILA Trigger Recommendations

### Trigger 1: UART Activity Start
```
Trigger: uart_rx falling edge (start bit detection)
Capture: 2048 samples before and after trigger
```

### Trigger 2: RX Data Valid
```
Trigger: rx_valid rising edge
Capture: Focus on FIFO write operations
```

### Trigger 3: Frame Completion
```
Trigger: parser_frame_valid rising edge
Capture: Protocol parsing results
```

### Trigger 4: Counter Issues
```
Trigger: rx_transaction_complete rising edge
Capture: Counter increment conditions
```

## Analysis Checklist

- [ ] UART clock generation correct (baud_tick frequency)
- [ ] Input synchronization working (rx_sync progression)
- [ ] State machine transitions (IDLE→START→DATA→STOP)
- [ ] Bit timing accuracy (sample_counter, bit_counter)
- [ ] Data reception (rx_shift_reg accumulation)
- [ ] FIFO interface (rx_valid → rx_fifo_wr_en)
- [ ] Frame parsing (valid frame detection)
- [ ] Protocol compliance (command, address, CRC)
- [ ] Transaction completion logic
- [ ] Counter increment conditions

## Expected Debug Timeline

1. **Initial Capture** (30 minutes): Basic UART activity verification
2. **Protocol Analysis** (1 hour): Frame structure and parsing
3. **Counter Logic** (30 minutes): Transaction completion analysis
4. **Root Cause** (30 minutes): Identify specific failure point
5. **Verification** (30 minutes): Confirm fix implementation

Total estimated debug time: ~3 hours for complete analysis.