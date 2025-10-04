# Hardware Debug Configuration with mark_debug
Date: October 4, 2025

## Mark Debug Signal List

### Clock and Reset Signals
- `clk` - System clock (125MHz)
- `rst` - External reset input
- `internal_rst` - Internal reset signal

### UART Interface Signals
- `uart_rx` - UART receive data input
- `uart_tx` - UART transmit data output  
- `uart_rts_n` - Request to Send (active low)
- `uart_cts_n` - Clear to Send (active low)

### Bridge Control and Status
- `bridge_enable` - Bridge enable control
- `bridge_busy` - Bridge busy status
- `bridge_error_code[7:0]` - Error code from bridge
- `tx_count[15:0]` - Transmission counter
- `rx_count[15:0]` - Reception counter
- `fifo_status[7:0]` - FIFO status flags

### Flow Control Signals
- `rx_fifo_full` - RX FIFO full flag
- `rx_fifo_high` - RX FIFO high threshold flag
- `tx_ready` - TX ready status

### System Monitoring
- `clk_div` - Clock divider for LED (heartbeat)
- `clk_div_counter[25:0]` - Clock divider counter

## Debug Strategy

### 1. Power-On and Reset Debug
**Signals to monitor:**
- `clk`, `rst`, `internal_rst`
- `bridge_enable`
- `clk_div` (heartbeat)

**Expected behavior:**
- Clock should be stable 125MHz
- Reset should be properly released
- Bridge should initialize correctly
- Heartbeat should start blinking (~1.86Hz)

### 2. UART Communication Debug
**Signals to monitor:**
- `uart_rx`, `uart_tx`
- `uart_rts_n`, `uart_cts_n`
- `rx_fifo_full`, `rx_fifo_high`, `tx_ready`

**Expected behavior:**
- UART signals should show proper start/stop bits
- Flow control should work correctly
- FIFO status should reflect data levels

### 3. Bridge Operation Debug
**Signals to monitor:**
- `bridge_busy`
- `bridge_error_code`
- `tx_count`, `rx_count`
- `fifo_status`

**Expected behavior:**
- Bridge should go busy during transactions
- Error code should remain 0x00 for normal operation
- Counters should increment with transactions
- FIFO status should reflect buffer utilization

## Vivado ILA Configuration

### Trigger Conditions
1. **Reset Release**: Trigger on `rst` falling edge
2. **Error Detection**: Trigger when `bridge_error_code != 0`
3. **UART Activity**: Trigger on `uart_rx` or `uart_tx` edge
4. **Flow Control**: Trigger on `uart_rts_n` or `uart_cts_n` changes

### Capture Depth Recommendations
- **Minimum**: 1024 samples for basic debugging
- **Recommended**: 4096 samples for flow control analysis
- **Maximum**: 8192+ samples for protocol analysis

### Sample Rate
- Use full clock rate (125MHz) for accurate timing analysis
- Consider decimation only for long-term monitoring

## Common Debug Scenarios

### 1. System Not Starting
**Check signals:**
- `clk` - Verify 125MHz clock presence
- `rst` - Confirm reset is properly released
- `bridge_enable` - Should go high after initialization
- `clk_div` - Heartbeat should be visible

### 2. UART Communication Issues
**Check signals:**
- `uart_rx`/`uart_tx` - Verify signal levels and timing
- Baud rate timing analysis
- Start/stop bit integrity

### 3. Flow Control Problems
**Check signals:**
- `uart_rts_n`/`uart_cts_n` timing relationship
- `rx_fifo_full`/`rx_fifo_high` thresholds
- `tx_ready` status

### 4. Bridge Protocol Errors
**Check signals:**
- `bridge_error_code` for specific error types
- `bridge_busy` timing
- Transaction counters behavior

## Implementation Notes

### Resource Usage Impact
- Each marked signal uses ILA resources
- Total of 18 marked signals
- Estimated resource usage: ~5-10% of typical Zynq device

### Performance Impact
- Mark debug signals are excluded from optimization
- May slightly impact timing closure
- Monitor timing reports after implementation

### Debug Port Constraints
The ILA will automatically use debug ports. Ensure debug ports are not constrained in XDC file.

## Usage Instructions

1. **Synthesis**: Vivado will automatically detect mark_debug attributes
2. **Implementation**: ILA cores will be automatically inserted
3. **Programming**: Use Vivado Hardware Manager for debugging
4. **Analysis**: Use ILA dashboard for signal visualization

## Troubleshooting

### ILA Not Appearing
- Verify mark_debug syntax is correct
- Check that signals are not optimized away
- Ensure debug_core IP is enabled in project

### Signal Not Captured
- Verify signal is actually toggling
- Check trigger conditions
- Confirm capture window timing

### Resource Limitations
- Reduce number of marked signals if needed
- Use selective marking based on debug priority
- Consider using multiple debug sessions