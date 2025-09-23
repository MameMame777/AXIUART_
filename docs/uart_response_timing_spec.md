# UART Response Hardware Specification

## Overview
This document defines the precise timing specifications for UART response generation in the AXIUART system based on actual RTL implementation analysis.

## Hardware Architecture
- **Clock Frequency**: 50MHz (20ns period)
- **UART Baud Rate**: 115200 baud
- **Bit Time**: 8.68µs (434 clock cycles @ 50MHz)
- **Byte Time**: 86.8µs (4340 clock cycles for 8N1 format)

## Response Timing Specification

### 1. Frame Processing Pipeline
```
Host Frame → UART RX → FIFO → Frame Parser → AXI Bridge → Frame Builder → TX FIFO → UART TX
```

### 2. Critical Timing Parameters

#### A. Frame Processing Delay
- **UART RX to Parser**: ~1 clock cycle (FIFO latency)
- **Parser Processing**: Variable (depends on frame validation)
- **AXI Bridge Response**: ~10-50 clock cycles (register access)
- **Frame Builder**: Variable (depends on response type)
- **Builder to UART TX**: ~1 clock cycle (FIFO latency)

#### B. Response Start Timing
**From actual debug logs analysis**:
- Frame reception complete → Response transmission start
- **Expected Delay**: 50-100µs (typical processing time)
- **Measured Pattern**: Response starts immediately after frame processing

#### C. Inter-byte Timing
- **Standard UART**: 1 stop bit + 1 start bit = 2 bit times = 17.36µs
- **Implementation**: May have additional processing delays

#### D. Frame Structure
**Write Response (4 bytes)**:
1. SOF: 0x5A (Device-to-Host Start of Frame)
2. STATUS: 0x00 (Success) or error code
3. CMD_ECHO: Original command byte
4. CRC: CRC-8 of STATUS + CMD_ECHO

**Read Response (Variable)**:
1. SOF: 0x5A
2. STATUS: 0x00 or error code
3. CMD_ECHO: Original command byte
4. ADDR_ECHO: 4 bytes (if success)
5. DATA: Variable length (if success)
6. CRC: CRC-8 of all preceding bytes

## Driver Implementation Requirements

### 3. Response Collection Strategy

#### A. Sequential Approach (Recommended)
```systemverilog
// 1. Send command frame
drive_frame(request);

// 2. Wait for response start (with timeout)
fork : response_timeout
    begin
        // Wait for TX line to go low (start bit)
        wait(uart_tx == 1'b0);
        response_detected = 1;
    end
    begin
        // Timeout protection
        repeat(RESPONSE_TIMEOUT_CYCLES) @(posedge clk);
        response_detected = 0;
    end
join_any
disable response_timeout;

// 3. Collect response bytes if detected
if (response_detected) begin
    collect_response_frame();
end
```

#### B. Timing Parameters
```systemverilog
// Response timeout: Max expected processing delay
localparam RESPONSE_TIMEOUT_US = 1000;  // 1ms
localparam RESPONSE_TIMEOUT_CYCLES = (RESPONSE_TIMEOUT_US * CLK_FREQ_HZ) / 1_000_000;

// Inter-byte timeout: Max gap between response bytes
localparam INTER_BYTE_TIMEOUT_US = 200;  // 200µs
localparam INTER_BYTE_TIMEOUT_CYCLES = (INTER_BYTE_TIMEOUT_US * CLK_FREQ_HZ) / 1_000_000;
```

### 4. Current Issue Analysis

#### Problem Identification
From debug logs, the Driver is collecting bytes at wrong timing:
- Hardware sends 0x5A at time T
- Driver collects different byte at time T+17ms

#### Root Cause
The Driver's `wait(uart_tx == 1'b0)` is not synchronized with the actual response frame start, likely due to:
1. Multiple TX transmissions occurring
2. Driver waiting for wrong TX event
3. Timing race condition

#### Solution Requirements
1. **Precise Response Start Detection**: Detect the first TX start bit after command transmission
2. **Frame Boundary Recognition**: Distinguish response frame from other TX activity
3. **Robust Timeout Handling**: Handle cases where no response occurs

## Testing Validation

### 5. Success Criteria
- Driver collects first byte = 0x5A (SOF)
- All response bytes collected in correct sequence
- No timing-related collection errors
- Consistent behavior across multiple test runs

### 6. Debug Requirements
- Log response detection timing
- Log each collected byte with timestamp
- Compare with hardware TX debug messages
- Verify frame structure integrity

## Implementation Priority
1. **High Priority**: Fix response start detection timing
2. **Medium Priority**: Implement robust timeout handling  
3. **Low Priority**: Optimize for different response types