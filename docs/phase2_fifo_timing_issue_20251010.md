# Phase 2 FIFO Synchronization Issue Analysis - 2025-10-10

## Problem Summary

Frame Parser fails to complete CRC_RX state processing due to persistent FIFO synchronization timing issues.

### Key Issue

**Root Cause Identified:** 
FIFO `rd_data` output is combinational (`assign rd_data = mem[rd_ptr]`), but `rd_ptr` is updated via `always_ff` block. This creates a timing mismatch where Frame Parser attempts to read FIFO data in the same clock cycle as asserting `rx_fifo_rd_en`.

### Symptoms Observed

```
DEBUG: Frame_Parser CRC_RX state: rx_fifo_empty=1, rx_fifo_data=0xxx, crc_flag=0 at time 1723390000
DEBUG: Frame_Parser CRC_RX waiting for FIFO data at time 1723390000
```

Despite successful UART RX completion:
```
DEBUG: UART_RX received byte = 0x87 (error=0) stop_bit=1 at time 1723350000
DEBUG: Frame_Parser DATA_RX->CRC_RX (count=2, expected=2) at time 1723370000
```

### Technical Analysis

1. **FIFO Implementation:** `fifo_sync.sv` uses:
   - Combinational read data: `assign rd_data = mem[rd_ptr]`
   - Sequential pointer update: `always_ff` for `rd_ptr`

2. **Frame Parser Issue:** Expects immediate data availability when `rx_fifo_rd_en` asserted

3. **Timing Conflict:** Same-cycle read request and data consumption

### Attempted Solutions

1. ✅ **CRC Flag Synchronization:** Added `crc_data_read_flag` to separate FIFO read from data processing
2. ✅ **Registered Data Capture:** Added `rx_fifo_data_reg` to capture FIFO output
3. ❌ **Two-stage Processing:** Implemented read → process cycle separation
4. ❌ **Enhanced Debug:** Added detailed FIFO transaction logging

**Current Status:** All modifications successful but issue persists

### Next Required Actions

1. **Deep FIFO Analysis:** Investigate exact timing of `rd_ptr` update vs `rd_data` availability
2. **Alternative Architecture:** Consider pipeline approach with proper FIFO handshaking
3. **Reference Implementation:** Compare with working UART bridge implementations

### Impact Assessment

- **Blocking:** Phase 2 completion (Frame Parser CRC processing)
- **Cascading:** captured_cmd=0x00 issue resolution 
- **Project:** Complete UART-to-AXI bridge functionality

### Development Priority

**CRITICAL:** This timing issue is the fundamental blocker preventing Frame Parser completion and must be resolved before proceeding to Phase 3 scoreboard improvements.
