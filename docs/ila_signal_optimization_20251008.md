# ILA Signal Optimization for WRITE_ADDR Debug Issue
## Date: October 8, 2025

### Problem Summary
- `reg_test_working_protocol.py` successfully reaches WRITE_ADDR state but gets stuck
- AXI handshake `aw_handshake` appears to not complete properly
- Need to debug AXI Master-Slave handshake completion

### Optimized ILA Signal Configuration

#### CRITICAL Signals Added for WRITE_ADDR Debug:
1. **AXI Master (Axi4_Lite_Master.sv)**:
   - `awvalid_int` - Master write address valid signal generation
   - `axi_awready` - Slave write address ready signal reception
   - `axi_wready` - Slave write data ready signal reception  
   - `axi_bvalid` - Slave write response valid signal reception
   - `aw_handshake` - Write address handshake completion detection
   - `timeout_counter` - Timeout monitoring for stuck states
   - `timeout_occurred` - Timeout detection flag

2. **AXI Slave (Register_Block.sv)** (Already configured):
   - `axi_state` - AXI slave state machine
   - `axi_awvalid_debug` - Master awvalid signal reception confirmation
   - `axi_awaddr_debug` - Write address value
   - `axi_wdata_debug` - Write data value
   - `aw_handshake` - Slave side handshake detection
   - `reg_test_write_trigger` - REG_TEST register write trigger

#### Retained Essential Signals:
- `cmd_reg` - Command verification (confirmed working at 0x20)
- `start_transaction` - Transaction initiation detection
- `transaction_done` - Transaction completion confirmation
- `state` - AXI Master state machine monitoring

#### Removed Redundant/Solved Signals:
- Input signals (`cmd`, `addr`, `axi_status`) - functionality confirmed
- Command processing signals (`rw_bit`, `cmd_reg_updated`, etc.) - problem solved
- Alignment check signals (`check_alignment_state`, etc.) - working correctly
- Write data phase signals (`wvalid_int`, `w_handshake`) - focus on address phase first

### Key Debug Questions to Answer:
1. **Does `awvalid_int` assert correctly when state=WRITE_ADDR?**
2. **Does `axi_awready` from Register_Block assert properly?**
3. **Does `aw_handshake` ever complete, or is there a timing issue?**
4. **Does `timeout_counter` reach AXI_TIMEOUT (2500 cycles)?**
5. **What is Register_Block `axi_state` when Master is in WRITE_ADDR?**

### Expected ILA Trigger Configuration:
```verilog
// Primary trigger: Successful command recognition leading to WRITE_ADDR
trigger_condition = (start_transaction && cmd_reg == 8'h20) ||
                    (state == WRITE_ADDR) ||
                    (aw_handshake) ||
                    (timeout_occurred)
```

### Vivado Project Location:
- Project file: `PandR/vivado/AXIUART_/AXIUART_.xpr`
- Source files: RTL updated with optimized mark_debug signals
- Next step: Open Vivado project, synthesize, implement, and program FPGA

### Manual Vivado Steps:
1. Open `PandR/vivado/AXIUART_/AXIUART_.xpr` 
2. Refresh sources to pick up updated RTL files
3. Run synthesis and implementation
4. Program FPGA with generated bitstream
5. Configure ILA with optimized signal set
6. Run `reg_test_working_protocol.py` and capture waveforms
7. Analyze AXI handshake timing and completion

### Success Criteria:
- Clear visualization of AXI Master `awvalid_int` assertion
- Clear visualization of AXI Slave `axi_awready` response  
- Identification of handshake completion or timeout condition
- Root cause analysis of WRITE_ADDR state stuck issue
- Path to implementing fix for complete write transaction flow

### Next Phase Focus:
Once WRITE_ADDR handshake issue is resolved, monitor WRITE_DATA and WRITE_RESP phases to ensure complete write transaction to REG_TEST registers.