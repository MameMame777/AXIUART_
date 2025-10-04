# AXIUART.xdc Review Recommendations
Date: October 4, 2025

## Summary
The constraint file is generally well-structured but contains some documentation inconsistencies that should be corrected for clarity and maintainability.

## Critical Issues Found

### 1. Clock Frequency Comment Inconsistency
**Issue**: Comment states RTL default is 50MHz, but RTL shows 125MHz
**Location**: Line ~18
**Current**: `# Note: RTL default is 50MHz, but Zybo Z7-20 provides 125MHz`
**Should be**: `# System Clock - 125MHz input (matching RTL CLK_FREQ_HZ parameter)`

### 2. Pin Assignment Comments Confusion
**Issue**: Comments describe device perspective but should describe FPGA perspective
**Location**: Lines 35-42

**Current problematic comments**:
```
# Clear to Send (デバイス CTS出力)
set_property -dict {PACKAGE_PIN V8 IOSTANDARD LVCMOS33} [get_ports uart_rts_n]
# UART Transmit Data (デバイス TX)  
set_property -dict {PACKAGE_PIN W8 IOSTANDARD LVCMOS33} [get_ports uart_rx]
```

**Should be**:
```
# RTS_N - Request to Send (FPGA output, active low)
set_property -dict {PACKAGE_PIN V8 IOSTANDARD LVCMOS33} [get_ports uart_rts_n]
# UART_RX - Receive Data (FPGA input from external device)
set_property -dict {PACKAGE_PIN W8 IOSTANDARD LVCMOS33} [get_ports uart_rx]
# UART_TX - Transmit Data (FPGA output to external device)
set_property -dict {PACKAGE_PIN U7 IOSTANDARD LVCMOS33} [get_ports uart_tx]
# CTS_N - Clear to Send (FPGA input, active low)
set_property -dict {PACKAGE_PIN V7 IOSTANDARD LVCMOS33} [get_ports uart_cts_n]
```

## Recommendations

### High Priority
1. **Correct clock frequency comment** - Remove confusion about 50MHz vs 125MHz
2. **Clarify pin assignment comments** - Use FPGA perspective consistently
3. **Remove Japanese comments** - Follow English documentation guideline

### Medium Priority  
1. **Add signal direction documentation** - Clearly document input/output for each pin
2. **Verify PMOD UART pinout** - Ensure pin assignments match actual PMOD UART module
3. **Add timing constraint comments** - Explain rationale for delay values

### Low Priority
1. **Organize constraint sections** - Group related constraints together
2. **Add implementation notes** - Document any special considerations
3. **Consider adding debug constraints** - For development/debugging phases

## Verification Checklist
- [ ] Clock frequency matches RTL parameter (125MHz) ✅
- [ ] All RTL port names have corresponding constraints ✅
- [ ] Pin assignments match board documentation ⚠️ (verify with actual PMOD)
- [ ] Input/output directions are correct ✅
- [ ] Timing constraints are appropriate ✅
- [ ] Comments are accurate and consistent ❌

## Next Steps
1. Update comments for clarity and accuracy
2. Verify PMOD UART pinout against hardware documentation
3. Test constraints with actual hardware implementation
4. Document any board-specific considerations

## Files to Update
- `PandR/constraint/AXIUART.xdc` - Apply comment corrections
- `docs/` - Update constraint documentation if needed