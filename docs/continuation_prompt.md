# プロジェクト継続作業用の簡潔なプロンプト

以下のプロンプトを新規担当者に提供してください：

---

## AXIUART Emergency Repair - Phase 3 Execution Prompt

### 🎯 PROJECT CONTEXT
**AXIUART Bridge**: SystemVerilog UART↔AXI4-Lite bridge under emergency repair
**Current Status**: Phase 2 complete (infrastructure fixes), Phase 3 ready (data alignment + testing)
**Environment**: Windows + DSIM v20240422.0.0 + PowerShell automation
**Git Status**: main branch, commit 6f5102c, working tree clean

### 🚨 CRITICAL ISSUE
**Root Cause**: RTL Frame_Builder generates sequential test data (0xa6, 0xa7, 0xa8...) but UVM testbench expects different CRC patterns, causing 45 timeout errors.

### 📋 EXECUTION TASKS

#### **TASK 1: Data Alignment Fix** (CRITICAL, 2-3 hrs)
**Objective**: Resolve RTL-testbench data mismatch (45 UVM_ERROR → 0)

**Steps**:
1. `cd e:\Nautilus\workspace\fpgawork\AXIUART_`
2. Examine `rtl/Frame_Builder.sv` lines 120-150 (response data generation)
3. Examine `sim/uvm/agents/uart/uart_monitor.sv` lines 180-220 (CRC validation)
4. **Fix Option A**: Update RTL to use actual AXI data instead of sequential test data
5. **Fix Option B**: Update testbench to expect CRC for sequential data
6. Test: `cd sim\uvm && .\run_uvm.ps1 -TestName uart_axi4_basic_test`
7. Success: UVM_ERROR: 0, TEST PASSED

#### **TASK 2: CRC Unit Tests** (HIGH, 3-4 hrs)  
**Objective**: Create 6-case CRC validation suite

**Steps**:
1. Create `sim/uvm/tests/crc_unit_test.sv`
2. Implement 6 test cases: normal, 1-bit flip, all-0, all-1, 2 random seeds
3. Create Python reference: `temporary/crc_reference_validation.py`
4. Test: `.\run_uvm.ps1 -TestName crc_unit_test -Verbosity UVM_HIGH`
5. Success: All 6 CRC calculations match reference

#### **TASK 3: Coverage Collection** (MEDIUM, 4-5 hrs)
**Objective**: Achieve ≥80% coverage with comprehensive protocol tests

**Steps**:
1. `.\run_uvm.ps1 -TestName uart_axi4_comprehensive_test -Coverage $true`
2. `dcreport.exe metrics.db -out_dir coverage_report -html`
3. Enhance `sequences/comprehensive_protocol_sequence.sv`
4. Success: Coverage ≥80%, comprehensive test report

### 🛠️ QUICK START
```powershell
# Environment verification
cd e:\Nautilus\workspace\fpgawork\AXIUART_
git status  # Should be: working tree clean
cd sim\uvm
.\run_uvm.ps1 -TestName uart_axi4_minimal_test  # Should complete

# Start with Task 1 - most critical
```

### ✅ SUCCESS CRITERIA
- Task 1: UVM_ERROR 45→0, TEST PASSED status
- Task 2: 6 CRC test cases passing, <30s execution
- Task 3: ≥80% coverage, HTML report generated
- All: Git commits with detailed messages, documentation updates

### 📊 DELIVERABLES
- Fixed RTL or testbench with validation
- CRC unit test suite with reference implementation
- Coverage report with protocol test enhancement
- Documentation in `docs/` directory
- Development diary entry

**Environment Ready**: PowerShell execution pipeline validated, 12 test cases available, infrastructure solid for continued development.

**Key Files**: 
- RTL: `rtl/Frame_Builder.sv` (data generation)
- Testbench: `sim/uvm/agents/uart/uart_monitor.sv` (CRC validation)
- Test Runner: `sim/uvm/run_uvm.ps1` (execution pipeline)

**Previous Work**: Stage 1-2 complete (CRC fixes, bridge enable, SOF alignment, TX pulse). Ready for Phase 3 execution.

---

**使用方法**: このプロンプトを新規担当者にそのまま提供し、Task 1から順番に実行してもらってください。各タスクは独立しており、段階的に品質向上を図れます。