英語で思考し、日本語で応答すること

# AXIUART Emergency Repair Project - Work Handover Instructions
**Date**: September 20, 2025  
**Status**: Phase 3 Ready - Data Alignment & Testing Implementation  
**Assigned Tasks**: Data Integrity Investigation, CRC Unit Testing, Coverage Collection

---

## 🎯 PROJECT OVERVIEW

### Project Purpose
**AXIUART Bridge** is a SystemVerilog-based UART-to-AXI4-Lite bridge enabling communication between UART serial interface and AXI4 memory-mapped peripherals. The project is currently undergoing **emergency repair** following systematic debugging of CRC validation failures and timeout issues.

### Current Mission Status
- **Phase 1**: ✅ COMPLETED - CRC mechanism fixes (47→2 mismatches)
- **Phase 2**: ✅ COMPLETED - Infrastructure fixes (bridge enable, SOF alignment, TX pulse)
- **Phase 3**: 🚀 **READY FOR EXECUTION** - Data alignment & comprehensive testing

### Technical Foundation
- **Hardware Target**: Zynq-7000 FPGA (50MHz system clock)
- **UART Protocol**: 115200 baud, 8N1, CRC-8 polynomial 0x07
- **Frame Format**: [SOF][CMD][ADDR_H][ADDR_L][DATA_0-3][CRC]
- **Simulation**: DSIM v20240422.0.0 with UVM 1.2 framework
- **Automation**: PowerShell execution pipeline validated

---

## 🔍 CURRENT PROJECT STATE

### Codebase Status (Git: main branch, commit 6f5102c)

#### ✅ Fixed Components
1. **CRC Mechanism** (`rtl/Crc8_Calculator.sv`)
   - Polynomial 0x07 implementation verified
   - Excludes SOF byte from calculation (protocol compliant)
   - Both command and response CRC generation working

2. **Protocol Constants** (`rtl/Frame_Builder.sv`, `rtl/Frame_Parser.sv`)
   - SOF_HOST_TO_DEVICE: 0x5A (was 0xAA)
   - SOF_DEVICE_TO_HOST: 0xA5 (was 0x55)
   - Protocol documentation alignment complete

3. **Bridge Infrastructure** (`rtl/Register_Block.sv`, `rtl/Uart_Axi4_Bridge.sv`)
   - Bridge enable default: control_reg[0] = 1 (auto-enable on startup)
   - TX start pulse generation implemented (prevents continuous triggering)

4. **UVM Testbench** (`sim/uvm/agents/uart/uart_driver.sv`)
   - CRC calculation debug tracing implemented
   - Driver CRC calculation verified against Python reference
   - Command frame generation confirmed accurate

#### ⚠️ Outstanding Issues
1. **Data Alignment Problem** (Root Cause Identified)
   - **Issue**: RTL Frame_Builder generates response frames with sequential test data (0xa6, 0xa7, 0xa8, 0xa9...)
   - **Problem**: UVM testbench expects CRC values for different data patterns
   - **Impact**: 45 UVM_ERROR timeout failures in uart_axi4_basic_test
   - **Location**: Response data generation in `rtl/Frame_Builder.sv` around line 120-150

2. **Test Coverage**: Currently 0% - no meaningful protocol tests running
3. **CRC Edge Cases**: No dedicated unit tests for CRC boundary conditions

### Execution Environment Status
- **PowerShell Pipeline**: ✅ Fully operational (`sim/uvm/run_uvm.ps1`)
- **Available Tests**: 12 specialized test cases ready for execution
- **Waveform Analysis**: MXD format dumps working (`uart_axi4_basic_test.mxd` generated)
- **DSIM Simulation**: Complete compilation and execution pipeline validated

---

## 🚀 PHASE 3 WORK ASSIGNMENTS

### **TASK 1: Data Alignment Investigation**
**Priority**: CRITICAL  
**Estimated Time**: 2-3 hours  
**Objective**: Resolve RTL-testbench data mismatch causing 45 timeout errors

#### Detailed Work Steps:

1. **RTL Response Data Analysis**
   ```powershell
   # Navigate to project directory
   cd e:\Nautilus\workspace\fpgawork\AXIUART_
   
   # Read Frame_Builder response data generation
   ```
   - **File**: `rtl/Frame_Builder.sv`
   - **Lines to examine**: 120-150 (response data assignment)
   - **Key question**: Why does RTL generate sequential data (0xa6, 0xa7, 0xa8)?
   - **Expected**: Response should contain actual AXI read data or predefined test patterns

2. **Testbench Expectation Analysis**
   ```powershell
   # Examine monitor CRC validation
   ```
   - **File**: `sim/uvm/agents/uart/uart_monitor.sv`
   - **Lines to examine**: 180-220 (CRC validation logic)
   - **Key question**: What CRC values does testbench expect for response frames?
   - **Action**: Compare monitor expected CRC with RTL-calculated CRC for sequential data

3. **Data Flow Tracing**
   - **Command Path**: Driver → UART TX → RTL Parser → AXI Bridge → Register Block
   - **Response Path**: Register Block → AXI Bridge → RTL Builder → UART TX → Monitor
   - **Critical Point**: Verify AXI read data matches what Frame_Builder puts in response

4. **Fix Implementation Options**:
   - **Option A**: Modify RTL to use actual AXI read data instead of sequential test data
   - **Option B**: Update testbench to expect CRC for sequential data patterns
   - **Recommendation**: Option A (RTL fix) for realistic behavior

5. **Validation Steps**:
   ```powershell
   # Test after fix
   cd e:\Nautilus\workspace\fpgawork\AXIUART_\sim\uvm
   .\run_uvm.ps1 -TestName uart_axi4_basic_test -Verbosity UVM_MEDIUM
   
   # Success criteria: UVM_ERROR: 0, TEST PASSED
   ```

#### Expected Deliverables:
- Root cause documentation in `docs/data_alignment_analysis.md`
- RTL fix in `rtl/Frame_Builder.sv` OR testbench update in monitor
- Git commit with fix and validation results
- UVM_ERROR count reduction from 45 → 0

---

### **TASK 2: CRC Unit Test Implementation**
**Priority**: HIGH  
**Estimated Time**: 3-4 hours  
**Objective**: Create comprehensive CRC validation test suite

#### Detailed Work Steps:

1. **Test Case Design**
   ```systemverilog
   // Required test cases (minimum 6):
   // 1. Normal operation: [0x5A][0x01][0x00][0x04][0x12][0x34][0x56][0x78] → CRC
   // 2. Single bit flip: Verify CRC detects 1-bit errors
   // 3. All zeros: [0x5A][0x00][0x00][0x00][0x00][0x00][0x00][0x00] → CRC
   // 4. All ones: [0x5A][0xFF][0xFF][0xFF][0xFF][0xFF][0xFF][0xFF] → CRC
   // 5. Random seed 1: Predetermined random data set 1
   // 6. Random seed 2: Predetermined random data set 2
   ```

2. **Implementation Structure**
   - **New File**: `sim/uvm/tests/crc_unit_test.sv`
   - **New Sequence**: `sim/uvm/sequences/crc_validation_sequence.sv`
   - **Integration**: Add to `sim/uvm/dsim_config.f`

3. **CRC Reference Implementation**
   ```python
   # Create Python reference for validation
   # File: temporary/crc_reference_validation.py
   def crc8_calculate(data_bytes):
       polynomial = 0x07
       crc = 0x00
       for byte in data_bytes:
           crc ^= byte
           for _ in range(8):
               crc = (crc << 1) ^ polynomial if crc & 0x80 else crc << 1
               crc &= 0xFF
       return crc
   ```

4. **SystemVerilog Test Implementation**
   ```systemverilog
   // Minimal test structure
   class crc_unit_test extends uart_axi4_base_test;
       // Test cases 1-6 with known CRC values
       // Direct CRC module stimulation (bypass UART)
       // Compare RTL CRC output with Python reference
   endclass
   ```

5. **Execution and Validation**
   ```powershell
   # Run CRC unit tests
   .\run_uvm.ps1 -TestName crc_unit_test -Verbosity UVM_HIGH
   
   # Success criteria: All 6 CRC calculations match reference values
   ```

#### Expected Deliverables:
- CRC unit test suite (`tests/crc_unit_test.sv`)
- Python reference implementation (`temporary/crc_reference_validation.py`)
- Test execution results with 100% pass rate
- Documentation in `docs/crc_unit_test_report.md`

---

### **TASK 3: Coverage Collection & Protocol Testing**
**Priority**: MEDIUM  
**Estimated Time**: 4-5 hours  
**Objective**: Implement comprehensive UART protocol testing with coverage collection

#### Detailed Work Steps:

1. **Coverage Infrastructure Setup**
   ```powershell
   # Enable coverage collection
   .\run_uvm.ps1 -TestName uart_axi4_comprehensive_test -Coverage $true -Verbosity UVM_MEDIUM
   
   # Generate coverage report
   dcreport.exe metrics.db -out_dir coverage_report
   ```

2. **Protocol Test Cases Implementation**
   - **Read Transactions**: Single, burst, boundary addresses
   - **Write Transactions**: Single, burst, data patterns
   - **Error Conditions**: Invalid CRC, malformed frames, timeout scenarios
   - **Performance Tests**: Back-to-back transactions, maximum throughput

3. **Coverage Targets** (Minimum 80% target)
   - **Line Coverage**: RTL statement execution
   - **Branch Coverage**: Conditional logic paths
   - **FSM Coverage**: All state transitions
   - **Protocol Coverage**: Frame types, error conditions

4. **Test Sequence Enhancement**
   - **File**: `sim/uvm/sequences/comprehensive_protocol_sequence.sv`
   - **Integration**: Update existing comprehensive test
   - **Execution**: Use multiple seeds for randomization

5. **Coverage Analysis**
   ```powershell
   # Generate detailed coverage report
   dcreport.exe metrics.db -out_dir coverage_report -html
   
   # Open coverage_report/index.html for analysis
   ```

#### Expected Deliverables:
- Enhanced protocol test suite with coverage collection
- Coverage report showing ≥80% line/branch coverage  
- Protocol coverage analysis in `docs/coverage_analysis_report.md`
- Performance metrics and throughput analysis

---

## 🛠️ DEVELOPMENT ENVIRONMENT SETUP

### Required Tools
1. **DSIM Simulator**: v20240422.0.0 (Environment: `%DSIM_HOME%`)
2. **PowerShell**: Windows PowerShell 5.1+ with execution policy configured
3. **Git**: Version control with main branch checkout
4. **Text Editor**: VS Code recommended with SystemVerilog extensions

### Environment Validation
```powershell
# Verify DSIM installation
$env:DSIM_HOME
# Should return: C:\Users\Nautilus\AppData\Local\metrics-ca\dsim\20240422.0.0

# Verify project structure
cd e:\Nautilus\workspace\fpgawork\AXIUART_
git status
# Should return: On branch main, up to date

# Verify PowerShell execution
cd sim\uvm
.\run_uvm.ps1 -TestName uart_axi4_minimal_test
# Should complete without PowerShell execution errors
```

### Quick Start Verification
```powershell
# 1. Navigate to project
cd e:\Nautilus\workspace\fpgawork\AXIUART_

# 2. Check current status  
git log --oneline -3
# Expected: 6f5102c Milestone: PowerShell execution environment validated

# 3. Run lightweight test
cd sim\uvm
.\run_uvm.ps1 -TestName uart_axi4_minimal_test -Verbosity UVM_LOW

# 4. Expected result: Test completes (errors expected until data alignment fix)
```

---

## 📊 SUCCESS CRITERIA & DELIVERABLES

### Task 1 Success Criteria:
- [ ] Data alignment root cause documented
- [ ] RTL Frame_Builder data generation fixed OR testbench expectations aligned  
- [ ] uart_axi4_basic_test: UVM_ERROR count 45 → 0
- [ ] TEST PASSED status achieved

### Task 2 Success Criteria:
- [ ] 6 CRC unit test cases implemented and passing
- [ ] Python reference validation matching RTL results
- [ ] Test execution time < 30 seconds
- [ ] Documentation with CRC validation report

### Task 3 Success Criteria:
- [ ] Protocol test suite with coverage collection ≥80%
- [ ] Coverage report generated in HTML format
- [ ] Performance metrics documented
- [ ] All major protocol scenarios tested

### Final Deliverables:
1. **Git Commits**: Each task completion with descriptive commit messages
2. **Documentation**: Updated in `docs/` directory with analysis and results  
3. **Test Reports**: Execution logs and coverage analysis
4. **Code Quality**: Follow SystemVerilog coding standards, proper comments
5. **Handover Report**: Summary of changes, remaining issues, future recommendations

---

## 🚨 ESCALATION & SUPPORT

### Common Issues & Solutions:
1. **DSIM License Issues**: Check `%DSIM_LICENSE%` environment variable
2. **PowerShell Execution Errors**: Verify execution policy with `Get-ExecutionPolicy`
3. **Git Conflicts**: Use `git status` and `git stash` before major changes
4. **Compilation Errors**: Check `dsim.log` in sim/uvm directory

### Contact Information:
- **Project Lead**: GitHub Copilot (AI Assistant)
- **Documentation**: All project docs in `docs/` directory
- **Previous Work**: Git commit history with detailed messages
- **Emergency Contact**: Escalate via development environment if critical issues occur

### Development Diary:
Record all insights, issues, and solutions in `docs/diary_$(Get-Date -Format 'yyyyMMdd').md` following established format.

---

**END OF HANDOVER DOCUMENT**  
*Generated: September 20, 2025*  
*Next Review: Upon Task Completion*