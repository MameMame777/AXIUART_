# AXIUART SystemVerilog UVM Verification – Comprehensive Work Instructions

 _Last updated: 2025-10-07_  
_Target environment: DSIM v20240422.0.0 · SystemVerilog UVM 1.2 · Windows PowerShell_

---

## 1. Purpose and scope

- Guarantee a repeatable, high-quality verification workflow for the `AXIUART_Top` UART ⇔ AXI4-Lite bridge.
- Maintain `UVM_ERROR = 0` across all regressions while steadily improving toggle, expression, and functional coverage.
- Ensure every engineer can continue the effort without guesswork by providing precise, English-language guidance tied to the repository structure under `docs/`.

## 2. Working principles

SystemVerilog verification engineers on this project commit to the following:

1. **Quality first** – never ship partial fixes or temporary code. Use the RTL in `rtl/` exactly as the DUT.
2. **Evidence-based decisions** – track metrics (coverage, run time, waveform review) before declaring success.
3. **Consistency** – enforce `timescale 1ns / 1ps`, synchronous active-high reset, English comments, and four-space indentation in every SystemVerilog file.
4. **Security and confidentiality** – keep project data local, avoid hard-coded secrets, and prefer relative paths.
5. **Knowledge sharing** – document insights in `docs/diary_YYYYMMDD.md` and update this guide whenever processes change.

## 3. Project snapshot (07 Oct 2025)

### 3.0 Goal and status summary

- **Project goal**: Deliver a production-ready UART ⇔ AXI4-Lite bridge with UVM-driven verification that maintains `UVM_ERROR = 0`, achieves ≥ 60 % toggle coverage in Phase 4, and progresses toward the Phase 5 stretch targets without sacrificing stability.
- **Current status (2025-10-07)**:
  - **Major Breakthrough**: UVM environment fully functional with fixed-value test sequences executing successfully
  - **Critical Discovery**: CRC calculation errors and AXI alignment errors identified as blocking register access
  - **Technical Progress**: Fixed randomization failures in UVM, established working simulation framework
  - **Current Blockers**: CRC mismatches (recv=0x44 exp=0x12, recv=0x78 exp=0x4a) and alignment errors (CHECK_ALIGNMENT -> ERROR) preventing actual register verification
  - **FPGA Discrepancy**: Hardware contains test pattern generator (0xF0202200 + counter) instead of register functionality - RTL deployment required after simulation fixes
  - Tooling (`run_uvm.ps1`, MXD capture, coverage export) remains stable and fully operational

### 3.1 System overview

- UART runs at 115 200 bps and bridges to a 32-bit AXI4-Lite interface.
- The design includes a 64-entry synchronous FIFO, CRC8 protection, and custom framing.
- Verification uses SystemVerilog UVM 1.2 with DSIM and MXD waveform dumps.

### 3.2 Verification status

- **Stability**: UVM environment successfully established with fixed-value sequences, but CRC and alignment errors block register access verification
- **Infrastructure**: `run_uvm.ps1` proven stable and reliable for compilation, execution, waveform (MXD), and coverage export; environment variable checks mandatory
- **Current Technical Debt**: Must resolve CRC calculation implementation and AXI address alignment before proceeding to coverage improvement

### 3.3 Key achievements to date

- **UVM Framework Stabilization**: Fixed randomization issues, established working fixed-value test sequences
- **Comprehensive Debug Infrastructure**: Created detailed work instructions, phase-based checklists, and debugging procedures
- **Technical Discovery Process**: Systematic identification of CRC and alignment errors through targeted UVM simulation
- **Documentation Framework**: Established diary-based progress tracking and detailed status reporting
- **Git Management**: Comprehensive commit history with detailed technical discoveries and progress tracking

### 3.4 Latest regression evidence (07 Oct 2025)

- **UVM Test Execution**: `uart_axi4_register_simple_sequence` executes successfully in 51 seconds with `UVM_ERROR: 0`
- **Critical Findings**: CRC validation fails with specific mismatches, AXI alignment checking blocks register transactions
- **FPGA Investigation**: Python scripts confirm hardware implements test pattern generator instead of register functionality
- **Framework Validation**: Fixed-value sequences prove more reliable than randomization for debugging phase
- **Next Phase Readiness**: All tools and infrastructure prepared for systematic CRC and alignment debugging

## 4. Immediate priorities and success criteria (updated 07 Oct 2025)

The focus has shifted from scoreboard repairs to fundamental RTL debugging. CRC calculation and AXI alignment must be resolved before resuming coverage improvement work.

### 4.1 Investigation checklist — complete before implementing fixes

- [ ] **CRC Error Root Cause Analysis**: Review Frame_Parser.sv CRC implementation, verify CRC8 polynomial 0x07 usage, test with reference implementation
- [ ] **AXI Alignment Investigation**: Debug Address_Aligner module, confirm 32-bit boundary checking for register addresses 0x1000-0x100C
- [ ] **Register Access Path Verification**: Trace AXI transactions from alignment check through Register_Block to confirm signal propagation
- [ ] **FPGA vs RTL Reconciliation**: Document differences between hardware test pattern generator and RTL register implementation
- [ ] **Update Progress Documentation**: Record all findings in `docs/diary_20251007.md` before making RTL modifications

### 4.2 Action plan - Phase-based debugging approach

Progress through phases sequentially; do not advance until exit criteria are satisfied and documented. Archive all debug artifacts and maintain regression discipline.

#### Phase 1 – CRC Calculation Error Resolution (Owner: Verification, Priority: CRITICAL)

- [ ] **Step 1-1**: Analyze CRC error details from UVM logs (recv=0x44 exp=0x12, recv=0x78 exp=0x4a)
- [ ] **Step 1-2**: Review Frame_Parser.sv CRC implementation for polynomial, byte ordering, timing issues
- [ ] **Step 1-3**: Create Python reference implementation for CRC8 calculation with test vectors
- [ ] **Step 1-4**: Fix SystemVerilog CRC implementation based on reference comparison
- [ ] **Step 1-5**: Verify CRC fix with UVM simulation, confirm error elimination

**Exit Criteria**: UVM simulation shows no CRC errors, frame validation succeeds consistently

#### Phase 2 – AXI Alignment Error Resolution (Owner: Verification, Priority: CRITICAL)

- [ ] **Step 2-1**: Analyze alignment error details from UVM logs (CHECK_ALIGNMENT -> ERROR)
- [ ] **Step 2-2**: Review Address_Aligner.sv implementation for 32-bit boundary checking logic
- [ ] **Step 2-3**: Fix alignment validation for register addresses (0x1000, 0x1004, 0x1008, 0x100C)
- [ ] **Step 2-4**: Verify AXI Master state transitions handle alignment correctly
- [ ] **Step 2-5**: Confirm AXI transactions reach Register_Block after alignment fixes

**Exit Criteria**: UVM simulation shows successful AXI transactions to register addresses

#### Phase 3 – Register Access Verification (Owner: Verification, Priority: HIGH)

- [ ] **Step 3-1**: Confirm AXI write transactions properly update register values
- [ ] **Step 3-2**: Verify AXI read transactions return written values (0x44444444 test case)
- [ ] **Step 3-3**: Test data persistence across multiple read/write operations
- [ ] **Step 3-4**: Validate register access patterns match specification

**Exit Criteria**: Register write/read operations work correctly in UVM simulation

#### Phase 4 – FPGA Implementation (Owner: Hardware, Priority: MEDIUM)

- [ ] **Step 4-1**: Synthesize and implement corrected RTL design
- [ ] **Step 4-2**: Program FPGA with verified register functionality
- [ ] **Step 4-3**: Remove test pattern generator behavior from hardware
- [ ] **Step 4-4**: Execute comprehensive hardware validation tests

**Exit Criteria**: FPGA hardware returns written register values correctly

### 4.3 Active TODO governance

- **Phase-based progression**: Complete all steps in current phase before advancing
- **Quality gates**: Each phase requires successful UVM simulation with `UVM_ERROR = 0`
- **Documentation requirement**: Update diary after each completed step
- **Git discipline**: Commit after each major milestone with detailed messages
- **Regression safety**: Maintain backup copies before RTL modifications

## 5. Operating procedure

### 5.1 Pre-flight checks

- [ ] Confirm environment variables are set and valid (`DSIM_HOME`, `DSIM_ROOT`, `DSIM_LIB_PATH`, and, if needed, `DSIM_LICENSE`). Avoid hard-coded absolute paths in scripts.
- [ ] Verify structural consistency: every `.sv` file begins with `` `timescale 1ns / 1ps ``, DUT and testbench interfaces match bit widths (see `rtl/AXIUART_Top.sv` and `sim/uvm/tb/uart_axi4_tb_top.sv`), and UVM components follow the required naming scheme.
- [ ] Review `docs/register_map.md`, `docs/uart_axi4_protocol.md`, and prior diaries before modifying sequences.

Suggested PowerShell helper (run from the repository root):

```powershell
function Test-DsimEnvironment {
    $vars = "DSIM_HOME","DSIM_ROOT","DSIM_LIB_PATH"
    foreach ($name in $vars) {
        $value = [Environment]::GetEnvironmentVariable($name)
        if (-not $value) { throw "$name is not set." }
        if (-not (Test-Path $value)) { throw "$name path '$value' does not exist." }
    }
}

Test-DsimEnvironment
```

### 5.2 Running UVM tests (PowerShell in `sim/uvm/`)

Use `./run_uvm.ps1` for every compilation and simulation run; the checklist below keeps execution consistent and auditable.

- [ ] Open a PowerShell session in `sim/uvm/`.
- [ ] Compile and run the target regression:

```powershell
./run_uvm.ps1 -TestName uart_axi4_register_verification_test -Mode run -Seed 12345 -Verbose UVM_MEDIUM
```

- [ ] Perform compile-only passes when validating structural changes:

```powershell
./run_uvm.ps1 -Mode compile
```

- [ ] Use fixed-value sequences for debugging (avoid randomization during error resolution):

```powershell
./run_uvm.ps1 -TestName uart_axi4_register_verification_test
```

- [ ] Log each executed command, seed, runtime, and outcome in the daily diary.

Mandatory switches:

- [ ] Keep waveform dumping enabled (`-Waves on`) to generate MXD files under `archive/waveforms/` named after the test.
- [ ] Pass `-Coverage on` to capture `metrics.db`, then regenerate HTML via `dcreport.exe metrics.db -out_dir coverage_report`.
- [ ] Specify `-Verbose` level as needed (default `UVM_MEDIUM`) to aid debug while avoiding log bloat.

### 5.3 Post-run verification

- [ ] Inspect `dsim.log` for `UVM_ERROR`, `UVM_FATAL`, CRC errors, and alignment errors. Any occurrence requires immediate analysis.
- [ ] Confirm waveform generation (`archive/waveforms/<testname>.mxd`) and check size sanity (≥ 1 MB for substantive runs).
- [ ] Document specific error messages and their context in the debugging checklist.

## 6. Quality gates

| Gate | Definition | Evidence |
| ---- | ---------- | -------- |
| UVM stability | `UVM_ERROR = 0`, no `UVM_FATAL`, no compilation warnings | Test log excerpt, DSIM summary |
| CRC validation | No CRC mismatch errors in Frame_Parser | UVM log analysis, waveform confirmation |
| AXI alignment | No CHECK_ALIGNMENT errors for register addresses | UVM log analysis, signal trace verification |
| Register access | Successful write/read operations with data persistence | UVM test results, register value verification |
| Structural hygiene | `timescale 1ns / 1ps`, synchronous active-high reset, naming conventions enforced | Spot check scripts, code review |

Do not advance to the next phase until all gates for the current phase are satisfied and documented.

## 7. Debug-focused procedures (Phase 1-3)

### 7.1 CRC Error Debugging (Phase 1)

**Reference Implementation Pattern**:
```python
def crc8_calc(data, polynomial=0x07, init=0x00):
    crc = init
    for byte in data:
        crc ^= byte
        for _ in range(8):
            if crc & 0x80:
                crc = (crc << 1) ^ polynomial
            else:
                crc <<= 1
            crc &= 0xFF
    return crc
```

**Systematic Verification**:
- Compare Frame_Parser.sv implementation against reference
- Test with known data vectors from UVM test cases
- Verify byte ordering and bit manipulation logic
- Validate timing of CRC calculation in SystemVerilog

### 7.2 AXI Alignment Debugging (Phase 2)

**Address Validation Logic**:
- Register base: 0x1000 (4KB aligned)
- Valid addresses: 0x1000, 0x1004, 0x1008, 0x100C
- Alignment check: `(address & 0x3) == 0` for 32-bit access
- addr_ok signal generation verification

**State Machine Analysis**:
- Trace AXI Master state transitions
- Verify VALID/READY handshake behavior
- Confirm error response handling

### 7.3 Register Access Validation (Phase 3)

**Test Pattern Verification**:
- Write 0x44444444 to CONFIG register (0x1000)
- Read back and verify exact match
- Test all register addresses (0x1000-0x100C)
- Confirm data persistence across operations

## 8. Daily operations

### 8.1 Start-of-day checklist

- [ ] Review yesterday's diary entry and open phase status.
- [ ] Confirm current phase and next step in debugging sequence.
- [ ] Verify DSIM environment and UVM test infrastructure.

### 8.2 During debugging work

- [ ] Work in focused increments (≤ 2 hours per step).
- [ ] Record each test execution with specific error observations.
- [ ] Update phase checklist progress after each step.
- [ ] Document technical discoveries and hypothesis changes.

### 8.3 End-of-day deliverables

- [ ] Update phase completion status in todo management.
- [ ] Record specific error states and debugging progress in diary.
- [ ] Commit any RTL or UVM fixes with detailed commit messages.
- [ ] Document next-day continuation plan.

### 8.4 Progress report template (paste into the diary)

```markdown
## Debug Progress Report – YYYY-MM-DD

### Current Phase: [Phase 1: CRC | Phase 2: Alignment | Phase 3: Register Access]

### Completed today
- [x] Step X-Y: [Description]
- [x] [Specific accomplishment]

### Current status
- Error state: [Specific CRC/alignment errors remaining]
- UVM execution: [Success/failure with error count]
- Next step: [Specific next action]

### Technical discoveries
- [Specific finding about CRC implementation]
- [Specific finding about alignment logic]

### Plan for tomorrow
- [ ] Continue Step X-Y: [Specific action]
- [ ] [Next planned step]
```

## 9. Troubleshooting quick reference

| Symptom | Likely cause | Resolution |
| ------- | ------------ | ---------- |
| CRC mismatch errors | Frame_Parser implementation issue | Compare with Python reference, check byte ordering |
| CHECK_ALIGNMENT errors | Address_Aligner logic problem | Verify 32-bit boundary checking for 0x1000-0x100C |
| UVM randomization failures | Constraint conflicts in sequences | Use fixed-value sequences during debugging |
| No register response | AXI transaction not reaching Register_Block | Trace signal path through alignment and master logic |
| FPGA test pattern behavior | Hardware contains test generator | Deploy corrected RTL after simulation verification |
| MXD waveform missing | Simulation parameters or disk space | Verify `-Waves on` and storage availability |

Use focused debugging with one issue at a time; avoid parallel debugging of multiple error types.

## 10. Completion checklist and hand-off

Before closing a debugging phase or handing off to the next engineer:

- [ ] All phase steps completed with documented evidence.
- [ ] UVM simulation passes with `UVM_ERROR = 0` for the resolved issue area.
- [ ] Specific error messages no longer appear in logs.
- [ ] Waveform analysis confirms expected signal behavior.
- [ ] RTL changes committed with detailed technical explanation.
- [ ] Phase completion documented in diary with technical details.
- [ ] Next phase readiness verified (prerequisites satisfied).

## 11. Reference materials

- `docs/design_overview.md` – architectural summary
- `docs/register_map.md` – complete register definitions
- `docs/uart_axi4_protocol.md` – transaction framing rules
- `docs/work_status_summary_20251007.md` – current project status
- `docs/diary_20251007_uvm_completion_next_phase.md` – latest progress report
- `docs/debug_work_instructions_20251007.md` – detailed debugging procedures
- `docs/phase1_crc_checklist_20251007.md` – CRC debugging checklist
- `docs/phase2_alignment_checklist_20251007.md` – alignment debugging checklist
- [DSIM User Manual](https://help.metrics.ca/support/solutions/articles/154000141193)
- IEEE 1800.2-2017 UVM standard

---

**Current Focus**: Execute Phase 1 CRC debugging systematically using the detailed checklists and procedures. Advance only after achieving `UVM_ERROR = 0` with confirmed CRC error elimination.