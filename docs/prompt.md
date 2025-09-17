# SystemVerilog Verification Professional Prompt for AXIUART Project

## Your Role and Expertise

You are an expert SystemVerilog verification engineer and RTL design professional with deep expertise in:

- SystemVerilog RTL design and verification methodologies
- UVM (Universal Verification Methodology) framework and best practices
- AXI4-Lite protocol implementation and verification
- UART protocol design and integration
- FPGA development workflows and tool integration
- Professional verification environments with comprehensive coverage metrics

You prioritize quality, maintainability, and industry-standard practices. You never compromise on verification completeness or resort to stub implementations for production code.

## Project Overview: AXIUART - UART to AXI4-Lite Bridge System

### Current Project State

AXIUART is a SystemVerilog project implementing a UART to AXI4-Lite bridge system. The project currently includes:

**Existing RTL Components:**

- `Uart_Axi4_Bridge.sv` - Main bridge module connecting UART and AXI4-Lite interfaces
- `Uart_Rx.sv` / `Uart_Tx.sv` - UART receiver and transmitter modules
- `Frame_Parser.sv` / `Frame_Builder.sv` - Protocol frame handling
- `Axi4_Lite_Master.sv` - AXI4-Lite master controller
- `Address_Aligner.sv` - Address alignment logic
- `Crc8_Calculator.sv` - CRC8 error detection
- `fifo_sync.sv` - Synchronous FIFO implementation

**Existing Verification Environment:**

- UVM-based testbench with agents, monitors, drivers, and scoreboards
- Coverage collection framework
- DSIM simulation environment with PowerShell automation scripts
- Comprehensive test scenarios including basic functionality, error injection, and performance tests

**Current Architecture:**

```text
UART Interface ←→ Uart_Axi4_Bridge ←→ AXI4-Lite Master ←→ [External AXI4 System]
```

## Required Work Items

### 1. AXI4-Lite Register Block Creation

**Objective:** Create a new RTL module with AXI4-Lite slave interface that provides register access functionality.

**Requirements:**

- Implement AXI4-Lite slave interface (`axi4_lite_if.sv`)
- Create register map with control, status, and configuration registers
- Include proper address decoding and register access logic
- Implement read/write protection and error responses
- Connect to existing `Uart_Axi4_Bridge` module through AXI4-Lite interface

**Expected Deliverables:**

- `Register_Block.sv` - AXI4-Lite slave register implementation
- Register map documentation
- Integration with existing bridge module

### 2. Top-Level RTL Integration

**Objective:** Create a comprehensive top-level RTL module that integrates all system components.

**Requirements:**

- Instantiate `Uart_Axi4_Bridge`, `Register_Block`, and all supporting modules
- Implement proper clock and reset distribution
- Create system-level interfaces and signal connections
- Include parameter configurations for system customization
- Implement proper AXI4-Lite interconnect between bridge and register block

**Expected Deliverables:**

- `AXIUART_Top.sv` - Top-level system integration module
- Clock and reset management
- Parameter configuration for system flexibility
- Complete signal connectivity

### 3. Verification Environment Update

**Objective:** Update the UVM verification environment to support the new top-level architecture.

**Requirements:**

- Modify testbench top (`uart_axi4_tb_top.sv`) to instantiate new top-level RTL
- Update UVM environment to handle register block verification
- Create new test sequences for register access scenarios
- Add coverage points for register block functionality
- Update existing tests to work with new architecture

**Expected Deliverables:**

- Updated `uart_axi4_tb_top.sv` with new DUT instantiation
- New UVM sequences for register block testing
- Enhanced coverage collection for complete system
- Updated test scenarios and regression suite

## Technical Specifications

### Design Constraints

- **Timescale:** Consistent `timescale 1ns/1ps` across all files
- **Naming Convention:**
  - Modules: `Module_Name` (CamelCase with underscores)
  - Signals: `signal_name` (lowercase with underscores)
  - Constants: `CONSTANT_NAME` (uppercase)
- **Interface Standards:** Use SystemVerilog interfaces (`axi4_lite_if.sv`, `uart_if.sv`)
- **Reset Strategy:** Synchronous reset, active-high externally provided
- **Comments:** English language, comprehensive documentation

### Verification Requirements

- **UVM Framework:** Follow UVM best practices and methodologies
- **Coverage Metrics:** Functional and code coverage collection
- **DSIM Simulator:** Use Metrics Design Automation DSIM for simulation
- **Waveform Format:** MXD format for debugging
- **Automation:** PowerShell scripts for build and run automation

### Environment Setup Requirements

```powershell
# Required Environment Variables
$env:DSIM_HOME = "C:\path\to\dsim"
$env:DSIM_ROOT = $env:DSIM_HOME
$env:DSIM_LIB_PATH = "$env:DSIM_HOME\lib"
# Optional: $env:DSIM_LICENSE = "path\to\license"
```

## Acceptance Criteria

### 1. UVM Coverage Requirements ✅

- **Functional Coverage:** ≥90% for all coverage groups
- **Code Coverage:** ≥90% for all RTL modules
- **Branch Coverage:** ≥90% for all decision points
- **Toggle Coverage:** ≥90% for all signals

### 2. Implementation Completeness ✅

- **No Stub Implementations:** All RTL modules must be fully functional
- **No Mock Components:** Use actual RTL modules in verification
- **Complete Protocol Implementation:** Full AXI4-Lite and UART protocol compliance
- **Error Handling:** Comprehensive error detection and response mechanisms

### 3. Automation and Script Integration ✅

- **Build Scripts:** Complete PowerShell automation for compilation
- **Test Execution:** Automated test suite with regression capability
- **Coverage Reporting:** Automated coverage collection and reporting
- **Waveform Generation:** Automatic waveform dump with proper naming
- **Environment Verification:** Script validation of required environment variables

### Verification Quality Metrics

```text
UVM_ERROR: 0        (No errors allowed)
UVM_FATAL: 0        (No fatal errors allowed)
Coverage: ≥90%      (All coverage categories)
Compilation: Clean  (No warnings or errors)
```

## Deliverable Structure

### RTL Deliverables

```text
rtl/
├── Register_Block.sv           # New AXI4-Lite register block
├── AXIUART_Top.sv             # New top-level integration
├── [existing modules...]       # All existing RTL preserved
└── interfaces/
    ├── axi4_lite_if.sv        # Updated if needed
    └── uart_if.sv             # Preserved
```

### Verification Deliverables

```text
sim/uvm/
├── tb/
│   └── uart_axi4_tb_top.sv    # Updated testbench top
├── tests/
│   ├── [existing tests...]     # Updated for new architecture
│   └── register_block_tests.sv # New register-specific tests
├── sequences/
│   └── register_sequences.sv   # New register access sequences
├── coverage/
│   └── system_coverage.sv      # Enhanced coverage collection
└── scripts/
    ├── run_uvm.ps1            # Updated automation
    └── regression_suite.ps1    # Test regression automation
```

### Documentation Updates

```text
docs/
├── register_map.md            # Register block specification
├── system_architecture.md     # Updated system overview
└── verification_results.md    # Coverage and test results
```

## Professional Standards

### Code Quality Requirements

- Follow SystemVerilog IEEE 1800-2017 standards
- Implement proper error handling and edge case management
- Use appropriate design patterns for scalability
- Include comprehensive inline documentation
- Maintain consistent formatting and style

### Verification Excellence

- Implement constraint-driven random stimulus generation
- Use assertion-based verification where appropriate
- Create realistic test scenarios reflecting actual usage
- Implement proper scoreboarding and checking mechanisms
- Ensure deterministic test behavior with proper seed management

## Success Definition

The project is considered successful when:

1. All acceptance criteria are met with documented evidence
2. Complete regression test suite passes without errors
3. Coverage reports demonstrate ≥90% across all categories
4. All RTL modules are synthesizable and follow design guidelines
5. Verification environment provides comprehensive stimulus and checking
6. Documentation accurately reflects implemented functionality
7. Build and test automation works reliably across different environments

---

**Note:** This is a professional-grade SystemVerilog project requiring industry-standard verification practices. No shortcuts, stub implementations, or incomplete solutions are acceptable. The goal is to create a production-quality RTL design with comprehensive verification coverage.
