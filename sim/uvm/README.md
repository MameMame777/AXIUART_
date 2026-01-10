# AXIUART Simplified UVM Environment

## Overview

The AXIUART UVM environment has been simplified following the UBUS reference implementation pattern, reducing complexity while maintaining verification coverage.

## Directory Structure

```
sim/
├── tests/                       # Test definitions (December 2024 refactoring)
│   ├── axiuart_test_pkg.sv     # Test package
│   ├── axiuart_base_test.sv    # Base test
│   ├── axiuart_basic_test.sv   # Basic test
│   ├── axiuart_reset_test.sv   # Reset test
│   └── axiuart_reg_rw_test.sv  # Register R/W test
│
└── uvm/
    ├── sv/                      # All UVM components (UBUS style)
    │   ├── axiuart_pkg.sv       # Main package (single file)
    │   ├── uart_transaction.sv  # Transaction
    │   ├── uart_monitor.sv      # UART monitor
    │   ├── uart_driver.sv       # UART driver
    │   ├── uart_sequencer.sv    # UART sequencer
    │   ├── uart_agent.sv        # UART agent
    │   ├── axi4_lite_monitor.sv # AXI monitor (observation only)
    │   ├── axiuart_scoreboard.sv# Scoreboard
    │   └── axiuart_env.sv       # Top environment
    │
    └── tb/                      # Testbench
        ├── axiuart_tb_top.sv    # Top module
        └── dsim_config.f        # DSIM file list
```

## Simplification Highlights

### 1. File Count Reduction
- **Previous environment**: 49 SystemVerilog files (distributed across agents/, env/, scoreboard/, analysis/)
- **New environment**: 14 files (organized in sv/, tb/, tests/)
  - UVM components: 10 files (sv/)
  - Testbench: 1 file (tb/)
  - Test definitions: 4 files (tests/ - December 2024 refactoring)

### 2. Removed Components

#### Duplicate Scoreboards
- `uart_axi4_enhanced_scoreboard.sv` → Removed
- `uart_axi4_scoreboard.sv` → Merged
- `correlation_engine.sv` → Integrated

#### Duplicate Coverage
- `uart_axi4_phase3_coverage.sv` → Removed
- `system_coverage.sv` → Removed
- `axiuart_cov_pkg.sv` → Removed

#### Excessive Separation
- `uart_axi4_predictor.sv` → Removed
- `uart_axi4_error_detector.sv` → Removed
- `bridge_status_monitor.sv` → Removed
- `independent_verification_monitor.sv` → Removed

#### Configuration Classes
- `uart_axi4_env_config.sv` → Removed (uses simple VIF configuration only)

### 3. Transaction Simplification
- **Previous**: 158 lines (20+ fields, complex constraints)
- **New**: 47 lines (essential fields only)

### 4. Monitor Simplification
- **Previous**: 890 lines (complex RX/TX state machines)
- **New**: 78 lines (simple frame collection)

### 5. Driver Simplification
- **Previous**: 351 lines (dynamic baud rate, reset handling, complex flow control)
- **New**: 98 lines (basic 8N1 format transmission)

### 6. Environment Simplification
- **Previous**: 191 lines (multiple analysis components, complex connections)
- **New**: 68 lines (Agent + Monitor + Scoreboard only)

## Register Map Management (December 2024)

### Using Auto-Generated Register Package

UVM tests use register constants from `axiuart_reg_pkg.sv` (auto-generated).

**Usage:**
```systemverilog
// sim/tests/axiuart_reg_rw_test.sv
import axiuart_reg_pkg::*;  // Import generated package

class axiuart_reg_rw_test extends axiuart_base_test;
  task main_phase(uvm_phase phase);
    // Use generated constants (no hardcoded addresses)
    uart_seq.write_then_read(REG_TEST_0, 32'h11111111);  // ✓ Correct
    uart_seq.write_then_read(32'h1020, 32'h11111111);    // ✗ Avoid
  endtask
endclass
```

**Regeneration:**
```bash
python software/axiuart_driver/tools/gen_registers.py \
  --in register_map/axiuart_registers.json
```

## Running Tests

### Using MCP Client (Recommended)

**Compile only:**
```bash
python mcp_server/mcp_client.py \
  --workspace e:\Nautilus\workspace\fpgawork\AXIUART_ \
  --tool run_uvm_simulation \
  --test-name axiuart_basic_test \
  --mode compile \
  --verbosity UVM_LOW \
  --timeout 180
```

**Full simulation:**
```bash
python mcp_server/mcp_client.py \
  --workspace e:\Nautilus\workspace\fpgawork\AXIUART_ \
  --tool run_uvm_simulation_batch \
  --test-name axiuart_basic_test \
  --verbosity UVM_MEDIUM \
  --waves \
  --timeout 300
```

### Using VS Code Tasks

Available tasks configured in `.vscode/tasks.json`:
- **DSIM: Run Basic Test (Compile Only - MCP)** - Compile-only pass
- **DSIM: Run Basic Test (Full Simulation - MCP)** - Full simulation with waveforms

## Test List

| Test | Description | Status |
|------|-------------|--------|
| `axiuart_basic_test` | Basic UART frame transmission test | ✅ Working |
| `axiuart_reset_test` | Reset sequence verification | ✅ Working |
| `axiuart_reg_rw_test` | Register read/write test | ✅ Working |

## Verification Strategy

### Coverage Goals
- UART protocol compliance
- Register interface functionality
- Reset behavior
- Error handling

### Assertion-Based Verification
Dedicated assertion modules (e.g., `Frame_Parser_Assertions`) are bound to RTL modules. Never embed assertions directly in RTL.

### Scoreboard Checking
- Compare UART transactions against AXI4-Lite transactions
- Verify protocol conversion accuracy
- Check CRC-8 calculation

## Environment Requirements

- **DSIM**: Version 2024.1 or later
- **UVM**: Version 1.2
- **Python**: 3.8+ (for MCP client)
- **Environment variables**: DSIM_HOME, DSIM_ROOT, DSIM_LIB_PATH, DSIM_LICENSE

## Known Issues

None. Previous issues with infinite monitor loops and subprocess environment inheritance have been resolved.

## Additional Resources

- [UVM Architecture](UVM_ARCHITECTURE.md) - Detailed testbench architecture
- [Register Map](../../software/axiuart_driver/REGISTER_MAP.md) - Auto-generated register documentation
- [RTL Documentation](../../rtl/README.md) - RTL module specifications
