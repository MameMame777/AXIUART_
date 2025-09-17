# AXIUART - SystemVerilog UART to AXI4-Lite Bridge

## Overview

AXIUART is a SystemVerilog implementation of a UART to AXI4-Lite bridge that enables communication between a UART interface and an AXI4-Lite bus. This project provides a complete RTL implementation with comprehensive UVM-based verification.

## Project Structure

```text
AXIUART_/
├── rtl/                    # RTL source files
│   ├── Address_Aligner.sv  # Address alignment logic
│   ├── Axi4_Lite_Master.sv # AXI4-Lite master controller
│   ├── Crc8_Calculator.sv  # CRC8 calculation module
│   ├── fifo_sync.sv        # Synchronous FIFO implementation
│   ├── Frame_Builder.sv    # UART frame construction
│   ├── Frame_Parser.sv     # UART frame parsing
│   ├── Uart_Axi4_Bridge.sv # Top-level bridge module
│   ├── Uart_Rx.sv          # UART receiver
│   ├── Uart_Tx.sv          # UART transmitter
│   └── interfaces/         # SystemVerilog interfaces
├── sim/                    # Simulation environment
│   └── uvm/               # UVM testbench
├── docs/                   # Documentation
├── reference/              # Reference materials
└── scripts/               # Build and run scripts
```

## Features

- **UART Interface**: Configurable baud rate, data bits, parity, and stop bits
- **AXI4-Lite Master**: Complete AXI4-Lite protocol implementation
- **Frame Protocol**: Custom frame format with CRC8 error detection
- **Address Alignment**: Automatic address alignment for AXI transactions
- **FIFO Buffers**: Synchronous FIFOs for data buffering
- **UVM Verification**: Comprehensive testbench with coverage metrics

## Protocol Description

The bridge uses a custom frame protocol over UART to encapsulate AXI4-Lite transactions:

- Frame format includes command type, address, data, and CRC8 checksum
- Supports both read and write operations
- Error detection and handling through CRC validation
- Flow control through handshaking mechanisms

## Quick Start

### Prerequisites

- **DSIM Simulator**: Metrics Design Automation DSIM simulator
- **SystemVerilog Support**: IEEE 1800-2017 compliant simulator
- **UVM Library**: Universal Verification Methodology library
- **PowerShell**: For running simulation scripts (Windows)

### Environment Setup

1. Set required environment variables:

   ```powershell
   $env:DSIM_HOME = "C:\path\to\dsim"
   $env:DSIM_ROOT = $env:DSIM_HOME
   $env:DSIM_LIB_PATH = "$env:DSIM_HOME\lib"
   # Optional: $env:DSIM_LICENSE = "path\to\license"
   ```

2. Navigate to simulation directory:

   ```powershell
   cd sim/uvm
   ```

3. Run UVM tests:

   ```powershell
   .\run_uvm.ps1
   ```

### Running Tests

The project includes several UVM test scenarios:

- **Basic Functional Tests**: Verify core UART-AXI bridge functionality
- **Protocol Tests**: Validate frame protocol and error handling
- **Performance Tests**: Measure throughput and latency
- **Error Injection Tests**: Test error detection and recovery

### Waveform Analysis

Simulation results are automatically saved in MXD format:

- Waveform files: `*_test_*.mxd`
- Coverage reports: `coverage_report/`
- Simulation logs: `*.log`

## Documentation

- `docs/design_overview.md` - Architecture and design details
- `docs/uart_axi4_protocol.md` - Protocol specification
- `docs/uvm_testplan.md` - Verification plan and test cases
- `docs/run_guide.md` - Detailed simulation guide

## Development Guidelines

### Coding Standards

- **Naming Convention**:
  - Modules: `Module_Name` (CamelCase with underscores)
  - Signals: `signal_name` (lowercase with underscores)
  - Constants: `CONSTANT_NAME` (uppercase with underscores)
- **File Extensions**: Use `.sv` for SystemVerilog files
- **Timescale**: Consistent `timescale 1ns/1ps` across all files
- **Comments**: English language, comprehensive documentation
- **Indentation**: 4 spaces, no tabs

### Verification Approach

- **UVM-based Verification**: Complete UVM testbench environment
- **Coverage-Driven**: Functional and code coverage metrics
- **Constrained Random Testing**: Stimulus generation with constraints
- **Assertion-Based Verification**: SVA assertions for protocol checking

## Security Considerations

This repository follows security best practices:

- No sensitive credentials or license keys are committed
- Personal paths and system-specific configurations are excluded
- Build artifacts and temporary files are gitignored
- All documentation and code use non-sensitive examples

## Contributing

1. Follow the established coding guidelines
2. Add comprehensive tests for new features
3. Update documentation for any interface changes
4. Ensure all tests pass before submitting changes
5. Use appropriate commit messages following conventional format

## License

Please ensure proper licensing compliance for all tools and IP used in this project.

## Support

For questions or issues:

1. Check the documentation in the `docs/` directory
2. Review existing test cases for usage examples
3. Examine the reference materials in `reference/`

## Version History

- **Initial Release**: SystemVerilog RTL implementation with UVM testbench
- **Current**: Comprehensive verification environment with coverage metrics