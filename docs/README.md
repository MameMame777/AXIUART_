# AXIUART Documentation

This directory contains the project documentation for the AXIUART SystemVerilog implementation.

## Essential Documentation (Maintained in Git)

### Core Project Documentation
- **`design_overview.md`** - High-level system architecture and design principles
- **`system_architecture.md`** - Detailed system architecture documentation
- **`data_flow_diagram.md`** - Data flow and protocol documentation

### Verification and Testing
- **`uvm_verification_plan.md`** - UVM verification strategy and methodology
- **`uvm_testplan.md`** - Detailed UVM test plan and coverage goals
- **`verification_procedure.md`** - Standard verification procedures
- **`rx_tx_verification_plan.md`** - UART RX/TX specific verification plan
- **`hardware_verification_checklist.md`** - Hardware verification checklist

### Protocol and Interface Specifications
- **`uart_axi4_protocol.md`** - UART to AXI4 protocol specification
- **`uart_response_timing_spec.md`** - UART timing specifications
- **`register_map.md`** - Register map and memory layout
- **`protocol_constants_mapping.csv`** - Protocol constants mapping table

### Driver and Software
- **`com_driver_specification.md`** - COM driver specification
- **`com_driver_implementation_plan.md`** - Driver implementation strategy

### Setup and Quick Start
- **`QUICK_START.md`** - Quick start guide for new developers
- **`run_guide.md`** - Simulation and build instructions
- **`execution_environment_status.md`** - Development environment status

### Development Guidelines
- **`optimal_error_injection_design.md`** - Error injection methodology
- **`protocol_verification_design.md`** - Protocol verification design
- **`axi_verification_strategy_critical.md`** - AXI verification strategy

## Local Development Documentation (Git Ignored)

The `local/` directory contains temporary development documents, diary entries, and debugging notes that are specific to individual development sessions. These files are excluded from git tracking to keep the repository clean.

### Local Documentation Types
- Daily development diaries (`diary_*.md`)
- Debugging session notes (`*_debug_*.md`)
- Temporary analysis reports (`*_analysis_*.md`)
- Work-in-progress documentation (`*_wip_*.md`)
- Emergency fixes and patches (`emergency_*.md`)
- Personal development notes

## Documentation Guidelines

### For Core Documentation
- Write in English
- Use Markdown format
- Include clear headers and structure
- Add appropriate cross-references
- Update when making significant changes

### For Local Documentation
- Store in `docs/local/` directory
- Use descriptive filenames with dates
- Include sufficient context for future reference
- Regular cleanup recommended

## File Organization

```
docs/
├── README.md                           # This file
├── design_overview.md                  # Core design documentation
├── uvm_verification_plan.md           # Verification strategy
├── QUICK_START.md                     # Getting started guide
├── local/                             # Git ignored local files
│   ├── diary_*.md                     # Development diaries
│   ├── *_debug_*.md                   # Debug session notes
│   └── *_analysis_*.md                # Temporary analysis
└── [other core documentation files]
```

## Contributing to Documentation

When adding new documentation:
1. Determine if it's core project documentation or temporary/personal
2. Core documentation goes in `docs/` root
3. Temporary/personal documentation goes in `docs/local/`
4. Update this README if adding new core documentation categories
5. Follow naming conventions and formatting guidelines

## Document Status

Last updated: October 13, 2025
Documentation cleanup completed: Moved 116 temporary files to local directory