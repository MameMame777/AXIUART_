# UVM Directory Structure - Organized Layout

## Overview

The UVM verification environment has been organized into a hierarchical directory structure to improve maintainability, navigation, and component isolation.

## Directory Structure

```
sim/uvm/
├── interfaces/           # SystemVerilog Interfaces
│   ├── axi4_lite_if.sv  # AXI4-Lite interface definition
│   └── uart_if.sv       # UART interface definition
│
├── packages/            # UVM Packages
│   ├── axi4_lite_agent_pkg.sv    # AXI4-Lite agent package
│   ├── uart_agent_pkg.sv         # UART agent package  
│   ├── sequence_lib_pkg.sv       # Sequence library package
│   └── uart_axi4_test_pkg.sv     # Test package
│
├── agents/              # UVM Agents
│   ├── axi4_lite/       # AXI4-Lite Agent Components
│   │   ├── axi4_lite_agent.sv       # AXI4-Lite agent
│   │   ├── axi4_lite_driver.sv      # AXI4-Lite driver
│   │   ├── axi4_lite_monitor.sv     # AXI4-Lite monitor
│   │   ├── axi4_lite_sequencer.sv   # AXI4-Lite sequencer
│   │   └── axi4_lite_transaction.sv # AXI4-Lite transaction
│   │
│   └── uart/            # UART Agent Components
│       ├── uart_agent.sv      # UART agent
│       ├── uart_driver.sv     # UART driver
│       ├── uart_monitor.sv    # UART monitor
│       ├── uart_sequencer.sv  # UART sequencer
│       └── uart_transaction.sv # UART transaction
│
├── sequences/           # UVM Sequences
│   ├── basic_func_sequence.sv      # Basic functionality sequence
│   ├── error_injection_sequence.sv # Error injection sequence
│   ├── performance_test_sequence.sv # Performance test sequence
│   │
│   ├── axi4_lite/       # AXI4-Lite Specific Sequences
│   │   └── axi4_lite_base_sequence.sv # AXI4-Lite base sequence
│   │
│   └── uart/            # UART Specific Sequences
│       ├── uart_base_sequence.sv     # UART base sequence
│       ├── uart_loopback_sequence.sv # UART loopback sequence
│       └── uart_physical_sequence.sv # UART physical sequence
│
├── env/                 # UVM Environment
│   ├── uart_axi4_env.sv         # Main environment class
│   ├── uart_axi4_env_config.sv  # Environment configuration
│   ├── uart_axi4_coverage.sv    # Functional coverage
│   └── uart_axi4_scoreboard.sv  # Verification scoreboard
│
└── tests/               # UVM Test Classes
    ├── uart_axi4_base_test.sv # Base test class
    └── uart_axi4_tests.sv     # Derived test classes
```

## Benefits of This Organization

### 1. **Improved Maintainability**
- Each component type is clearly separated
- Related files are grouped together
- Easy to locate specific functionality

### 2. **Enhanced Navigation**
- Logical directory hierarchy
- Consistent naming conventions
- Clear component relationships

### 3. **Better Collaboration**
- Team members can easily find components
- Reduces merge conflicts
- Clear ownership of component areas

### 4. **Scalability**
- Easy to add new agents or sequences
- Component isolation prevents interference
- Supports large verification environments

## Component Descriptions

### **Interfaces**
Contains SystemVerilog interface definitions that define the signals and protocols for communication between testbench and DUT.

### **Packages**
UVM packages that define classes, types, and compile-time configurations for each verification component.

### **Agents**
Complete UVM agent implementations with transaction, sequencer, driver, monitor, and agent classes organized by protocol.

### **Sequences**
UVM sequence classes organized by functionality:
- **Common sequences**: Cross-protocol test scenarios
- **Protocol-specific**: Sequences targeting specific interfaces

### **Environment**
Top-level environment components including configuration, coverage collection, and scoreboarding.

### **Tests**
UVM test classes that configure the environment and coordinate test execution.

## DSIM Configuration Updates

The `dsim_config.f` file has been updated to include all organized directories in the include path:

```
+incdir+sim/uvm/interfaces
+incdir+sim/uvm/packages  
+incdir+sim/uvm/agents
+incdir+sim/uvm/agents/axi4_lite
+incdir+sim/uvm/agents/uart
+incdir+sim/uvm/sequences
+incdir+sim/uvm/sequences/axi4_lite
+incdir+sim/uvm/sequences/uart
+incdir+sim/uvm/env
+incdir+sim/uvm/tests
```

## File Compilation Order

The organized structure maintains proper compilation dependencies:

1. **Interfaces** - Protocol definitions
2. **Packages** - Type and class definitions  
3. **Agents** - Verification components
4. **Sequences** - Test stimulus generation
5. **Environment** - Testbench coordination
6. **Tests** - Test execution control

## Migration Notes

- All existing functionality is preserved
- File paths in DSIM configuration updated
- Include paths expanded for new directory structure
- No changes required to individual file contents

This organized structure provides a professional, maintainable verification environment suitable for complex FPGA verification projects.
