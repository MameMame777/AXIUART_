# UART AXI4 Bridge SystemVerilog UVM Verification Project

## 🚀 Primary Simulation Method: Model Context Protocol (MCP) Server

This project uses a **true Model Context Protocol (MCP) server** for all UVM simulation tasks, providing standard-compliant tool integration and automated verification workflows.

### Quick Start with MCP Server

1. **Start MCP Server**:
```powershell
cd e:\Nautilus\workspace\fpgawork\AXIUART_
python mcp_server/dsim_uvm_server.py --workspace .
```

2. **Use MCP Tools** (via any MCP client):
- `run_uvm_simulation`: Execute UVM tests with comprehensive options
- `check_dsim_environment`: Verify DSIM setup and environment
- `list_available_tests`: Show all available test cases
- `get_simulation_logs`: Retrieve detailed simulation results
- `generate_coverage_report`: Create coverage analysis reports

### MCP Server Benefits
- **Standards Compliant**: Official Model Context Protocol implementation
- **Cross-Platform**: Python-based, works everywhere
- **Tool Integration**: Compatible with any MCP client
- **Automated Workflows**: Streamlined simulation and analysis
- **Comprehensive Logging**: Detailed results and debugging info

## 📋 Project Overview

A comprehensive SystemVerilog verification environment for UART-AXI4 bridge IP, featuring:
- **UVM 1.2** testbench with modular agent architecture
- **SystemVerilog Assertions (SVA)** for protocol verification
- **DSIM simulator** integration with waveform analysis
- **Coverage-driven verification** with automated reporting
- **Model Context Protocol** server for tool integration

## 🏗️ Architecture

```text
AXIUART_/
├── rtl/                           # RTL source files
│   ├── AXIUART_Top.sv            # Top-level system integration
│   ├── Uart_Axi4_Bridge.sv      # UART-AXI4 bridge core
│   ├── Register_Block.sv         # Internal register block
│   ├── Uart_Rx.sv               # UART receiver
│   ├── Uart_Tx.sv               # UART transmitter
│   └── Frame_Parser.sv          # UART frame parsing
├── sim/                          # Simulation environment
│   ├── uvm/                     # UVM testbench
│   │   ├── uart_axi4_tb_top.sv # Testbench top
│   │   ├── uart_axi4_test_pkg.sv # Test package
│   │   ├── uart_axi4_env.sv    # UVM environment
│   │   ├── uart_agents/         # UVM agents
│   │   └── tests/               # Test cases
│   └── assertions/              # SVA modules
├── mcp_server/                  # Model Context Protocol server
│   ├── dsim_uvm_server.py      # MCP server implementation
│   ├── setup.py                # Environment setup
│   └── README.md               # MCP documentation
└── docs/                       # Project documentation
```

## 🚀 MCP Server Usage

### Primary Workflow

```powershell
# 1. Setup MCP Server Environment
cd e:\Nautilus\workspace\fpgawork\AXIUART_
python mcp_server/setup.py

# 2. Start MCP Server
python mcp_server/dsim_uvm_server.py --workspace .

# 3. Use MCP Tools (via MCP client)
# - run_uvm_simulation
# - check_dsim_environment  
# - list_available_tests
# - get_simulation_logs
# - generate_coverage_report
```

### MCP Tool Examples

```json
{
  "name": "run_uvm_simulation",
  "arguments": {
    "test_name": "uart_axi4_write_protocol_test",
    "mode": "run",
    "verbosity": "UVM_MEDIUM",
    "waves": true,
    "coverage": true,
    "seed": 42
  }
}
```

## 🔧 Alternative: Legacy PowerShell Scripts

For environments where MCP server is not available, traditional PowerShell scripts are provided:

```powershell
# Direct script execution
cd sim/exec
.\run_uvm.ps1 -TestName "uart_axi4_basic_test" -Waves on -Coverage on
```

## 📊 Verification Status

| Test Case | Status | Coverage | Notes |
|-----------|--------|----------|-------|
| Basic Write Protocol | ✅ PASS | 95% | Full AXI4 write sequence |
| Basic Read Protocol | ✅ PASS | 92% | Full AXI4 read sequence |
| Error Injection | ✅ PASS | 88% | Parity/framing errors |
| Bridge Control | ✅ PASS | 90% | Enable/disable sequences |

## 🛠️ Development Environment

### Required Tools
- **DSIM**: v20240422.0.0 (Metrics Design Automation)
- **Python**: 3.8+ with MCP package support
- **SystemVerilog**: IEEE 1800-2017 compliant
- **UVM**: Version 1.2

### Environment Variables
```powershell
$env:DSIM_HOME = "C:\Users\Nautilus\AppData\Local\metrics-ca\dsim\20240422.0.0"
$env:DSIM_LICENSE = "path\to\license.dat"  # if required
```

## 📈 Coverage Analysis

Generate comprehensive coverage reports using the MCP server:

```json
{
  "name": "generate_coverage_report",
  "arguments": {
    "format": "html",
    "output_dir": "coverage_report"
  }
}
```

## 🔍 Debugging Workflow

1. **Start MCP Server**: Automatic environment validation
2. **Run Tests**: Comprehensive logging and waveform capture  
3. **Analyze Results**: Automated report generation
4. **Debug Issues**: SVA assertion analysis and waveform review

## 📝 Documentation

- [`mcp_server/README.md`](mcp_server/README.md) - MCP server implementation details
- [`docs/design_overview.md`](docs/design_overview.md) - System architecture
- [`docs/verification_plan.md`](docs/verification_plan.md) - UVM verification strategy
- [`docs/uvm_verification_plan.md`](docs/uvm_verification_plan.md) - Detailed test plans

## 🎯 Key Features

### RTL Implementation
- ✅ Full UART-AXI4 bridge with configurable parameters
- ✅ Comprehensive frame parsing and protocol conversion
- ✅ Register block with standard AXI4-Lite interface
- ✅ Error detection and handling mechanisms

### Verification Environment  
- ✅ UVM 1.2 compliant testbench architecture
- ✅ Modular agent design for reusability
- ✅ SystemVerilog assertions for protocol checking
- ✅ Coverage-driven verification methodology
- ✅ Model Context Protocol server integration

### Automation & Tools
- ✅ MCP server for standardized tool integration
- ✅ Automated environment setup and validation
- ✅ Comprehensive logging and reporting
- ✅ VS Code integration with task automation
- ✅ Cross-platform Python-based workflows

## 🚀 Getting Started

1. **Clone the repository**
2. **Setup MCP server**: `python mcp_server/setup.py`
3. **Start MCP server**: `python mcp_server/dsim_uvm_server.py --workspace .`
4. **Run tests via MCP client** or use VS Code tasks
5. **Review results** in generated reports

For detailed setup instructions, see the [MCP Server README](mcp_server/README.md).