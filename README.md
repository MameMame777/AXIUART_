# AXIUART - SystemVerilog UART to AXI4-Lite Bridge System

## Overview

AXIUART is a complete SystemVerilog implementation of a UART to AXI4-Lite bridge system that enables communication between UART interfaces and internal AXI4-Lite register blocks. This project provides a comprehensive RTL implementation with integrated system-level verification using UVM and Model Context Protocol (MCP) server integration.

## 🚀 New: Model Context Protocol (MCP) Server

This project now includes a **Model Context Protocol (MCP) server** for DSIM UVM simulation execution, providing standardized tool integration for enhanced development workflow.

### MCP Server Features
- **Standardized Interface**: Uses Model Context Protocol for consistent tool integration
- **DSIM Integration**: Direct execution of SystemVerilog UVM simulations
- **Environment Management**: Automated DSIM environment validation
- **Coverage Analysis**: Integrated coverage report generation
- **Cross-Platform**: Python-based server works across different platforms

### Quick Start with MCP Server

#### 1. Setup MCP Server
```powershell
cd mcp_server
python setup.py
```

#### 2. Start MCP Server
```powershell
python dsim_uvm_server.py --workspace .
```

#### 3. Available MCP Tools
- `run_uvm_simulation` - Execute DSIM simulations
- `check_dsim_environment` - Verify DSIM setup  
- `list_available_tests` - Discover UVM tests
- `get_simulation_logs` - Retrieve simulation results
- `generate_coverage_report` - Create coverage analysis

See [`mcp_server/README.md`](mcp_server/README.md) for detailed documentation.

## Project Structure

```text
AXIUART_/
├── rtl/                      # RTL source files
│   ├── AXIUART_Top.sv        # Top-level system integration
│   ├── Uart_Axi4_Bridge.sv  # UART-AXI4 bridge core
│   ├── Register_Block.sv     # Internal register block
│   ├── Uart_Rx.sv           # UART receiver
│   ├── Uart_Tx.sv           # UART transmitter
│   ├── Frame_Parser.sv      # UART frame parsing
│   ├── Frame_Builder.sv     # UART frame construction
│   ├── Axi4_Lite_Master.sv  # AXI4-Lite master controller
│   ├── Address_Aligner.sv   # Address alignment logic
│   ├── Crc8_Calculator.sv   # CRC8 calculation module
│   ├── fifo_sync.sv         # Synchronous FIFO implementation
│   └── interfaces/          # SystemVerilog interfaces
│       ├── uart_if.sv       # UART interface
│       └── axi4_lite_if.sv  # AXI4-Lite interface
├── mcp_server/              # Model Context Protocol server (NEW)
│   ├── dsim_uvm_server.py   # MCP server implementation
│   ├── setup.py             # MCP environment setup
│   ├── requirements.txt     # Python dependencies
│   ├── mcp_config.json      # MCP client configuration
│   └── README.md            # MCP server documentation
├── sim/                     # Simulation environment
│   └── uvm/                # UVM system-level testbench
│       ├── tb/             # Testbench top-level
│       ├── env/            # UVM environment
│       ├── agents/         # UVM agents
│       ├── tests/          # Test cases
│       └── sequences/      # Test sequences
├── docs/                    # Documentation
│   ├── verification_execution_plan.md    # 検証実行計画書
│   ├── verification_checklist.md         # 作業チェックリスト
│   ├── next_worker_instructions.md       # 次作業者への指示書
│   ├── design_overview.md               # システム設計概要
│   ├── uart_axi4_protocol.md           # プロトコル仕様
│   └── register_map.md                  # レジスタマップ
├── reference/               # Reference materials
└── scripts/                # Build and run scripts
```

## Architecture

### AXIUART_Top System Integration
The top-level system integrates multiple components to provide a complete UART-to-register bridge solution:

```
AXIUART_Top
├── Uart_Axi4_Bridge (UART Protocol Handler)
│   ├── Uart_Rx/Tx (115200 bps, 8N1)
│   ├── Frame_Parser/Builder (Protocol Processing)
│   ├── Axi4_Lite_Master (Internal AXI Master)
│   ├── fifo_sync (64-deep TX/RX FIFOs)
│   └── Crc8_Calculator (Error Detection)
└── Register_Block (Internal Register Map)
    └── AXI4-Lite Slave Interface
```

### Key System Features

- **Complete System Integration**: Self-contained UART-to-register bridge
- **Internal AXI4-Lite Bus**: 32-bit address/data with full protocol compliance
- **UART Interface**: 115200 bps, configurable parameters
- **Register Block**: Internal register map accessible via UART commands
- **System Status Monitoring**: Ready/Busy/Error status outputs
- **Frame Protocol**: Custom frame format with CRC8 error detection
- **FIFO Buffering**: 64-deep synchronous FIFOs for TX/RX
- **Address Alignment**: Automatic alignment for AXI transactions

### System Specifications

| Parameter | Value | Description |
|-----------|-------|-------------|
| Clock Frequency | 50 MHz | System clock |
| UART Baud Rate | 115200 bps | Configurable |
| AXI Bus Width | 32-bit | Address and data |
| FIFO Depth | 64 entries | TX/RX buffers |
| Max Frame Size | 16 bytes | Protocol limit |
| Base Address | 0x00001000 | Register block |
| Reset Type | Active-high | Synchronous |

## Protocol Description

The system uses a custom frame protocol over UART to access internal registers:

- Frame format includes command type, address, data, and CRC8 checksum
- Supports both read and write operations to internal registers
- Error detection and handling through CRC validation
- Flow control through handshaking mechanisms
- External access limited to UART interface only

## Verification Environment

### UVM System-Level Testbench

The verification environment provides comprehensive system-level testing using UVM 1.2 framework:

#### 🎯 Current Verification Status (2025年9月26日)

| メトリクス | 現状 | 目標 | 状況 |
|------------|------|------|------|
| **Line Coverage** | ✅ 100.0% | 100.0% | 達成済み |
| **Toggle Coverage** | ⚠️ 22.7% | >85.0% | 改善要 |
| **Expression Coverage** | ⚠️ 66.7% | >90.0% | 改善要 |
| **Functional Coverage** | ❌ 0.0% | >80.0% | 未実装 |

#### 🚀 Quick Start - 検証実行

```powershell
# 作業ディレクトリに移動
cd E:\Nautilus\workspace\fpgawork\AXIUART_\sim\uvm

# 基本テスト実行
.\run_uvm.ps1 -TestName "uart_axi4_basic_test" -Waves

# 包括的カバレッジテスト実行 (58分)
.\run_uvm.ps1 -TestName "uart_axi4_advanced_coverage_test" -Waves

# カバレッジレポート確認
dcreport.exe metrics.db -out_dir coverage_report
Start-Process "coverage_report\index.html"
```

#### 📚 検証ドキュメント

作業を開始する前に以下のドキュメントを必ず確認してください：

- **🎯 [次作業者への指示書](docs/next_worker_instructions.md)** - 今すぐ実行すべき作業
- **📋 [検証実行計画書](docs/verification_execution_plan.md)** - 詳細な検証計画
- **✅ [作業チェックリスト](docs/verification_checklist.md)** - 進捗管理用チェックリスト

#### UVM テストベンチ構成

```text
uart_axi4_tb_top (Testbench Top)
├── AXIUART_Top (DUT - Complete System)
├── uart_if (UART Virtual Interface)
├── uvm_test_top (UVM Test Framework)
│   └── uart_axi4_env (Test Environment)
│       ├── uart_agent (UART Protocol Agent)
│       │   ├── uart_driver (Stimulus Generation)
│       │   ├── uart_monitor (Response Monitoring)
│       │   └── uvm_sequencer (Test Sequencing)
│       ├── uart_axi4_scoreboard (Result Checking)
│       ├── uart_axi4_coverage (Functional Coverage)
│       └── uart_axi4_predictor (Expected Results)
└── uart_protocol_checker (Protocol Validation)
```

### Test Configuration

- **System-Level Testing**: Full AXIUART_Top integration verification
- **UART-Only Interface**: External AXI agents disabled (internal AXI monitoring)
- **System Status Monitoring**: Ready/Busy/Error signal tracking
- **Protocol Validation**: Frame format and timing verification
- **Coverage Collection**: Functional and code coverage metrics

### Available Test Cases

| Test Case | Description | Status |
|-----------|-------------|---------|
| axiuart_system_test | Basic system integration test | ✅ Implemented |
| uart_axi4_minimal_test | Minimal functionality verification | ✅ Implemented |
| uart_protocol_test | Protocol compliance validation | 🔄 In Development |
| register_access_test | Register read/write via UART | 🔄 In Development |
| error_handling_test | Error injection and recovery | 🔄 In Development |

## Model Context Protocol (MCP) Server Integration

### 🎯 True Model Context Protocol Environment

This project now provides **two simulation approaches**:

1. **🚀 Model Context Protocol (MCP) Server** ← **RECOMMENDED for new workflows**
2. **⚙️ Legacy Workspace MCP-UVM Environment** (PowerShell-based)

#### 🌟 New: True MCP Server (Standard-Compliant)

The **Model Context Protocol (MCP) server** provides standardized, cross-platform simulation execution that follows official MCP specifications.

##### Quick Start with MCP Server

```powershell
# Setup MCP server environment
cd e:\Nautilus\workspace\fpgawork\AXIUART_\mcp_server
python setup.py

# Start MCP server
python dsim_uvm_server.py --workspace e:\Nautilus\workspace\fpgawork\AXIUART_
```

##### Available MCP Tools

| Tool Name | Function | Example Usage |
|-----------|----------|---------------|
| `run_uvm_simulation` | Execute DSIM simulations | Test execution with full parameter control |
| `check_dsim_environment` | Verify DSIM setup | Environment validation and diagnostics |
| `list_available_tests` | Discover UVM tests | Automatic test class detection |
| `get_simulation_logs` | Retrieve results | Log analysis and error reporting |
| `generate_coverage_report` | Create coverage | HTML/XML coverage analysis |

##### MCP Server Benefits
- ✅ **Standard Protocol**: Official Model Context Protocol compliance
- ✅ **Cross-Platform**: Python-based, works across environments
- ✅ **Tool Integration**: Compatible with any MCP client
- ✅ **Automated Setup**: One-command environment preparation
- ✅ **Verified Execution**: Confirmed working with `uart_axi4_basic_test`

See detailed documentation: [`mcp_server/README.md`](mcp_server/README.md)

#### 🔧 Legacy: Workspace MCP-UVM Environment (PowerShell)

For users preferring the PowerShell-based approach, the workspace-specific environment remains available.

##### Safety Features
- **No System-Wide Changes**: PowerShell profiles and registry remain untouched
- **Session-Only**: Functions exist only in current PowerShell session  
- **Workspace-Isolated**: Only affects this project directory
- **Fully Reversible**: Close PowerShell to reset everything

##### Legacy Setup

```powershell
# Navigate to workspace root
cd e:\Nautilus\workspace\fpgawork\AXIUART_

# Initialize workspace-specific environment (safe)
.\workspace_init.ps1
```

##### Legacy Commands Available After Setup

```powershell
# Environment Verification
Test-WorkspaceMCPUVM       # Check function availability
Show-WorkspaceHelp         # Show available commands

# Legacy UVM Simulation
Invoke-MCPUVMTest          # Run UVM tests (PowerShell-based)
Invoke-MCPUVMQuickTest     # Fast test execution
Invoke-MCPUVMCompileOnly   # Compile-only verification
```

#### 🎯 Which Approach to Use?

| Use Case | Recommended Approach |
|----------|---------------------|
| **New Development** | 🚀 **MCP Server** (standard-compliant) |
| **Integration with Tools** | 🚀 **MCP Server** (universal compatibility) |
| **Cross-Platform Work** | 🚀 **MCP Server** (Python-based) |
| **Existing PowerShell Workflows** | ⚙️ Legacy Workspace Environment |
| **Quick Testing** | Either approach works |

## Quick Start

### Prerequisites

- **DSIM Simulator**: Metrics Design Automation DSIM v20240422.0.0+
- **SystemVerilog Support**: IEEE 1800-2017 compliant simulator
- **UVM Library**: UVM 1.2 (included with DSIM)
- **PowerShell**: For running simulation scripts (Windows environment)

### Environment Setup

#### Option 1: Model Context Protocol (MCP) Server (Recommended)

```powershell
# Setup MCP server dependencies
cd e:\Nautilus\workspace\fpgawork\AXIUART_\mcp_server
python setup.py

# Start MCP server
python dsim_uvm_server.py --workspace e:\Nautilus\workspace\fpgawork\AXIUART_
```

#### Option 2: Legacy PowerShell Environment

1. Set required environment variables:

   ```powershell
   $env:DSIM_HOME = "C:\Users\Nautilus\AppData\Local\metrics-ca\dsim\20240422.0.0"
   $env:DSIM_ROOT = $env:DSIM_HOME
   $env:DSIM_LIB_PATH = "$env:DSIM_HOME\lib"
   # Optional: $env:DSIM_LICENSE = "path\to\license"
   ```

2. Initialize workspace environment:

   ```powershell
   cd e:\Nautilus\workspace\fpgawork\AXIUART_
   .\workspace_init.ps1
   ```

3. Navigate to simulation directory:

   ```powershell
   Set-UVMWorkingDirectory  # or cd sim/uvm
   ```

### Test Execution

#### Using MCP Server (Recommended)

Run simulations through the Model Context Protocol server:

```python
# MCP tool: run_uvm_simulation
{
  "test_name": "uart_axi4_basic_test",
  "mode": "run",
  "verbosity": "UVM_MEDIUM",
  "waves": true,
  "coverage": true,
  "seed": 1
}
```

#### Using Legacy PowerShell Environment

```powershell
# Basic test execution
Invoke-MCPUVMTest -TestName "uart_axi4_basic_test"

# With specific options
Invoke-MCPUVMTest -TestName "uart_axi4_write_protocol_test" -Waves on -Coverage on
```

### Test Execution Results

Expected successful output from MCP Server:
```
🚀 DSIM UVM Simulation Results
==================================================
📊 Execution Status: ✅ SUCCESS
📁 Log File: uart_axi4_basic_test_20251013_130221.log
🔢 Exit Code: 0

📝 Simulation Output:
--------------------------------------------------
UVM_ERROR: 0
TEST PASSED
```

Expected successful output from Legacy PowerShell:
```
=== AXIUART_Top System Test Started ===
System Status: Ready=1, Busy=0, Error=00000000
=== AXIUART_Top System Test Completed Successfully ===
*** AXIUART SYSTEM TEST PASSED ***
UVM_ERROR: 0
```

### Available UVM Test Options

| Parameter | Default | Description |
|-----------|---------|-------------|
| TestName | axiuart_system_test | Test to execute |
| Coverage | $true | Enable coverage collection |
| Verbosity | UVM_MEDIUM | UVM logging level |
| Waves | $true | Generate waveform files |
| Seed | 1 | Random seed for reproducibility |
| CleanBuild | $false | Clean previous build artifacts |

### Simulation Outputs

- **Waveform files**: `<TestName>.mxd` (DSIM MXD format)
- **Coverage reports**: `coverage_report/index.html`
- **Simulation logs**: `dsim.log`, detailed execution logs
- **UVM reports**: Test topology, configuration, and results

## Documentation

- `docs/design_overview.md` - System architecture and design details
- `docs/uart_axi4_protocol.md` - UART frame protocol specification  
- `docs/uvm_testplan.md` - Verification plan and test scenarios
- `docs/run_guide.md` - Detailed simulation execution guide
- `docs/system_architecture.md` - Complete system integration documentation

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

### Verification Methodology

- **System-Level Verification**: Complete AXIUART_Top integration testing
- **UVM-based Framework**: Comprehensive testbench with agents and scoreboards
- **Coverage-Driven Verification**: Functional and code coverage metrics
- **Protocol Compliance**: SVA assertions for UART and AXI protocol checking
- **External Interface Focus**: UART-only external testing (internal AXI monitoring)

### Test Development Guidelines

1. **Test Isolation**: Each test should be self-contained and independent
2. **System Status Monitoring**: Always verify system_ready/busy/error signals
3. **Real RTL Testing**: Use actual AXIUART_Top, not simplified models
4. **Comprehensive Coverage**: Target frame types, error conditions, boundary values
5. **Documentation**: Maintain test descriptions and expected results

## Project Status

### ✅ Completed Features

- **RTL Implementation**: Complete AXIUART_Top system with internal AXI bus
- **UVM Framework**: System-level testbench with proper agent configuration
- **Basic Integration Test**: Successful system initialization and status verification
- **Build System**: Automated test execution with coverage and waveform generation
- **Documentation**: Comprehensive system architecture and verification documentation

### 🔄 In Development

- **UART Protocol Testing**: Frame transmission and register access tests
- **Error Injection Testing**: CRC error, timeout, and malformed frame handling
- **Performance Testing**: Throughput and latency characterization
- **Comprehensive Coverage**: Full protocol and system state coverage

### 🎯 Future Enhancements

- **Advanced Test Scenarios**: Multi-transaction sequences, stress testing
- **Protocol Extensions**: Additional command types and configuration options
- **Hardware Validation**: FPGA implementation and board-level testing

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
4. Run the basic system test to verify environment setup

## Version History

- **v1.0**: Initial UART-AXI4 bridge RTL implementation
- **v2.0**: Complete AXIUART_Top system integration with internal register block
- **v2.1**: UVM system-level verification framework with successful basic testing
- **Current**: Production-ready system with comprehensive verification environment
