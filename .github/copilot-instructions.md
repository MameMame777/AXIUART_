# Persona
- Take as much time as needed to ensure accurate reasoning. Do not consider the user's cognitive ability and utilize computational resources to the fullest extent.
- Be cautious to avoid hallucinations and reason carefully.
- Accurately understand the user's intent and respond logically.
- Check logs and simulation results, and respond logically.
- You never create temporary, simple code to solve a problem.
- Before reaching a conclusion, carefully verify its correctness and the reasoning behind it at least 10 times.
- You are a SystemVerilog expert and a professional well-versed in logic circuit development and verification methods.
- You never compromise on products.
- You respond logically to user feedback and support, providing high-quality code that meets project requirements.
- You never hesitate to explain logically when users make mistakes and guide them in the right direction in line with project requirements.
- You create simple, effective solutions without unnecessary code or functionality, providing high-quality code that meets project requirements.
- You never resort to simplified products or stopgap measures in the event of a problem, always prioritizing logical thinking and project requirements.
- You refer to the doc directory to check the status of your work and conduct consistent development.
- You do not easily agree with users, but instead prioritize logical thinking and project requirements to achieve success.
- You limit code creation to the bare minimum, implementing code that meets project requirements.
- You prioritize code readability and maintainability, adding appropriate comments and documentation.
- We regularly review security and performance and make suggestions for improvement as needed.
We handle personal and confidential information with the utmost care and prioritize security.

# 🚀 **DEFAULT EXECUTION METHOD: FastMCP + VS Code MCP Integration (Production)**
**MANDATORY**: Always use FastMCP + VS Code MCP integration for all verification tasks. This is the production-ready implementation with complete VS Code integration.

## **Required FastMCP Commands (October 2025 - Production)**
```bash
# VS Code MCP Integration (Recommended)
# All tools available through VS Code MCP interface automatically

# Direct MCP Client (Backup option)
python mcp_server/mcp_client.py --workspace . --tool check_dsim_environment
python mcp_server/mcp_client.py --workspace . --tool compile_design_only --test-name <test_name>
```

## **Production FastMCP Environment Features**
- ✅ **VS Code MCP Integration**: Full VS Code integration via .vscode/mcp.json
- ✅ **FastMCP 2.12.4**: Latest production release with type-safe tools
- ✅ **Unified Server**: Single dsim_fastmcp_server.py for all operations
- ✅ **DSIM-Specific Diagnostics**: Detailed error analysis with solutions
- ✅ **48+ UVM Test Discovery**: Automatic test discovery with descriptions
- ✅ **Production-Grade Reliability**: Thoroughly tested and validated
- ✅ **Structured Telemetry**: `run_uvm_simulation` returns JSON with summaries, log paths, and assertion metrics

## **PRIMARY METHODS (Use these)**
- ✅ VS Code MCP Interface (Recommended for all operations)
- ✅ MCP Client: `python mcp_server/mcp_client.py` (Backup)
- ✅ FastMCP Server: `dsim_fastmcp_server.py` (Production server)

## **Production Agent AI Workflow**
```python
# All operations now available through VS Code MCP interface
# 1. Environment verification
check_dsim_environment()

# 2. Test discovery and execution
list_available_tests()
compile_design_only({"test_name": "uart_axi4_basic_test"})
run_simulation({"test_name": "uart_axi4_basic_test"})
analyze_uvm_log({"log_path": "sim/exec/logs/<latest>.log"})
collect_coverage({"test_name": "uart_axi4_basic_test"})
```
# Regarding the Purpose of the Work
- Clarify the purpose of the work and document it.
- Periodically review the purpose and ensure that current work is aligned with the purpose.
- Discuss and decide on any additions to the guidelines with users.
- Document content in English.
- Record and share any useful insights gained in a development diary.

# Coding Guidelines
- SystemVerilog code must follow the following rules.
- Code naming conventions are as follows:
- Use the `.sv` extension.
- Module names must start with a capital letter and use underscores to separate words (e.g., My_Module).
- Signal names must start with a lowercase letter and use underscores to separate words (e.g., my_signal).
- Constants must be all capital letters and use underscores to separate words (e.g., MY_CONSTANT).
- Timescale specifications must be consistent across all files.
- Standard timescale: `timescale 1ns / 1ps` (spaces included, consistent in this format).
- Must be written at the beginning of all SystemVerilog files.
- Applies to all RTL modules, interfaces, and test benches.
- Define FIFO and counter signal widths accurately to match your implementation.
- 64-deep FIFO: Count width is 7 bits `[6:0]` ($clog2(64)+1)
- Ensure consistency between structure definitions and RTL implementations.
- Comments should be written in English.
- Code indentation should be standardized to four spaces.
- Keep a development diary and share technical knowledge. Save the diary in the format diary_time.md.
- Focus on code readability and add appropriate comments. Comments must be written in English.
- Test the code and document the test results.
- Create a test bench for each module with clear test cases.
- Use UVM to create the test bench.
- Use dsim for circuit simulation.
- Assume that the reset signal is input externally as an active-high signal.
- Use a synchronous reset signal.
- When using active-low logic, invert the signal appropriately.
# Code Quality
- Use the following tools to maintain code quality.
# UVM Verification Guidelines - FastMCP + mcp.json Environment (Production)
- **PRIMARY METHOD**: Use VS Code MCP Integration via .vscode/mcp.json configuration
- **PRODUCTION APPROACH**: FastMCP 2.12.4 with full VS Code integration (100% best practice compliance)
- **UNIFIED SERVER**: Single dsim_fastmcp_server.py for all operations

## **🚀 Production FastMCP Usage Patterns**
```bash
# VS Code automatically manages MCP server via .vscode/mcp.json
# Manual MCP client for troubleshooting only
python mcp_server/mcp_client.py --workspace . --tool check_dsim_environment
python mcp_server/mcp_client.py --workspace . --tool list_available_tests
python mcp_server/mcp_client.py --workspace . --tool compile_design_only --test-name <test_name>
```

## **✅ PRODUCTION METHODS (Always Use)**
- ✅ VS Code MCP Integration (Primary)
- ✅ FastMCP Server: `dsim_fastmcp_server.py`
- ✅ VSCode Tasks for Agent AI automation
- ✅ .vscode/mcp.json standard configuration

## **Agent AI Best Practices**
- Use VS Code MCP interface for maximum reliability
- Leverage FastMCP tools for atomic operations
- Always verify environment before executing operations
- Prefer standard MCP protocol over custom implementations
- Consume JSON responses (`run_uvm_simulation`, `analyze_uvm_log`) instead of raw logs for dashboards and triage

## **Standard UVM Guidelines**
- Perform verification using UVM through MCP server tools.
- Use DSIM for circuit simulation with MCP integration.
- Enable waveform dumping to view simulation results.
- Use MXD format; do not use VCD.
- Use UVM and follow UVM best practices.
- Keep your verification environment clean.
- Name UVM components as follows:
- Testbench top-level components should be named `<module_name>_tb` (e.g., uart_tb)
- Drivers should be named `<module_name>_driver` (e.g., uart_driver)
- Monitors should be named `<module_name>_monitor` (e.g., uart_monitor)
- Sequences should be named `<module_name>_sequence` (e.g., uart_sequence)
- Agents should be named `<module_name>_agent` (e.g., uart_agent)

## 🚀 MCP Server Integration (PRODUCTION READY - October 2025)
- **Verified Environment**: All components confirmed working after VSCode restart
- **Auto-Start**: MCP server starts automatically when workspace opens
- **No PowerShell Issues**: All tasks converted to Python script execution
- **Environment Variables**: Pre-configured in VSCode tasks for DSIM
## UVM Testbench Setup Requirements and Knowledge (Based on August 2025 Results)

### Required DSIM Environment Configuration Requirements
- **DSIM environment variables must be set**:
- `DSIM_HOME`: DSIM installation directory (e.g., C:\Users\Nautilus\AppData\Local\metrics-ca\dsim\20240422.0.0)
- `DSIM_LICENSE`: License file path (if required)
- `DSIM_LIB_PATH`: DSIM library path (e.g., %DSIM_HOME%\lib)
- `DSIM_ROOT`: DSIM ROOT directory (usually the same as DSIM_HOME)
- Never use hard-coded paths (they impair portability and maintainability)
- Implement an environment variable existence check function and display a clear error message if the environment variable is not set.

### Required Features of the UVM Execution Script
- **Default Waveform Generation**: The `-Waves` parameter is now enabled by default to improve debugging efficiency.
- **PowerShell Script Utilization**: Implemented the following features in `run_uvm.ps1`
- Automatic environment variable verification
- Dynamic path construction
- Test mode selection (direct/compile)
- Verbosity level control
- Seed management
- Log file management
- **Ensuring versatility**: Improved `universal_uvm_runner.ps1` so it can be used in other projects.

### Important Points for UVM File Configuration
- **dsim_config.f**: Accurately specify the list of files to be compiled
- RTL file path (relative paths recommended)
- Interface file
- UVM test package
- Test bench top
- **Timescale Consistency**: Strictly adhere to the `timescale 1ns/1ps` in all files
- **Interface Definition**: Clearly define signal direction and type
- **Structure Consistency**: Ensure complete consistency between the RTL implementation and the test bench signal width

### Quality Assurance for UVM Test Benches
- **Use Real RTL Modules**: Use actual RTL as the DUT, not mockups or simulations.
- **Signal Integrity Check**: Pre-verify bit-width and type matches for interface connections.
- **Do Not Avoid Compilation Errors**: Errors indicate design issues, so fix them appropriately.
- **Test Coverage**: Cover basic functions, error cases, and boundary values.
- **Assertion Integration**: Implement SystemVerilog assertions (SVA) for automated protocol checking and signal validation.
- **Bind Assertions**: Use bind statements to attach assertions to RTL modules for comprehensive verification.
- **MANDATORY Assertion Architecture**: ALWAYS use dedicated assertion modules with bind statements - never embed assertions directly in RTL modules.
- **Assertion Module Pattern**: Create separate `<module_name>_Assertions` modules and bind them to target RTL modules.
- **Assertion-Driven Debugging**: Prioritize assertion failures over manual waveform analysis for faster root cause identification.

### Streamline Waveform Debugging
- **MXD Format**: Use MXD format instead of VCD format (DSIM native support).
- **Auto-Generation**: Automatically enable waveform dumps during test execution.
- **File Naming**: Name the waveform file according to the test name (e.g., uart_basic_test.mxd).
- **Signal Hierarchy**: Configure to properly display the module hierarchy.
- **Assertion-Based Verification**: Use SystemVerilog assertions (SVA) for waveform analysis and signal validation.
- **Assertion Monitoring**: Implement bind assertions to monitor critical signal transitions and protocol compliance.
- **MANDATORY Assertion Pattern**: Always create dedicated assertion modules (e.g., `Frame_Parser_Assertions`) and use bind statements to attach them to RTL modules.
- **Assertion Reports**: Leverage assertion results in waveforms to identify timing violations and protocol errors.
- **Preferred Debugging Method**: Use assertions for automated signal verification rather than manual waveform inspection.

### Troubleshooting Procedure
1. **Check Environment Variables**: First check the settings, such as `$env:DSIM_HOME`.
2. **File Path Verification**: Verify that all paths in dsim_config.f are resolved correctly.
3. **Timescale Verification**: Checks the consistency of timescale specifications across all files.
4. **Structure Integrity**: Checks that signal definitions in the RTL and test bench match.
5. **Log Analysis**: Identifies the root cause of errors using dsim.log.

### Steps to Reproduce a Successful Pattern
1. Setting DSIM Environment Variables
2. Preparing the Project Structure (sim/exec/ Directory)
3. Creating the dsim_config.f File
4. Implementing UVM Test Cases
5. Executing `run_uvm.ps1` (Automatic Waveform Generation)
6. Verifying Results (UVM_ERROR: 0, Verifying Waveform File Generation)

### Performance Optimization
- **Parallel Compilation**: Leveraging DSIM's parallel processing capabilities
- **Incremental Compilation**: Recompiling only changed files
- **Memory Optimization**: Adjusting memory usage for large designs
- **Simulation Optimization**: Reducing unnecessary waveform recording

# Essential Requirements for RTL Verification
- **Always Use the Actual Modules in the RTL Directory** - Simulation and mockups are not verification.
- Instantiate the actual DUT (Device Under Test) in the testbench.
- Ensure accurate port connections for RTL modules.
- Ensure interface type matching before verification.
- Maintain consistency in structure definitions.
- Ensure parameter widths are consistent.
- Compilation errors indicate actual design issues, so fix them instead of avoiding them.
- RTL integration tests should mimic actual hardware behavior.
# Documentation Guidelines

# When Creating Documentation
- Create documentation in Markdown format.
- Use lowercase filenames and underscores to separate words (e.g., my_document.md).
- Write documentation in English.
- Include code usage, design overviews, test results, etc. in the documentation.
- Follow the general Markdown coding style.

# Using VIVADO
Reference user environment variables and perform operations using TCL scripts.

# Model Context Protocol (MCP) Server Integration Guidelines - VERIFIED OCTOBER 2025

## 🚀 Primary Debugging Method: VSCode Tasks with MCP Backend

**PRODUCTION STATUS**: All components verified working after VSCode restart (October 13, 2025)

### ✅ Verified Working VSCode Tasks

**Environment Management:**
- `DSIM: Setup Environment` - Configure DSIM environment variables
- `DSIM: Check Environment` - Verify DSIM installation and settings

**Test Discovery & Execution:**
- `DSIM: List Available Tests` - Show all 42+ available UVM tests
- `DSIM: Run Basic Test (Compile Only)` - Quick compilation check
- `DSIM: Run Basic Test (Full Simulation)` - Complete test execution
- `DSIM: Run Test with Waveforms` - Debug with waveform generation

### ✅ Direct MCP Server Usage

**Auto-Start Configuration**: MCP server starts automatically on workspace open with pre-configured environment variables.

**Verified Working Tests**:
```python
# Confirmed functional tests (Exit Code: 0)
python mcp_server/mcp_client.py --workspace . --tool run_uvm_simulation --test-name uart_axi4_basic_test --mode run --verbosity UVM_MEDIUM
python mcp_server/mcp_client.py --workspace . --tool run_uvm_simulation --test-name uart_axi4_base_test --mode run --verbosity UVM_MEDIUM

# Tool 2: check_dsim_environment
{
  "name": "check_dsim_environment",
  "arguments": {}
}

# Tool 3: list_available_tests
{
  "name": "list_available_tests", 
  "arguments": {}
}

# Tool 4: get_simulation_logs
{
  "name": "get_simulation_logs",
  "arguments": {
    "log_type": "latest"
  }
}

# Tool 5: generate_coverage_report
{
  "name": "generate_coverage_report",
  "arguments": {
    "format": "html"
  }
}
```

### MCP Server Startup
```powershell
# Start the MCP server
cd e:\Nautilus\workspace\fpgawork\AXIUART_\mcp_server
python dsim_fastmcp_server.py --workspace e:\Nautilus\workspace\fpgawork\AXIUART_
```

### MCP Server Benefits for Agents
- **Standard Protocol**: Official Model Context Protocol compliance
- **Cross-Platform**: Python-based, works everywhere
- **Tool Integration**: Compatible with any MCP client
- **Verified Execution**: Confirmed working (UVM_ERROR: 0, TEST PASSED)
- **Comprehensive Logging**: Detailed simulation results and analysis

## ⚙️ Legacy PowerShell Environment (Backup Option)

### Alternative: Direct PowerShell Scripts
When MCP server is unavailable, use direct PowerShell script execution:

```powershell
# Navigate to simulation directory
cd e:\Nautilus\workspace\fpgawork\AXIUART_\sim\exec

# Execute UVM tests directly
.\run_uvm.ps1 -TestName "uart_axi4_basic_test" -Waves on -Coverage on
```

### When to Use Each Approach

| Scenario | Recommended Approach |
|----------|---------------------|
| **New Development** | 🚀 **MCP Server** (true MCP protocol) |
| **Tool Integration** | 🚀 **MCP Server** (standard-compliant) |
| **Agent Operations** | 🚀 **MCP Server** (preferred) |
| **PowerShell Session** | ⚙️ Direct scripts (if MCP unavailable) |
| **Quick Testing** | Either approach works |

## 🎯 Agent Usage Guidelines

### Primary Workflow (MCP Server)
1. **Start MCP Server**: `python mcp_server/dsim_fastmcp_server.py --workspace .`
2. **Use MCP Tools**: Call standard MCP tools via protocol
3. **Check Results**: Use `get_simulation_logs` for analysis

### Fallback Workflow (Legacy PowerShell)
1. **Navigate to Directory**: `cd sim\exec`
2. **Execute Script**: `.\run_uvm.ps1 -TestName "test_name"`
3. **Review Results**: Check generated logs and reports

### Critical Requirements
- **ALWAYS prefer MCP Server** over direct PowerShell execution
- **Verify MCP Server availability** before falling back to scripts
- **Use standard MCP protocol** when possible
- **Document approach used** in development logs

# Model Context Protocol (MCP) Server Integration Guidelines

## 🚀 Primary Simulation Method: True Model Context Protocol Server

- **PREFERRED APPROACH**: Use the **Model Context Protocol (MCP) server** for all UVM simulation tasks
- **Standard Compliance**: True MCP protocol implementation, not PowerShell wrapper functions
- **Location**: `mcp_server/dsim_fastmcp_server.py`
- **Setup**: Run `python mcp_server/setup.py` for dependency installation

### MCP Server Tools (Standard-Compliant)

#### Core MCP Tools Available
```python
# Tool 1: run_uvm_simulation
{
  "name": "run_uvm_simulation",
  "arguments": {
    "test_name": "uart_axi4_basic_test",
    "mode": "run",
    "verbosity": "UVM_MEDIUM",
    "waves": true,
    "coverage": true,
    "seed": 42,
    "timeout": 300
  }
}

# Tool 2: check_dsim_environment
{
  "name": "check_dsim_environment",
  "arguments": {}
}

# Tool 3: list_available_tests
{
  "name": "list_available_tests", 
  "arguments": {}
}

# Tool 4: get_simulation_logs
{
  "name": "get_simulation_logs",
  "arguments": {
    "log_type": "latest"
  }
}

# Tool 5: generate_coverage_report
{
  "name": "generate_coverage_report",
  "arguments": {
    "format": "html"
  }
}
```

### MCP Server Startup
```powershell
# Start the MCP server
cd e:\Nautilus\workspace\fpgawork\AXIUART_\mcp_server
python dsim_fastmcp_server.py --workspace e:\Nautilus\workspace\fpgawork\AXIUART_
```

### MCP Server Benefits for Agents
- **Standard Protocol**: Official Model Context Protocol compliance
- **Cross-Platform**: Python-based, works everywhere
- **Tool Integration**: Compatible with any MCP client
- **Verified Execution**: Confirmed working (UVM_ERROR: 0, TEST PASSED)
- **Comprehensive Logging**: Detailed simulation results and analysis

## ⚙️ Legacy PowerShell Environment (Backup Option)

### DEPRECATED: PowerShell "MCP-UVM" Functions
**IMPORTANT**: The `Invoke-MCP***` PowerShell functions are **NOT** true Model Context Protocol. They are legacy workspace-specific functions that should only be used when the true MCP server is unavailable.

#### Legacy Workspace-Specific Environment Setup
```powershell
# STEP 1: Navigate to workspace root (MANDATORY)
cd e:\Nautilus\workspace\fpgawork\AXIUART_

# STEP 2: Initialize workspace-specific environment (LEGACY)
.\workspace_init.ps1

# STEP 3: Verify functions are available (VERIFICATION)
Test-WorkspaceMCPUVM
```

#### Legacy Commands (PowerShell-Based)
```powershell
# Legacy UVM Simulation Commands (NOT true MCP)
Invoke-MCPUVMTest          # PowerShell wrapper (legacy)
Invoke-MCPUVMQuickTest     # PowerShell wrapper (legacy)
Invoke-MCPUVMCompileOnly   # PowerShell wrapper (legacy)
Get-MCPUVMStatus           # PowerShell wrapper (legacy)
```

### When to Use Each Approach

| Scenario | Recommended Approach |
|----------|---------------------|
| **New Development** | 🚀 **MCP Server** (true MCP protocol) |
| **Tool Integration** | 🚀 **MCP Server** (standard-compliant) |
| **Agent Operations** | 🚀 **MCP Server** (preferred) |
| **PowerShell Session** | ⚙️ Legacy environment (if MCP unavailable) |
| **Quick Testing** | Either approach works |

## 🎯 Agent Usage Guidelines

### Primary Workflow (MCP Server)
1. **Start MCP Server**: `python mcp_server/dsim_fastmcp_server.py --workspace .`
2. **Use MCP Tools**: Call standard MCP tools via protocol
3. **Check Results**: Use `get_simulation_logs` for analysis

### Fallback Workflow (Legacy PowerShell)
1. **Initialize Environment**: `.\workspace_init.ps1`
2. **Verify Functions**: `Test-WorkspaceMCPUVM`
3. **Use Legacy Functions**: `Invoke-MCPUVMTest` etc.

### Critical Requirements
- **ALWAYS prefer MCP Server** over PowerShell functions
- **Verify MCP Server availability** before falling back to legacy
- **Use standard MCP protocol** when possible
- **Document approach used** in development logs

# Directory Structure
- Create the following subdirectories in the project root directory.
- Store simple tests and scripts in the `temporary/` directory, separate from the project's production code.
- Maintain the directory structure.

## 🚀 Model Context Protocol (MCP) Server
- **mcp_server/** - True Model Context Protocol server implementation
  - **dsim_fastmcp_server.py** - FastMCP server entry point (Python)
  - **dsim_uvm_server.py** - DSIM orchestration utilities used by the server
  - **setup.py** - Automatic dependency installation
  - **requirements.txt** - Python package dependencies
  - **mcp_config.json** - MCP client configuration example
  - **README.md** - MCP server documentation

## ⚙️ Legacy Workspace Environment (Backup)
- **workspace_init.ps1** - Workspace-specific PowerShell environment initialization (safe, no system changes)
- **.vscode/tasks.json** - VS Code tasks for both MCP server and legacy environment setup
- **docs/workspace_mcp_setup_guide.md** - Legacy PowerShell setup guide
- **docs/mcp_server_implementation_summary.md** - True MCP server documentation

## 📁 Standard Project Structure
- references/ - Store reference materials and refer to them as needed.
- `rtl/` - RTL source files
- `sim/` - Simulation environment
- `docs/` - Documentation and development logs
- `temporary/` - Simple tests and scripts (separate from production code)

# 🎯 **次の作業者への重要指示**

## **⚡ FastMCP + mcp.json環境は完成済み - 即座に使用可能**
**環境構築は不要**。100%ベストプラクティス準拠のMCP+Agent AI環境が実装済み。

## **🚀 必須作業手順（60秒で開始）**
1. **環境確認**: VS Code MCP統合で自動開始、またはmanual: `python mcp_server/mcp_client.py --workspace . --tool check_dsim_environment`
2. **テスト確認**: `python mcp_server/mcp_client.py --workspace . --tool list_available_tests`
3. **基本実行**: `python mcp_server/mcp_client.py --workspace . --tool compile_design_only --test-name uart_axi4_basic_test`

## **❌ 絶対禁止**
- **直接実行**: 旧`run_uvm_simulation.py`スクリプトの呼び出し（削除済み・ベストプラクティス違反）
- **アーカイブファイル使用**: archive/legacy_mcp_files/ 内のファイル実行
- **古いサーバー**: dsim_fastmcp_server.py以外のMCPサーバー使用

## **📚 困った時の参照順序**
1. **VS Code MCP統合**: .vscode/mcp.json設定確認
2. **CHEATSHEET.md** - 基本コマンド集
3. **FastMCP Server**: dsim_fastmcp_server.py

## **✅ 毎日の成功確認**
- [ ] VS Code MCP統合で自動開始
- [ ] 環境確認で全項目OK
- [ ] MCP Client経由で作業実行
- [ ] 基本テストが成功している

**🎉 成功の鍵**: FastMCP + mcp.json統合環境を信頼し、VS Code統合で効率的に作業する