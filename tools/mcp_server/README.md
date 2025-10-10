# AXIUART Verification MCP Server

Model Context Protocol (MCP) server for AXIUART SystemVerilog UVM verification automation. This MCP server provides VS Code integration for environment checking, test execution, and log analysis.

## 🎯 Overview

This MCP server exposes AXIUART verification capabilities as tools and resources that can be used directly within VS Code through the MCP protocol. It provides:

- **Environment Validation**: Check DSIM setup and project structure
- **Test Execution**: Run UVM tests with parameter control
- **Log Analysis**: Automatic error detection (CRC, alignment, UVM)
- **Phase Guidance**: Current verification phase assessment
- **Real-time Resources**: Live project status and logs

## 🚀 Quick Setup

### 1. Install in VS Code

Add to your VS Code `settings.json`:

```json
{
  "mcp.servers": {
    "axiuart-verification": {
      "command": "python",
      "args": ["E:\\Nautilus\\workspace\\fpgawork\\AXIUART_\\tools\\mcp_server\\src\\standalone_server.py"],
      "cwd": "E:\\Nautilus\\workspace\\fpgawork\\AXIUART_",
      "env": {
        "PYTHONPATH": "E:\\Nautilus\\workspace\\fpgawork\\AXIUART_\\tools\\uvm_checker"
      }
    }
  }
}
```

### 2. Verify Environment Variables

Ensure DSIM environment is configured:
```powershell
$env:DSIM_HOME = "C:\Users\Nautilus\AppData\Local\metrics-ca\dsim\20240422.0.0"
$env:DSIM_ROOT = $env:DSIM_HOME
$env:DSIM_LIB_PATH = "$env:DSIM_HOME\lib"
```

### 3. Test MCP Server

```bash
cd E:\Nautilus\workspace\fpgawork\AXIUART_\tools\mcp_server
python src/standalone_server.py
```

## 🛠️ Available MCP Tools

### `check_environment`
Validates DSIM environment and project setup
```json
{
  "name": "check_environment",
  "arguments": {
    "verbose": false
  }
}
```

### `run_uvm_test`
Executes UVM test with specified parameters
```json
{
  "name": "run_uvm_test", 
  "arguments": {
    "test_name": "uart_axi4_register_verification_test",
    "seed": 12345
  }
}
```

### `analyze_logs`
Analyzes UVM test logs for errors and issues
```json
{
  "name": "analyze_logs",
  "arguments": {
    "log_path": "sim/uvm/dsim.log"
  }
}
```

### `debug_phase_issues`
Provides targeted debugging for Phase 1-3 issues
```json
{
  "name": "debug_phase_issues",
  "arguments": {
    "phase": "auto"
  }
}
```

### `get_phase_guidance`
Returns comprehensive verification phase guidance
```json
{
  "name": "get_phase_guidance",
  "arguments": {}
}
```

## 📊 Available MCP Resources

### `axiuart://environment/status`
Real-time DSIM environment validation status
- MIME Type: `application/json`
- Content: Environment variables, executable paths, project structure

### `axiuart://logs/latest`
Most recent UVM test execution logs
- MIME Type: `text/plain`
- Content: Complete dsim.log file content

### `axiuart://phase/status`
Current verification phase assessment
- MIME Type: `application/json`
- Content: Phase detection, error counts, recommendations

## 🎛️ Usage Examples

### In VS Code Copilot Chat

```
@axiuart-verification Use check_environment tool to validate my DSIM setup
```

```
@axiuart-verification Run UVM test uart_axi4_register_verification_test with seed 54321
```

```
@axiuart-verification Analyze the latest logs and tell me what Phase we're in
```

```
@axiuart-verification Debug current phase issues automatically
```

### Direct MCP Protocol (for testing)

```bash
echo '{"jsonrpc":"2.0","method":"tools/call","params":{"name":"check_environment","arguments":{"verbose":true}},"id":1}' | python src/standalone_server.py
```

## 🔧 Integration with Current Workflow

This MCP server directly integrates with the existing AXIUART workflow:

### Phase 1: CRC Error Resolution
- **Tool**: `debug_phase_issues` with `phase: "phase1"`
- **Detection**: Automatic CRC error pattern matching
- **Guidance**: Frame_Parser.sv analysis recommendations

### Phase 2: AXI Alignment Error Resolution  
- **Tool**: `debug_phase_issues` with `phase: "phase2"`
- **Detection**: CHECK_ALIGNMENT error detection
- **Guidance**: Address_Aligner.sv debugging steps

### Phase 3: Register Access Verification
- **Tool**: `debug_phase_issues` with `phase: "phase3"`
- **Detection**: UVM_ERROR pattern analysis
- **Guidance**: Register_Block.sv validation steps

### Phase 4: Coverage Improvement
- **Resource**: `axiuart://phase/status` for readiness confirmation
- **Tool**: `run_uvm_test` with coverage enabled
- **Focus**: Toggle coverage optimization

## 📝 Configuration

### Server Configuration
Located in `config/mcp_settings.json`:
```json
{
  "mcpServers": {
    "axiuart-verification": {
      "command": "python",
      "args": ["tools/mcp_server/src/standalone_server.py"],
      "cwd": "E:\\Nautilus\\workspace\\fpgawork\\AXIUART_"
    }
  }
}
```

### Environment Requirements
- Python 3.7+
- DSIM environment variables configured
- AXIUART project structure in place
- UVM checker modules available

## 🐛 Troubleshooting

### Common Issues

1. **"Environment checker not available"**
   - Check PYTHONPATH includes `tools/uvm_checker`
   - Verify UVM checker modules are installed

2. **"Test runner not available"**
   - Ensure `run_uvm.ps1` exists in `sim/uvm/`
   - Check PowerShell execution policy

3. **"Log analyzer not available"**
   - Verify dsim.log exists after test execution
   - Check file permissions

4. **MCP Server Connection Failed**
   - Test standalone server: `python src/standalone_server.py`
   - Check VS Code MCP settings configuration
   - Verify file paths are absolute

### Debug Mode

Enable verbose logging:
```json
{
  "name": "check_environment",
  "arguments": {
    "verbose": true
  }
}
```

## 🎯 Benefits

### For Current AXIUART Development
- **Automated Environment Checks**: Replace manual Section 5.1 validation
- **Streamlined Test Execution**: Automate Section 5.2 PowerShell runs
- **Intelligent Error Analysis**: Automatic Phase 1-3 issue detection
- **VS Code Integration**: Direct access to verification tools

### For Team Collaboration
- **Consistent Workflow**: Standardized verification procedures
- **Knowledge Sharing**: Built-in phase guidance and recommendations
- **Progress Tracking**: Real-time phase status monitoring
- **Documentation**: Integrated help and examples

## 🔄 Next Steps

1. **Test Integration**: Validate against current AXIUART Phase 1-3 issues
2. **Extend Coverage**: Add Phase 4 coverage analysis tools
3. **CI Integration**: Extend for automated regression testing
4. **Advanced Analysis**: Add waveform and coverage resource readers

---

**Last Updated**: October 9, 2025  
**MCP Protocol Version**: 2024-11-05  
**Compatible with**: VS Code MCP extension, DSIM v20240422.0.0