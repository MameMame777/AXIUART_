# Project UVM Reporting Guidelines
*Based on UVM Reporting Strategy Implementation (October 10, 2025)*

## Overview
This document defines the project-specific UVM reporting guidelines for the AXIUART project, implementing the enhanced reporting strategy established on October 10, 2025.

## Test Class Structure

### Base Class Hierarchy
- All tests inherit from `enhanced_uart_axi4_base_test`
- Enhanced base provides mandatory reporting configuration
- Individual tests implement test-specific reporting via `configure_test_specific_reporting()`

### Report ID Naming Convention
All test-specific report IDs follow hierarchical naming:
```
TEST_<TEST_TYPE>_<CATEGORY>_<SPECIFIC>
```

Examples:
- `TEST_FRAME_PARSER_DIAG_START`
- `TEST_BASIC_SEQ`
- `TEST_MINIMAL_PROGRESS`

## Implementation Status

### Completed Features
1. **Enhanced Base Test Class** (`enhanced_uart_axi4_base_test.sv`)
   - Mandatory reporting configuration for all tests
   - Component-specific verbosity optimization
   - Hierarchical report ID management
   - October 10, 2025 standards compliance

2. **Enhanced Execution Script** (`run_uvm.ps1`)
   - Automatic enhanced reporting analysis
   - Report parsing and categorization
   - Performance classification
   - Default enabled enhanced analysis

3. **Test Class Updates**
   - 32 test classes updated to inherit from enhanced base
   - Test-specific report ID implementation
   - Proper UVM function call syntax

### Verified Functionality
- **Test Execution**: Successfully runs with UVM_ERROR = 0
- **Report Generation**: Proper UVM report counts and categorization
- **Enhanced Analysis**: PowerShell script analysis integration
- **Waveform Generation**: MXD format output with proper naming
- **Coverage Collection**: Integrated coverage reporting

## Usage Guidelines

### For Test Development
1. Inherit from `enhanced_uart_axi4_base_test`
2. Implement `configure_test_specific_reporting()` with hierarchical IDs
3. Use test-specific report IDs in `uvm_info` calls
4. Follow English comments and documentation standards

### For Test Execution
1. Use `run_uvm.ps1` with `-ReportAnalysis` (enabled by default)
2. Enhanced reporting provides automatic analysis
3. Waveforms saved to `archive/waveforms/` in MXD format
4. Coverage reports generated automatically

### Report ID Management
- Use hierarchical naming for all test-specific IDs
- Configure verbosity levels appropriately:
  - `UVM_HIGH`: Critical start/end points
  - `UVM_MEDIUM`: Progress and state transitions
  - `UVM_LOW`: Summary information

## File Structure
```
sim/
├── exec/
│   └── run_uvm.ps1           # Enhanced execution script
├── uvm/
│   ├── tests/
│   │   ├── enhanced_uart_axi4_base_test.sv  # Base class
│   │   ├── frame_parser_diagnostic_test.sv  # Example implementation
│   │   └── ...               # Other test classes
│   └── sequences/
│       └── debug_sequences.sv  # Separated to avoid conflicts
```

## Compliance Notes
- Implementation follows October 10, 2025 UVM Reporting Strategy
- All tests provide enhanced reporting capabilities
- PowerShell analysis provides detailed report breakdown
- Supports hierarchical verbosity management
- Enables comprehensive test diagnostics

## Future Enhancements
- Additional report analysis metrics
- Integration with CI/CD reporting
- Enhanced coverage correlation
- Advanced filtering capabilities

---
*Generated: October 11, 2025*
*Compliance: UVM Reporting Strategy Implementation Guidelines*