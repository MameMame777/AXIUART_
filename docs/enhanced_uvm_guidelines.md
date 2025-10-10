# Enhanced UVM Development Guidelines
*Effective: October 10, 2025*
*Mandatory for all future UVM test development*

## Quick Start Guide

### 1. Creating New UVM Tests

**Step 1: Use Enhanced Base Class**
```systemverilog
// MANDATORY: Inherit from enhanced_uart_axi4_base_test
class your_new_test extends enhanced_uart_axi4_base_test;
    `uvm_component_utils(your_new_test)
    
    function new(string name = "your_new_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Enhanced reporting is automatically configured
endclass
```

**Step 2: Use Template for Consistency**
- Copy `template_enhanced_test.sv`
- Replace "template" with your test name
- Implement test-specific logic

**Step 3: Execute with Enhanced Reporting**
```powershell
# MANDATORY: Use enhanced reporting (enabled by default)
.\run_uvm.ps1 -TestName your_new_test -Verbosity UVM_MEDIUM -ReportAnalysis
```

### 2. Report ID Categorization Standards

**Mandatory Report ID Categories:**
- `[TEST_NAME]_START`: Test initialization and setup
- `[TEST_NAME]_PROGRESS`: Test execution milestones
- `[TEST_NAME]_RESULT`: Test results and validation
- `[TEST_NAME]_DEBUG`: Detailed debugging information

**Example Implementation:**
```systemverilog
`uvm_info("FRAME_PARSER_START", "Starting frame parser test", UVM_LOW)
`uvm_info("FRAME_PARSER_PROGRESS", "Frame validation in progress", UVM_MEDIUM)
`uvm_info("FRAME_PARSER_RESULT", "Frame validation PASSED", UVM_LOW)
`uvm_info("FRAME_PARSER_DEBUG", "Debug: CRC calculation details", UVM_HIGH)
```

### 3. Verbosity Level Guidelines

**Standard Verbosity Hierarchy:**
- **UVM_LOW**: Test results, major milestones, errors
- **UVM_MEDIUM**: Test progress, important state changes
- **UVM_HIGH**: Detailed debugging, component interactions
- **UVM_FULL**: Comprehensive tracing (use sparingly)

**Component-Specific Defaults:**
- Scoreboard: `UVM_HIGH` (critical for verification)
- Coverage: `UVM_MEDIUM` (important metrics)
- Drivers: `UVM_LOW` (reduce noise)
- Monitors: `UVM_MEDIUM` (balanced visibility)

### 4. PowerShell Script Requirements

**Mandatory Parameters:**
```powershell
param(
    [string]$TestName = "your_test",
    [ValidateSet("UVM_NONE", "UVM_LOW", "UVM_MEDIUM", "UVM_HIGH", "UVM_FULL")]
    [string]$Verbosity = "UVM_MEDIUM",
    [switch]$ReportAnalysis = $true,  # MUST be enabled by default
)
```

**Mandatory Function:**
- Include `Analyze-UVMReports` function
- Must analyze report counts by ID
- Must provide component volume analysis
- Must extract test-specific messages

## File Structure Requirements

### Required Files for New Projects:
```
project/
├── sim/exec/
│   └── enhanced_run_uvm.ps1        # With Analyze-UVMReports
├── uvm/tests/
│   ├── enhanced_uart_axi4_base_test.sv  # Enhanced base class
│   └── template_enhanced_test.sv        # Development template
├── docs/
│   └── enhanced_uvm_guidelines.md       # This file
└── scripts/
    └── report_trend_analysis.ps1        # Future: trend analysis
```

### Package Integration:
```systemverilog
// In uart_axi4_test_pkg.sv
`include "tests/enhanced_uart_axi4_base_test.sv"  // MANDATORY
`include "tests/your_new_test.sv"
```

## Quality Assurance Checklist

### Before Code Commit:
- [ ] Test inherits from `enhanced_uart_axi4_base_test`
- [ ] Test-specific report IDs implemented
- [ ] PowerShell script includes `Analyze-UVMReports`
- [ ] Test executed with `-ReportAnalysis` flag
- [ ] Report volume analysis reviewed

### Code Review Requirements:
- [ ] Enhanced base class inheritance verified
- [ ] Report categorization properly implemented
- [ ] Verbosity levels appropriate for component types
- [ ] No hardcoded report verbosity overrides

### CI/CD Integration:
- [ ] All tests execute with enhanced reporting
- [ ] Report analysis included in build artifacts
- [ ] Unusual report patterns flagged for review

## Performance Guidelines

### Acceptable Report Volumes:
- **Unit Tests**: <50 reports total
- **Integration Tests**: 50-200 reports total
- **System Tests**: 200-500 reports total
- **Stress Tests**: <1000 reports total

### High Volume Component Thresholds:
- **UART_MONITOR**: >30 reports → consider UVM_LOW
- **SCOREBOARD**: >50 reports → acceptable for complex tests
- **COVERAGE**: >20 reports → review coverage scope

## Troubleshooting Guide

### Common Issues and Solutions:

**Issue**: "Analyze-UVMReports function not found"
**Solution**: Verify function defined before script execution

**Issue**: High report volume from monitors
**Solution**: Reduce monitor verbosity to UVM_LOW

**Issue**: Missing test-specific categories
**Solution**: Implement proper report ID hierarchy

**Issue**: Enhanced base class not found
**Solution**: Verify package includes enhanced_uart_axi4_base_test.sv

## Success Metrics

### Expected Benefits:
- **50% reduction** in debugging time
- **100% consistency** in report categorization
- **Automated analysis** eliminating manual log review
- **Improved team productivity** through standardized reporting

### Measurement Criteria:
- All new tests use enhanced base class
- All PowerShell scripts include report analysis
- Report volume within acceptable thresholds
- Test-specific categories properly implemented

## Migration Path for Existing Tests

### Phase 1: Infrastructure (Completed)
- ✅ Enhanced base class created
- ✅ PowerShell analysis function implemented
- ✅ Template test created

### Phase 2: Test Updates (Next 2 weeks)
- [ ] Update existing tests to use enhanced base class
- [ ] Add test-specific report categorization
- [ ] Verify all tests work with enhanced reporting

### Phase 3: Full Adoption (Next 4 weeks)
- [ ] All new tests must use enhanced reporting
- [ ] CI/CD integration complete
- [ ] Team training completed

## Contact and Support

For questions about enhanced UVM reporting:
- Review this document first
- Check template_enhanced_test.sv for implementation examples
- Verify PowerShell script includes Analyze-UVMReports function

**Remember**: Enhanced reporting is now MANDATORY for all UVM development. This ensures consistent, analyzable, and maintainable test output across all projects.