# Phase 5: Physical Layer Investigation
## UART Signal Quality & PC Reception Analysis

### 📋 Investigation Plan

**Objective**: Identify root cause of 0x20→0x48 conversion in UART communication
**Scope**: Physical layer signals + PC-side reception tools
**Confidence**: HIGH (RTL layer completely verified in Phase 4)

### 🔬 Investigation Strategy

#### A. Oscilloscope UART TX Signal Analysis
**Target**: Zybo Z7-20 UART TX pin (JA1 pin 2)
**Measurements Required**:
- Signal levels (3.3V LVCMOS verification)
- Baud rate accuracy (115200 baud)
- Rise/fall times
- Jitter and signal quality
- Bit pattern verification for known data (0x20)

#### B. Alternative UART Tool Testing
**Tools**: Tera Term, PuTTY, CoolTerm, RealTerm
**Purpose**: Isolate Python-specific vs hardware-wide issues
**Test Pattern**: Same FPGA signals with different PC-side reception tools

#### C. UART Configuration Verification
**Parameters**:
- Baud rate: 115200
- Data bits: 8
- Parity: None
- Stop bits: 1
- Flow control: None
- Clock accuracy and stability

#### D. Hardware Connection Analysis
**Components**:
- USB-UART cable integrity
- Pin connections (TX, RX, GND)
- Signal path electrical characteristics
- Alternative USB-UART adapter testing

#### E. FPGA I/O Configuration
**Verification Points**:
- Vivado constraint file (.xdc) settings
- I/O standard (LVCMOS33)
- Drive strength and slew rate
- Pin assignment accuracy

### 🎯 Expected Outcomes

#### Scenario 1: UART TX Signal Correct
- Oscilloscope shows proper 0x20 transmission
- Problem isolated to PC-side reception
- Solution: USB-UART driver or cable issues

#### Scenario 2: UART TX Signal Incorrect
- Oscilloscope shows 0x48 transmission
- Problem in FPGA physical layer
- Solution: I/O settings or timing issues

#### Scenario 3: Intermittent Issues
- Signal quality problems (jitter, timing)
- Baud rate inaccuracy
- Solution: Clock configuration or I/O optimization

### 🛠️ Required Equipment

- **Oscilloscope**: For signal analysis
- **Alternative UART Tools**: Multiple software options
- **Test Cables**: Backup USB-UART adapters
- **Multimeter**: For electrical verification
- **Documentation**: Zybo Z7-20 schematic and pin assignments

### 📊 Success Criteria

1. **Root Cause Identified**: Clear understanding of 0x20→0x48 conversion point
2. **Reproducible Solution**: Consistent fix across all test scenarios
3. **Documentation Complete**: Detailed analysis and resolution steps
4. **Verification Passed**: End-to-end communication working correctly

---

**Phase 5 Status**: 🚀 INITIATED
**Current Focus**: Oscilloscope UART TX signal measurement
**Next Milestone**: Physical layer characterization complete