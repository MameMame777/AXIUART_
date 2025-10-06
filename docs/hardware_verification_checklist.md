# Hardware Connection & Electrical Verification Guide
## Phase 5: Physical Layer Investigation

### 🎯 Objective
Verify all hardware connections, cable integrity, and electrical characteristics to ensure proper UART signal transmission between FPGA and PC.

### 📋 Hardware Verification Checklist

#### A. Zybo Z7-20 FPGA Board Inspection
- [ ] **Power Status**
  - LD9 (Power LED) illuminated
  - Board receives stable 5V via USB or external supply
  - No overheating or abnormal conditions

- [ ] **FPGA Configuration Status**
  - LD10 (DONE LED) illuminated (bitstream loaded successfully)
  - No configuration errors in Vivado Hardware Manager
  - Latest bitstream with Phase 4 RTL fixes programmed

- [ ] **UART Pin Physical Inspection**
  - JA1 connector properly seated
  - Pin 2 (UART TX) - no physical damage
  - Pin 3 (UART RX) - proper connection
  - Pin 6 (GND) - secure ground connection

#### B. USB-UART Cable Analysis

##### Primary Cable (Current Setup)
- [ ] **Cable Type & Model**
  - Record exact model/manufacturer: ________________
  - Cable length: ________________
  - USB connector type: ________________

- [ ] **Physical Inspection**
  - No visible damage to connectors
  - No kinks or stress points in cable
  - Secure USB connection to PC
  - Proper insertion into FPGA connector

- [ ] **Electrical Continuity Test**
  - Multimeter test: FPGA TX → PC RX
  - Multimeter test: FPGA RX → PC TX  
  - Multimeter test: FPGA GND → PC GND
  - Resistance values within normal range (< 5Ω)

##### Alternative Cable Testing
- [ ] **Secondary USB-UART Cable**
  - Test with different USB-UART adapter
  - Different manufacturer/chipset if available
  - Record comparative results

#### C. Signal Integrity Measurements

##### Oscilloscope Measurements (UART TX - JA1 Pin 2)
- [ ] **DC Voltage Levels**
  - Logic HIGH: ______ V (expected: ~3.3V)
  - Logic LOW: ______ V (expected: ~0V)
  - Idle state: ______ V (expected: ~3.3V)

- [ ] **AC Characteristics**
  - Rise time: ______ ns (10%-90%)
  - Fall time: ______ ns (90%-10%)
  - Overshoot: ______ V
  - Undershoot: ______ V

- [ ] **Timing Measurements**
  - Bit period: ______ μs (expected: 8.68 μs for 115200 baud)
  - Start bit width: ______ μs
  - Stop bit width: ______ μs
  - Jitter (peak-to-peak): ______ ns

- [ ] **Data Integrity**
  - Test byte 0x20: Pattern ______ (expected: specific bit sequence)
  - Test byte 0x55: Pattern ______ (alternating bits reference)
  - Verify bit patterns match expected UART format

##### Multimeter DC Verification
- [ ] **Static Measurements**
  - FPGA 3.3V rail: ______ V
  - USB-UART adapter 3.3V: ______ V
  - Ground potential difference: ______ V (should be ~0V)

#### D. PC-Side Reception Analysis

##### Device Manager Verification
- [ ] **COM Port Status**
  - COM port number: ______
  - Driver version: ______
  - No warning or error indicators
  - Advanced settings (buffer sizes, etc.): ______

- [ ] **USB Hub Analysis**
  - Direct USB connection vs hub
  - USB 2.0 vs USB 3.0 port
  - Power management settings disabled

##### Alternative PC Testing
- [ ] **Different PC/Laptop**
  - Test same setup on different computer
  - Compare results: ______
  - Isolate PC-specific issues

#### E. FPGA I/O Configuration Verification

##### Vivado Constraint File (.xdc) Review
```tcl
# UART TX (JA1 Pin 2)
set_property PACKAGE_PIN G13 [get_ports uart_tx]
set_property IOSTANDARD LVCMOS33 [get_ports uart_tx]
set_property DRIVE 12 [get_ports uart_tx]
set_property SLEW FAST [get_ports uart_tx]

# UART RX (JA1 Pin 3)  
set_property PACKAGE_PIN B11 [get_ports uart_rx]
set_property IOSTANDARD LVCMOS33 [get_ports uart_rx]
```

- [ ] **Pin Assignment Verification**
  - UART TX: Pin G13 → JA1 Pin 2 ✅
  - UART RX: Pin B11 → JA1 Pin 3 ✅
  - Schematic cross-reference confirmed

- [ ] **I/O Standard Settings**
  - IOSTANDARD: LVCMOS33 (3.3V logic)
  - DRIVE: 12mA (sufficient for short connections)
  - SLEW: FAST (adequate rise/fall times)

- [ ] **Timing Constraints**
  - No conflicting timing constraints
  - Clock domain properly defined
  - Setup/hold margins adequate

#### F. Environmental Factors

##### Temperature & Operating Conditions
- [ ] **Ambient Temperature**: ______ °C
- [ ] **FPGA Board Temperature**: Normal/Warm/Hot
- [ ] **Humidity Level**: ______ % (if measurable)
- [ ] **Vibration/Movement**: Minimal during testing

##### Power Supply Quality
- [ ] **USB Power Stability**
  - Measure with oscilloscope if available
  - 5V ± 5% tolerance
  - Low noise/ripple

### 🔧 Test Procedures

#### Procedure 1: Cable Swapping Test
1. Document current configuration and symptoms
2. Replace USB-UART cable with known-good alternative
3. Re-run Python test: `python test_registers_updated.py`
4. Compare results:
   - Same 0x20→0x48 conversion → Hardware/FPGA issue
   - Correct 0x20 reception → Cable issue
   - Different pattern → Cable-dependent issue

#### Procedure 2: Direct Oscilloscope Verification
1. Connect oscilloscope probe to JA1 Pin 2 (UART TX)
2. Run: `python oscilloscope_uart_test.py`
3. Trigger on falling edge (start bit)
4. Capture 0x20 transmission
5. Verify bit-by-bit pattern matches 0x20 (00100000)
6. Document any discrepancies

#### Procedure 3: Signal Path Isolation
1. Measure FPGA TX pin directly (closest to source)
2. Measure at USB-UART adapter input
3. Measure at PC USB connector
4. Identify where signal degradation/conversion occurs

#### Procedure 4: Ground Loop Investigation
1. Check ground potential between FPGA and PC
2. Try different grounding arrangements
3. Test with isolated USB-UART adapter if available

### 📊 Results Documentation

#### Hardware Verification Results
```
Date: ________________
Tester: ________________

Cable Test Results:
- Primary cable: ________________
- Alternative cable: ________________
- Conversion persists: Y/N

Oscilloscope Results:
- Signal levels correct: Y/N
- Timing accurate: Y/N
- 0x20 pattern verified: Y/N
- Observed pattern: ________________

Root Cause Identified:
- Location: ________________
- Description: ________________
- Confidence: High/Medium/Low
```

#### Recommended Solutions (Based on Findings)

##### If Cable Issue:
- Replace USB-UART cable
- Use different connector type
- Check cable specifications

##### If FPGA I/O Issue:
- Adjust drive strength
- Modify slew rate
- Verify pin assignments

##### If Signal Integrity Issue:
- Add termination resistors
- Shorten cable length
- Improve grounding

##### If PC-Side Issue:
- Update USB-UART drivers
- Change USB port
- Test on different PC

### 🎯 Success Criteria
- [ ] Root cause of 0x20→0x48 conversion identified
- [ ] Specific component/layer causing issue isolated
- [ ] Reproducible solution developed and tested
- [ ] Documentation complete for future reference

---

**Status**: Phase 5 Hardware Investigation
**Next Step**: Execute verification procedures and document findings