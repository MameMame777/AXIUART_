# UART-AXI4-Lite Bridge - Design Overview

## Project Description

This project implements a production-quality UART to AXI4-Lite bridge in SystemVerilog, enabling serial communication protocols to interface with memory-mapped AXI4-Lite bus systems. The design includes comprehensive UVM verification environment with full coverage collection and protocol checking.

## Architecture Overview

### System Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                  UART-AXI4 Bridge System                       │
├─────────────────┬───────────────────────────┬─────────────────────┤
│   UART RX/TX    │    Protocol Processing    │   AXI4-Lite Master │
│   Interface     │                           │    Interface        │
├─────────────────┼───────────────────────────┼─────────────────────┤
│ • 8N1 Format    │ • Frame Parser           │ • Read/Write Trans  │
│ • 115200 Baud   │ • Frame Builder          │ • Address Alignment │  
│ • CRC8 Check    │ • Command Decode         │ • Response Handling │
│ • FIFO Buffers  │ • Data Validation        │ • Timeout Handling  │
└─────────────────┴───────────────────────────┴─────────────────────┘
```

### Key Components

#### 1. UART Interface Module (`Uart_Rx.sv`, `Uart_Tx.sv`)
- **Purpose**: Handles serial communication with 8N1 format
- **Features**:
  - 16x oversampling for robust reception
  - Configurable baud rate (default: 115200)  
  - Start/stop bit detection and validation
  - Parity error detection (if enabled)
  - FIFO buffering for TX/RX data

#### 2. Protocol Processing (`Frame_Parser.sv`, `Frame_Builder.sv`) 
- **Purpose**: Implements custom UART-AXI protocol per specification
- **Frame Parser Features**:
  - State machine-driven frame parsing
  - CRC8 validation with polynomial 0x07
  - Command field validation
  - Timeout handling for incomplete frames
  - Data extraction with configurable lengths

- **Frame Builder Features**:
  - Response frame construction
  - Status code generation
  - CRC8 calculation for outgoing frames
  - Echo-back command/address fields

#### 3. AXI4-Lite Master (`Axi4_Lite_Master.sv`)
- **Purpose**: Performs memory-mapped transactions on AXI bus
- **Features**:
  - Read/write transaction handling
  - Address alignment checking and correction
  - WSTRB generation for partial writes
  - Response collection and status mapping
  - Timeout handling for bus transactions

#### 4. Supporting Components
- **CRC8 Calculator** (`Crc8_Calculator.sv`): Hardware CRC implementation
- **Address Aligner** (`Address_Aligner.sv`): Ensures AXI address alignment
- **Synchronous FIFO** (`fifo_sync.sv`): 64-deep buffering with flow control

## Protocol Specification

### Frame Format

#### Host-to-Device Frame
```
┌─────┬─────┬──────────┬─────────┬─────┐
│ SOF │ CMD │ ADDRESS  │  DATA   │ CRC │
│ 1B  │ 1B  │   4B     │ 0-4B    │ 1B  │
└─────┴─────┴──────────┴─────────┴─────┘
```

#### Device-to-Host Frame  
```
┌─────┬────────┬─────┬──────────┬─────────┬─────┐
│ SOF │ STATUS │ CMD │ ADDRESS  │  DATA   │ CRC │
│ 1B  │   1B   │ 1B  │   4B     │ 0-4B    │ 1B  │
└─────┴────────┴─────┴──────────┴─────────┴─────┘
```

### Command Structure

| Bit 7 | Bits 6:4 | Bits 3:0 |
|-------|----------|----------|
| R/W   | Length   | Reserved |

- **R/W**: 0=Write, 1=Read  
- **Length**: 001=1B, 010=2B, 100=4B
- **Reserved**: Must be 0000

### Status Codes

| Code | Name | Description |
|------|------|-------------|
| 0x00 | OK | Transaction successful |
| 0x01 | CRC_ERROR | Frame CRC validation failed |
| 0x02 | TIMEOUT | AXI transaction timeout |
| 0x03 | INVALID_CMD | Invalid command format |
| 0x04 | ALIGNMENT_ERROR | Address alignment violation |
| 0x05 | AXI_ERROR | AXI bus error response |

## Timing Specifications

### UART Timing
- **Baud Rate**: 115200 bps (configurable)
- **Bit Time**: 8.68 μs  
- **Frame Timeout**: 1 ms maximum
- **Inter-byte Gap**: 5-20 clock cycles

### AXI4-Lite Timing  
- **Clock Frequency**: 50 MHz system clock
- **Transaction Timeout**: 1000 clock cycles (20 μs)
- **Response Delay**: 1-10 clock cycles typical

## Directory Structure

```
AXIUART_/
├── docs/                          # Documentation
│   ├── uart_axi4_protocol.md     # Protocol specification  
│   ├── design_overview.md         # This document
│   ├── uvm_testplan.md           # Verification plan
│   └── run_guide.md              # User guide
├── rtl/                          # RTL Implementation
│   ├── interfaces/               # SystemVerilog interfaces
│   │   ├── uart_if.sv           # UART interface
│   │   └── axi4_lite_if.sv      # AXI4-Lite interface  
│   ├── Uart_Axi4_Bridge.sv      # Top-level bridge
│   ├── Uart_Rx.sv               # UART receiver
│   ├── Uart_Tx.sv               # UART transmitter
│   ├── Frame_Parser.sv           # Protocol frame parser
│   ├── Frame_Builder.sv          # Protocol frame builder
│   ├── Axi4_Lite_Master.sv       # AXI master controller
│   ├── Address_Aligner.sv        # Address alignment
│   ├── Crc8_Calculator.sv        # CRC8 implementation
│   └── fifo_sync.sv              # Synchronous FIFO
└── sim/                          # Verification Environment  
    └── uvm/                      # UVM testbench
        ├── packages/             # UVM packages
        ├── env/                  # Environment classes
        ├── agents/               # UVM agents  
        ├── sequences/            # Test sequences
        ├── tests/                # Test classes
        ├── tb/                   # Testbench top
        ├── dsim_config.f         # DSIM file list
        ├── run_uvm.ps1           # Test runner script
        └── universal_uvm_runner.ps1 # Universal runner
```

## Performance Characteristics

### Throughput Analysis
- **Theoretical Maximum**: 115200 bps / 10 bits = 11.52 KB/s
- **Protocol Overhead**: ~7 bytes per transaction minimum
- **Effective Throughput**: ~8-10 KB/s for 4-byte transactions
- **Latency**: 200-500 μs typical frame processing time

### Resource Utilization (Estimated)
- **Logic Elements**: ~1500-2000 LEs
- **Memory Bits**: ~2048 bits (FIFO buffers)  
- **Maximum Frequency**: 100+ MHz (design target: 50 MHz)

## Verification Strategy

### UVM Testbench Architecture
```
┌─────────────────────────────────────────────────────────┐
│                UVM Test Environment                     │
├─────────────────┬─────────────────┬─────────────────────┤
│  UART Agent     │   Environment   │  AXI4-Lite Agent   │
│  (Active)       │                 │    (Passive)        │
├─────────────────┼─────────────────┼─────────────────────┤
│ • Driver        │ • Scoreboard    │ • Monitor          │
│ • Monitor       │ • Coverage      │ • Protocol Check   │
│ • Sequencer     │ • Configuration │ • Coverage         │
└─────────────────┴─────────────────┴─────────────────────┘
```

### Test Coverage Areas
1. **Functional Coverage**
   - All command types (read/write, 1/2/4 byte)
   - Address patterns (aligned/misaligned)
   - Data patterns (all 0s, all 1s, walking patterns)
   - Error conditions (CRC errors, timeouts, invalid commands)

2. **Protocol Coverage**
   - Frame format compliance  
   - CRC calculation accuracy
   - Response timing requirements
   - Error handling completeness

3. **Performance Coverage**
   - Throughput measurements
   - Latency analysis
   - Burst transaction handling
   - Stress testing scenarios

### Test Scenarios
- **Basic Functionality**: Read/write operations, data integrity
- **Error Injection**: CRC errors, protocol violations, timeouts  
- **Performance**: Burst operations, back-to-back transactions
- **Boundary Conditions**: Edge cases, resource limits
- **Stress Testing**: Extended operation, error recovery

## Design Decisions and Rationale

### 1. CRC8 Selection
- **Polynomial**: 0x07 (x^8 + x^2 + x + 1)
- **Rationale**: Good error detection for short frames, hardware efficient

### 2. FIFO Depth Selection
- **Size**: 64 entries deep  
- **Rationale**: Balance between resource usage and burst handling capability

### 3. Timeout Values
- **Frame Timeout**: 1 ms - allows for transmission delays
- **AXI Timeout**: 20 μs - prevents bus lockup while allowing slow slaves

### 4. Address Alignment Strategy
- **Approach**: Automatic alignment with size-appropriate boundaries
- **Rationale**: Ensures AXI compliance while maximizing compatibility

## Future Enhancements

### Planned Improvements
1. **Multi-Master Support**: Support for multiple concurrent AXI masters
2. **Enhanced Error Recovery**: More sophisticated error handling mechanisms  
3. **Performance Optimization**: Pipeline improvements for higher throughput
4. **Protocol Extensions**: Support for additional command types
5. **Security Features**: Authentication and encryption capabilities

### Scalability Considerations
- **FIFO Sizing**: Configurable depth for different applications
- **Clock Domain Crossing**: Support for independent UART and AXI clocks
- **Multiple Channels**: Support for multiple independent UART channels
- **Protocol Versioning**: Framework for backward-compatible extensions

## Quality Assurance

### Verification Completeness
- **Functional Coverage**: Target >95% coverage of all features
- **Code Coverage**: Target >90% line and branch coverage  
- **Protocol Compliance**: 100% adherence to specification
- **Performance Validation**: Meet all timing requirements

### Testing Standards
- **UVM Methodology**: Industry-standard verification approach
- **Constrained Random**: Comprehensive stimulus generation
- **Assertion-Based**: RTL and protocol assertion monitoring
- **Regression Testing**: Automated test suite execution

### Documentation Standards
- **Design Documentation**: Complete architectural descriptions
- **Verification Plans**: Detailed coverage and test strategies  
- **User Guides**: Comprehensive usage instructions
- **API Documentation**: Complete interface specifications

---

**Document Version**: 1.0  
**Last Updated**: January 27, 2025  
**Author**: SystemVerilog Design Team  
**Review Status**: Final