# AXIUART System Architecture

This document describes the complete architecture of the AXIUART system, including the integration of the UART-AXI4 bridge with the register block and top-level system organization.

## System Overview

The AXIUART system implements a complete UART to AXI4-Lite bridge with integrated register-based control and status monitoring. The system provides a bridge between UART serial communication and AXI4-Lite memory-mapped interfaces, with comprehensive configuration and monitoring capabilities.

```text
┌─────────────────────────────────────────────────────────────────┐
│                        AXIUART_Top                             │
│  ┌─────────────────┐    ┌──────────────────────────────────┐  │
│  │                 │    │                                  │  │
│  │ Register_Block  │    │      Uart_Axi4_Bridge            │  │
│  │                 │    │                                  │  │
│  │ - CONTROL       │◄──►│ ┌──────────┐  ┌─────────────┐    │  │
│  │ - STATUS        │    │ │ Frame    │  │ AXI4-Lite   │    │　|
│  │ - CONFIG        │    │ │ Parser   │  │ Master      │    │  │   
│  │ - DEBUG         │    │ └──────────┘  └─────────────┘    │  │
│  │ - Counters      │    │ ┌──────────┐  ┌─────────────┐    │  │
│  │ - Version       │    │ │ Frame    │  │ UART        │    │  │
│  │                 │    │ │ Builder  │  │ Rx/Tx       │    │◄─┼─► UART
│  └─────────────────┘    │ └──────────┘  └─────────────┘    │  │
│                         │ ┌──────────┐  ┌─────────────┐   │  │
│                         │ │ CRC8     │  │ FIFO        │   │  │
│                         │ │ Calc     │  │ Sync        │   │  │
│                         │ └──────────┘  └─────────────┘   │  │
│                         └──────────────────────────────────┘ │
│───────────────────────────────────────────────────────────────┘
```

## Component Architecture

### Top-Level Module: AXIUART_Top

The `AXIUART_Top` module serves as the complete system integration point, providing:

- **Clock and Reset Management**: Distributes system clock and manages reset sequencing
- **Interface Integration**: Connects UART and AXI4-Lite interfaces
- **Address Routing**: Routes register accesses (0x1000-0x1FFF) to internal register block
- **System Status**: Provides high-level system status and error reporting
- **Parameter Configuration**: Allows system-wide parameter customization

**Key Features:**

- Parameterizable clock frequency, baud rates, and FIFO depths
- Integrated enable/disable control through register block
- System-level status monitoring and error aggregation
- Clean separation between register access and external AXI transactions

### Register Block: Register_Block

The register block provides memory-mapped control and status for the UART bridge:

**Control Registers:**

- **CONTROL (0x1000)**: System enable, statistics reset
- **CONFIG (0x1008)**: UART and AXI configuration parameters
- **DEBUG (0x100C)**: Debug mode selection and control

**Status Registers:**

- **STATUS (0x1004)**: Bridge busy flag and error codes
- **TX_COUNT/RX_COUNT (0x1010/0x1014)**: Transaction counters
- **FIFO_STAT (0x1018)**: FIFO status and level monitoring
- **VERSION (0x101C)**: Hardware version identification

**Architecture Features:**

- Full AXI4-Lite slave compliance with proper handshaking
- Address decoding with SLVERR responses for invalid/unaligned addresses
- Register field access control (RW/RO/W1C behaviors)
- Synchronous reset with well-defined reset values

Further details on CONTROL register disable timing, BUSY semantics, and verification expectations are documented in [`docs/register_map.md`](./register_map.md#control-register-0x1000) and [`docs/uvm_verification_plan.md`](./uvm_verification_plan.md#disable-enable-verification-scenarios).

### UART-AXI4 Bridge: Uart_Axi4_Bridge

The existing bridge module handles the core protocol translation:

- **UART Protocol**: Full-duplex serial communication with configurable baud rates
- **Frame Processing**: Protocol frame parsing/building with CRC8 error detection
- **AXI4-Lite Master**: Generates memory-mapped transactions to external systems
- **FIFO Buffering**: Synchronous FIFOs for RX/TX data buffering
- **Error Handling**: Comprehensive error detection and reporting

## Address Space Organization

### Register Block Address Space (0x1000-0x1FFF)

The register block occupies a 4KB address space within the system:

```text
0x0000_1000  ┌─────────────────────────────────────────┐
             │ CONTROL      (0x000)                   │
             ├─────────────────────────────────────────┤
             │ STATUS       (0x004)                   │
             ├─────────────────────────────────────────┤
             │ CONFIG       (0x008)                   │
             ├─────────────────────────────────────────┤
             │ DEBUG        (0x00C)                   │
             ├─────────────────────────────────────────┤
             │ TX_COUNT     (0x010)                   │
             ├─────────────────────────────────────────┤
             │ RX_COUNT     (0x014)                   │
             ├─────────────────────────────────────────┤
             │ FIFO_STAT    (0x018)                   │
             ├─────────────────────────────────────────┤
             │ VERSION      (0x01C)                   │
             ├─────────────────────────────────────────┤
             │ Reserved     (0x020-0xFFF)             │
             │ (Returns SLVERR)                       │
0x0000_1FFF  └─────────────────────────────────────────┘
```

### External AXI Address Space

All addresses outside the 0x1000-0x1FFF range are passed through to the external AXI master interface, allowing the UART bridge to access:

- External memory devices
- Peripheral registers
- System interconnect components
- Custom user logic

## Signal Flow and Data Path

### UART Reception Path

1. **UART Rx** → Serial data reception and frame validation
2. **RX FIFO** → Data buffering and flow control  
3. **Frame Parser** → Protocol frame parsing and CRC validation
4. **AXI Master** → Memory-mapped write transaction generation
5. **Register Block** → Status updates and counter increments

### UART Transmission Path

1. **AXI Master** → Memory-mapped read transaction generation
2. **Frame Builder** → Protocol frame construction with CRC generation
3. **TX FIFO** → Data buffering and transmission scheduling
4. **UART Tx** → Serial data transmission
5. **Register Block** → Status updates and counter increments

### Register Access Path

1. **AXI Master Interface** → Incoming register access requests
2. **Address Router** → Decode between register block and external access
3. **Register Block** → AXI4-Lite slave interface processing
4. **Register Logic** → Field updates, access control, response generation
5. **Bridge Control** → Configuration updates to UART bridge

## Clock and Reset Architecture

### Clock Distribution

```text
clk (50MHz) ──┬── AXIUART_Top
              ├── Register_Block
              ├── Uart_Axi4_Bridge
              └── All internal components
```

### Reset Strategy

- **External Reset**: Active-high synchronous reset input
- **Bridge Reset**: Controlled by register block enable bit
- **Reset Sequencing**: Register block remains operational during bridge reset
- **Statistics Reset**: Separate pulse-based reset for counters

```text
rst (external) ──┬── Register_Block (always)
                 └── Uart_Axi4_Bridge (gated by enable)

bridge_enable ───┬── Enable gate for bridge reset
                 └── Bridge operational control
```

## Interface Specifications

### External UART Interface

- **uart_rx**: Input serial data line
- **uart_tx**: Output serial data line
- **Electrical**: Standard UART voltage levels (3.3V/5V compatible)
- **Protocol**: Configurable baud rate, 8N1 frame format

### External AXI4-Lite Master Interface

- **Address Width**: 32 bits
- **Data Width**: 32 bits  
- **Protocol**: Full AXI4-Lite compliance
- **Usage**: Memory-mapped access to external systems

### System Status Interface

- **system_busy**: High when any transaction is active
- **system_error**: Current error code (8 bits)
- **system_ready**: High when system is enabled and operational

## Configuration and Parameterization

### Compile-Time Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| CLK_FREQ_HZ | 50_000_000 | System clock frequency |
| BAUD_RATE | 115200 | UART baud rate |
| AXI_TIMEOUT | 1000 | AXI transaction timeout (clock cycles) |
| UART_OVERSAMPLE | 16 | UART oversampling factor |
| RX_FIFO_DEPTH | 64 | RX FIFO depth |
| TX_FIFO_DEPTH | 64 | TX FIFO depth |
| MAX_LEN | 16 | Maximum frame length |
| REG_BASE_ADDR | 0x1000 | Register block base address |

### Runtime Configuration

Runtime configuration is performed through the register interface:

- **Baud Rate**: Configurable through CONFIG register
- **Timeouts**: AXI timeout configuration
- **Debug Modes**: Debug feature selection
- **Enable Control**: System enable/disable

## Error Handling and Diagnostics

### Error Detection

- **UART Errors**: Frame errors, parity errors, overrun
- **AXI Errors**: Protocol violations, timeout errors
- **CRC Errors**: Frame integrity validation failures
- **FIFO Errors**: Overflow/underflow conditions

### Error Reporting

- **STATUS Register**: Current error code and busy flag
- **Error Codes**: Categorized error identification (0x00-0xFF)
- **Statistics**: Transaction counters for performance monitoring
- **Debug Modes**: Enhanced diagnostic capabilities

### Recovery Mechanisms

- **Soft Reset**: Statistics and error counter reset
- **Bridge Disable**: Complete bridge shutdown and restart
- **FIFO Flush**: Buffer clearing for error recovery
- **Timeout Handling**: Automatic recovery from stuck transactions

## Verification Strategy

The system verification follows a comprehensive UVM-based approach:

### Test Coverage Areas

1. **Register Verification**: All register fields, access types, and error responses
2. **Protocol Verification**: UART and AXI4-Lite protocol compliance
3. **Integration Testing**: End-to-end system functionality
4. **Error Injection**: Fault tolerance and recovery testing
5. **Performance Testing**: Throughput and latency characterization

### Coverage Metrics

- **Functional Coverage**: ≥90% for all feature areas
- **Code Coverage**: ≥90% for all RTL modules
- **Branch Coverage**: ≥90% for all decision points
- **Toggle Coverage**: ≥90% for all signals

## Design Considerations

### Synthesis and Implementation

- **Target Technology**: FPGA (Xilinx/Intel) and ASIC compatible
- **Clock Domains**: Single clock domain design for simplicity
- **Reset Strategy**: Synchronous reset for reliable startup
- **Resource Usage**: Optimized for area and power efficiency

### Performance Characteristics

- **Maximum Baud Rate**: Up to 1 Mbps (with 50MHz clock)
- **AXI Transaction Latency**: <100 clock cycles typical
- **FIFO Buffer Size**: Configurable depth for throughput optimization
- **Throughput**: Limited by UART baud rate and AXI response time

### Scalability and Extensibility

- **Additional Registers**: Reserved address space for future expansion
- **Protocol Extensions**: Framework for enhanced UART protocols
- **Multi-Channel**: Architecture supports multiple UART channels
- **Custom Features**: Debug hooks and configuration options

---

**Document Version**: 1.0
**Last Updated**: September 2025
**Architecture Version**: AXIUART v1.0.0
