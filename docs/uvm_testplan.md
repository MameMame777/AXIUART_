# UVM Verification Test Plan for UART-AXI4 Bridge

## Document Information

| Field | Value |
|-------|-------|
| **Document Title** | UVM Verification Test Plan |
| **Project** | UART-AXI4-Lite Bridge |
| **Version** | 1.0 |
| **Date** | January 27, 2025 |
| **Status** | Final |
| **Author** | SystemVerilog Verification Team |

## Table of Contents

1. [Verification Overview](#verification-overview)
2. [Verification Environment](#verification-environment)
3. [Test Coverage Plan](#test-coverage-plan)
4. [Test Scenarios](#test-scenarios)
5. [Coverage Metrics](#coverage-metrics)
6. [Test Execution Strategy](#test-execution-strategy)
7. [Pass/Fail Criteria](#passfail-criteria)
8. [Resource Requirements](#resource-requirements)

## Verification Overview

### Verification Goals

The primary objective is to comprehensively verify the UART-AXI4-Lite bridge design through systematic testing that covers:

- **Functional Correctness**: All protocol operations work according to specification
- **Protocol Compliance**: Both UART and AXI4-Lite protocols are correctly implemented  
- **Error Handling**: Proper response to all error conditions
- **Performance**: Meeting timing and throughput requirements
- **Robustness**: Operation under stress and boundary conditions

### Verification Methodology

This verification plan follows UVM (Universal Verification Methodology) best practices:

- **Layered Testbench Architecture**: Modular, reusable components
- **Constrained Random Testing**: Comprehensive stimulus coverage  
- **Functional Coverage**: Systematic feature coverage collection
- **Assertion-Based Verification**: Protocol and RTL property checking
- **Self-Checking Environment**: Automatic result verification

### Design Under Test (DUT)

**Module**: `Uart_Axi4_Bridge`

**Primary Interfaces**:
- UART RX/TX signals (serial communication)
- AXI4-Lite master interface (memory-mapped bus)
- Clock and reset (system control)

**Key Features to Verify**:
- UART frame parsing and building
- AXI4-Lite transaction generation
- CRC8 calculation and validation
- Address alignment handling
- Error detection and reporting
- FIFO management and flow control

## Verification Environment

### UVM Testbench Architecture

```text
                        ┌─────────────────────────┐
                        │    UVM Test Classes     │
                        └─────────────────────────┘
                                    │
                        ┌─────────────────────────┐
                        │   UVM Environment       │
                        │  ┌─────────────────────┐│
                        │  │   Scoreboard        ││
                        │  │   Coverage          ││
                        │  │   Configuration     ││
                        │  └─────────────────────┘│
                        └─────────────────────────┘
                                    │
                ┌───────────────────────────────────────┐
                │                                       │
    ┌─────────────────────┐                ┌─────────────────────┐
    │   UART Agent        │                │ AXI4-Lite Agent     │
    │  ┌─────────────────┐│                │ ┌─────────────────┐ │
    │  │ Driver          ││                │ │ Monitor         │ │
    │  │ Monitor         ││                │ │ Coverage        │ │
    │  │ Sequencer       ││                │ │ Protocol Check  │ │
    │  │ Coverage        ││                │ └─────────────────┘ │
    │  └─────────────────┘│                └─────────────────────┘
    └─────────────────────┘
            │                                       │
            │                                       │
    ┌─────────────────────┐                ┌─────────────────────┐
    │   UART Interface    │                │ AXI4-Lite Interface │
    └─────────────────────┘                └─────────────────────┘
            │                                       │
            └─────────────────┬─────────────────────┘
                              │
                    ┌─────────────────────┐
                    │       DUT           │
                    │ Uart_Axi4_Bridge    │
                    └─────────────────────┘
```

### Environment Components

#### 1. UART Agent (Active)

**Purpose**: Drive UART protocol transactions and monitor responses

**Components**:
- **Driver**: Generates UART frames according to protocol specification
- **Monitor**: Captures and analyzes UART traffic for coverage and checking
- **Sequencer**: Controls transaction ordering and timing
- **Coverage**: Collects UART-specific functional coverage

**Key Responsibilities**:
- Generate valid and invalid UART frames
- Implement CRC8 calculation for transmitted frames  
- Monitor receive path for response frames
- Collect protocol-level coverage data
- Support error injection scenarios

#### 2. AXI4-Lite Agent (Passive)

**Purpose**: Monitor AXI4-Lite bus transactions and provide memory responses

**Components**:
- **Monitor**: Observes all AXI4-Lite transactions  
- **Coverage**: Collects AXI-specific coverage metrics
- **Protocol Checker**: Validates AXI4-Lite protocol compliance

**Key Responsibilities**:
- Monitor read/write transactions on AXI bus
- Verify address alignment and transaction validity
- Collect coverage for AXI transaction patterns
- Check protocol timing requirements
- Provide memory model for transaction responses

#### 3. Scoreboard

**Purpose**: Transaction-level checking and result verification

**Key Functions**:
- **Transaction Correlation**: Match UART commands with AXI transactions
- **Data Integrity**: Verify data consistency across interfaces
- **Response Validation**: Check status codes and response timing
- **Error Detection**: Identify unexpected behaviors or protocol violations

**Checking Strategy**:
- Reference model comparison for expected vs. actual results
- End-to-end data flow verification
- Protocol compliance checking
- Performance metrics collection

#### 4. Coverage Collector

**Purpose**: Systematic coverage collection across all verification aspects

**Coverage Areas**:
- **Command Coverage**: All command types and combinations
- **Data Coverage**: Various data patterns and lengths
- **Address Coverage**: Alignment scenarios and address ranges  
- **Error Coverage**: All error conditions and recovery paths
- **Protocol Coverage**: Frame formats and timing scenarios

#### 5. Configuration Object

**Purpose**: Centralized test configuration and parameter management

**Configuration Parameters**:
- Clock frequencies and timing parameters
- UART baud rate and protocol settings
- AXI bus characteristics and timing
- Test-specific behavior controls
- Coverage collection controls

## Test Coverage Plan

### Functional Coverage

#### 1. Command Coverage

**Coverage Points**:

```systemverilog
covergroup command_coverage;
    // Basic command structure
    cp_read_write: coverpoint cmd[7] {
        bins read = {1};
        bins write = {0};
    }
    
    cp_data_length: coverpoint cmd[6:4] {
        bins one_byte = {3'b001};
        bins two_bytes = {3'b010}; 
        bins four_bytes = {3'b100};
        illegal_bins invalid = default;
    }
    
    cp_reserved_bits: coverpoint cmd[3:0] {
        bins zero = {4'b0000};
        illegal_bins non_zero = default;
    }
    
    // Cross coverage
    cross_cmd_type: cross cp_read_write, cp_data_length;
endgroup
```

**Target**: 100% coverage of all valid command combinations

#### 2. Address Coverage

**Coverage Points**:
- Address alignment patterns (word, half-word, byte)
- Address ranges (low, mid, high, boundary values)
- Alignment violations for error testing
- Address incremental patterns for burst testing

**Target**: 95% coverage of address space and alignment scenarios

#### 3. Data Pattern Coverage

**Coverage Points**:
- Data values: all zeros, all ones, alternating patterns
- Walking bit patterns (walking 0s and 1s)
- Random data distributions  
- Boundary values (0x00, 0xFF, 0x55, 0xAA)

**Target**: 90% coverage of significant data patterns

#### 4. Error Scenario Coverage

**Coverage Points**:
- CRC error injection and handling
- Frame timeout scenarios
- Invalid command combinations
- Address misalignment errors
- AXI bus error responses
- Protocol violations

**Target**: 100% coverage of all error conditions

### Code Coverage

#### RTL Code Coverage

**Metrics**:
- **Line Coverage**: 95% minimum
- **Branch Coverage**: 90% minimum  
- **FSM Coverage**: 100% of states and transitions
- **Toggle Coverage**: 85% minimum

**Focus Areas**:
- State machine transitions in Frame_Parser and Frame_Builder
- Error handling paths in all modules
- FIFO full/empty conditions
- AXI protocol state machines

#### Testbench Code Coverage

**Metrics**:
- **Line Coverage**: 90% minimum
- **Branch Coverage**: 85% minimum

**Focus Areas**:
- All UVM components and methods
- Sequence execution paths  
- Coverage collection mechanisms
- Error injection and checking paths

### Protocol Coverage

#### UART Protocol Coverage

**Areas**:
- Frame format compliance (SOF, command, address, data, CRC)
- Bit timing and baud rate accuracy
- Start/stop bit detection
- CRC8 calculation correctness
- Frame timeout handling

**Target**: 100% protocol compliance verification

#### AXI4-Lite Protocol Coverage

**Areas**:
- Handshake protocol (valid/ready signaling)
- Address and data channel timing
- Response signaling and codes
- Transaction ordering and completion
- Protocol violation detection

**Target**: 100% AXI4-Lite specification compliance

## Test Scenarios

### 1. Basic Functional Tests

#### Test: `uart_axi4_basic_test`

**Objective**: Verify fundamental read/write operations

**Test Scenarios**:
- Single-byte read/write operations
- Multi-byte read/write operations (2, 4 bytes)
- Sequential address transactions
- Mixed read/write patterns
- Data integrity verification

**Success Criteria**:
- All transactions complete successfully
- Data integrity maintained end-to-end
- Correct status responses generated
- No protocol violations detected

**Duration**: ~10 minutes

#### Test: `uart_axi4_burst_perf_test`

**Objective**: Verify performance and burst transaction handling

**Test Scenarios**:
- Back-to-back transaction generation
- Burst read/write operations
- Throughput measurement  
- Latency analysis
- FIFO utilization testing

**Success Criteria**:
- Meet minimum throughput requirements (>0.5 Mbps)
- Average latency <500μs per transaction
- No FIFO overflow/underflow conditions
- Consistent performance across test duration

**Duration**: ~15 minutes

### 2. Error Path Tests

#### Test: `uart_axi4_error_paths_test`

**Objective**: Verify comprehensive error handling

**Test Scenarios**:
- CRC error injection and detection
- Frame timeout scenarios
- Invalid command formats
- Address misalignment handling
- AXI bus error responses
- Protocol violation recovery

**Success Criteria**:
- All error conditions properly detected
- Appropriate status codes generated
- System recovery after error conditions
- No system lockup or undefined states

**Duration**: ~20 minutes

### 3. Stress and Robustness Tests

#### Test: `uart_axi4_stress_test`

**Objective**: Verify operation under stress conditions

**Test Scenarios**:
- Extended operation (1M+ transactions)
- Continuous error injection with recovery
- Resource exhaustion scenarios
- Temperature and timing corner cases
- Concurrent multi-channel operation

**Success Criteria**:
- Stable operation over extended periods
- Proper error recovery mechanisms
- No memory leaks or resource exhaustion
- Consistent performance under stress

**Duration**: ~60 minutes

### 4. Protocol Compliance Tests

#### Test: `uart_axi4_protocol_compliance_test`

**Objective**: Verify strict protocol adherence

**Test Scenarios**:
- Frame format validation
- Timing requirement verification  
- Signal transition compliance
- Protocol state machine verification
- Cross-protocol interaction validation

**Success Criteria**:
- 100% protocol specification compliance
- No timing violations detected
- Proper state machine operation
- Clean interface behavior

**Duration**: ~30 minutes

## Coverage Metrics

### Coverage Targets

| Coverage Type | Target | Minimum |
|---------------|--------|---------|
| Functional Coverage | 95% | 90% |
| Line Coverage | 95% | 90% |
| Branch Coverage | 90% | 85% |
| FSM Coverage | 100% | 100% |
| Toggle Coverage | 85% | 80% |
| Assertion Coverage | 100% | 100% |

### Coverage Reporting

**Tools**: DSIM coverage collection and reporting

**Reports Generated**:
- Functional coverage report with detailed breakdown
- Code coverage report with exclusion analysis
- Cross-coverage analysis for complex scenarios
- Trend analysis across test runs
- Coverage closure tracking

**Review Process**:
- Daily coverage review during active development
- Weekly coverage closure meetings
- Coverage gaps analysis and closure plans
- Final coverage report for sign-off

## Test Execution Strategy

### Regression Test Suite

**Nightly Regression**:
- All basic functional tests
- Key error path scenarios  
- Performance baseline validation
- Coverage collection and reporting

**Weekly Regression**:
- Complete test suite execution
- All stress and robustness tests
- Protocol compliance validation
- Performance benchmarking

**Release Regression**:
- Full test suite with extended stress testing
- Cross-platform validation
- Performance characterization
- Documentation validation

### Test Execution Environment

**Required Tools**:
- DSIM simulator with UVM support
- Coverage collection and analysis tools
- Performance measurement utilities
- Regression automation framework

**Execution Platform**:
- High-performance simulation servers
- Parallel execution capability
- Automated result collection
- Performance monitoring and alerting

### Continuous Integration

**Automated Triggers**:
- Code check-in triggers regression subset
- Nightly full regression execution
- Performance trend monitoring
- Coverage tracking and reporting

**Result Processing**:
- Automatic pass/fail determination
- Performance regression detection
- Coverage trend analysis
- Failure debugging and triage

## Pass/Fail Criteria

### Test Pass Criteria

**Functional Requirements**:
- Zero UVM_ERROR or UVM_FATAL messages
- All transactions complete successfully
- Data integrity maintained across all paths
- Correct response generation for all scenarios

**Performance Requirements**:
- Minimum throughput: 0.5 Mbps effective
- Maximum latency: 500μs average per transaction
- FIFO utilization: <90% peak usage
- No resource exhaustion conditions

**Coverage Requirements**:
- Functional coverage: ≥95%
- Code coverage: ≥90% line, ≥85% branch
- Protocol coverage: 100% compliance
- Error coverage: 100% of error scenarios

### Test Fail Criteria

**Critical Failures**:
- Any UVM_FATAL messages
- Data corruption or integrity violations
- Protocol specification violations
- System lockup or undefined behavior

**Performance Failures**:
- Throughput below minimum requirements
- Excessive latency or timing violations
- Resource exhaustion or memory leaks
- Performance regression >10% from baseline

**Coverage Failures**:
- Functional coverage <90%
- Critical path coverage <100%
- Untested error conditions
- Protocol compliance gaps

## Resource Requirements

### Simulation Resources

**Compute Requirements**:
- Multi-core simulation servers (16+ cores)
- 32GB+ RAM per simulation instance
- High-speed storage for waveform capture
- Network access for license servers

**Software Requirements**:
- DSIM simulator with UVM library
- SystemVerilog compilation tools
- Coverage analysis and reporting tools
- Performance measurement utilities

### Human Resources

**Verification Team**:
- Lead Verification Engineer: Overall test planning and execution
- UVM Environment Developer: Testbench development and maintenance
- Test Developer: Sequence and test case development
- Coverage Analyst: Coverage analysis and closure

**Estimated Effort**:
- Test plan development: 1 week
- Environment development: 3-4 weeks
- Test development: 2-3 weeks  
- Execution and debug: 2-3 weeks
- Coverage closure: 1-2 weeks

**Total Project Duration**: 8-12 weeks

### Timeline and Milestones

| Milestone | Duration | Deliverables |
|-----------|----------|-------------|
| Environment Setup | 2 weeks | UVM testbench framework |
| Basic Test Development | 2 weeks | Functional test suite |
| Advanced Testing | 3 weeks | Error, stress, performance tests |
| Coverage Closure | 2 weeks | 95%+ coverage achievement |
| Final Validation | 1 week | Release-ready verification |

---

**Document Approval**:

| Role | Name | Signature | Date |
|------|------|-----------|------|
| Verification Lead | [Name] | [Signature] | [Date] |
| Design Lead | [Name] | [Signature] | [Date] |
| Project Manager | [Name] | [Signature] | [Date] |