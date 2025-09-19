# AXIUART Register Map

This document defines the register map for the AXI4-Lite slave register block in the AXIUART system.
All register addresses are byte-addressed and 32-bit aligned.

## Conventions

- Address unit: bytes (32-bit aligned)
- All fields documented with access type: RW / RO / W1C / W1S / RC (read clears)
- Reset values are synchronous, active-high reset
- Reserved bits must read as 0 and be written as 0 unless otherwise noted
- Base address: 0x0000_1000
- Address space: 4KB (0x0000_1000 to 0x0000_1FFF)

## Summary Table

| Offset | Name         | Width | Access | Reset      | Description                        |
|--------|--------------|-------|--------|------------|------------------------------------|
| 0x000  | CONTROL      | 32    | RW     | 0x0000_0000| Global control and command register|
| 0x004  | STATUS       | 32    | RO     | 0x0000_0000| Global status and error flags      |
| 0x008  | CONFIG       | 32    | RW     | 0x0000_0000| UART and AXI configuration        |
| 0x00C  | DEBUG        | 32    | RW     | 0x0000_0000| Debug mode and control            |
| 0x010  | TX_COUNT     | 32    | RO     | 0x0000_0000| TX transaction counter            |
| 0x014  | RX_COUNT     | 32    | RO     | 0x0000_0000| RX transaction counter            |
| 0x018  | FIFO_STAT    | 32    | RO     | 0x0000_0000| FIFO status and flags             |
| 0x01C  | VERSION      | 32    | RO     | 0x0001_0000| Hardware version information      |

## Register Detailed Descriptions

## CONTROL (0x000, RW, reset=0x0000_0000)

Global control register for AXIUART system operation.

| Bit(s) | Field        | Access | Reset | Description                             |
|--------|--------------|--------|-------|-----------------------------------------|
| 0      | bridge_enable| RW     | 0     | Enable UART bridge operation (0=disable, 1=enable) |
| 1      | reset_stats  | W1C    | 0     | Write 1 to reset statistics counters (self-clearing) |
| 31:2   | reserved     | -      | 0     | Must be 0                               |

**Side Effects:**
- Writing 1 to bit 1 (reset_stats) generates a pulse to reset TX_COUNT and RX_COUNT
- Bit 1 always reads as 0
- Clearing bit 0 disables the entire UART bridge and resets internal state

## STATUS (0x004, RO, reset=0x0000_0000)

System status and error reporting register.

| Bit(s) | Field        | Access | Reset | Description                             |
|--------|--------------|--------|-------|-----------------------------------------|
| 0      | bridge_busy  | RO     | 0     | 1 when UART bridge is processing a transaction |
| 8:1    | error_code   | RO     | 0     | Current error status (see error codes below) |
| 31:9   | reserved     | -      | 0     | Must be 0                               |

**Error Codes:**
- 0x00: No error
- 0x01-0x0F: UART protocol errors
- 0x10-0x1F: AXI4-Lite protocol errors  
- 0x20-0x2F: Frame parsing errors
- 0x30-0xFF: Reserved for future use

## CONFIG (0x008, RW, reset=0x0000_0000)

Configuration register for UART and AXI parameters.

| Bit(s) | Field        | Access | Reset | Description                             |
|--------|--------------|--------|-------|-----------------------------------------|
| 7:0    | baud_div     | RW     | 0     | UART baud rate divider configuration    |
| 15:8   | timeout_cfg  | RW     | 0     | AXI transaction timeout configuration   |
| 31:16  | reserved     | -      | 0     | Must be 0                               |

**Field Details:**
- baud_div: Divider value for UART baud rate generation (implementation defined)
- timeout_cfg: Timeout value in system clock cycles (×64 multiplier)

## DEBUG (0x00C, RW, reset=0x0000_0000)

Debug control and monitoring register.

| Bit(s) | Field        | Access | Reset | Description                             |
|--------|--------------|--------|-------|-----------------------------------------|
| 3:0    | debug_mode   | RW     | 0     | Debug mode selection (see modes below) |
| 31:4   | reserved     | -      | 0     | Must be 0                               |

**Debug Modes:**
- 0x0: Normal operation
- 0x1: UART loopback mode
- 0x2: AXI transaction logging
- 0x3: Frame parser debug
- 0x4-0xF: Reserved for future debug features

## TX_COUNT (0x010, RO, reset=0x0000_0000)

Transmit transaction counter (read-only).

| Bit(s) | Field        | Access | Reset | Description                             |
|--------|--------------|--------|-------|-----------------------------------------|
| 15:0   | tx_counter   | RO     | 0     | Number of completed TX transactions     |
| 31:16  | reserved     | -      | 0     | Must be 0                               |

**Behavior:**
- Increments on each successful UART transmission
- Can be reset by writing 1 to CONTROL[1] (reset_stats)
- Wraps around at 65535

## RX_COUNT (0x014, RO, reset=0x0000_0000)

Receive transaction counter (read-only).

| Bit(s) | Field        | Access | Reset | Description                             |
|--------|--------------|--------|-------|-----------------------------------------|
| 15:0   | rx_counter   | RO     | 0     | Number of completed RX transactions     |
| 31:16  | reserved     | -      | 0     | Must be 0                               |

**Behavior:**
- Increments on each successful UART reception
- Can be reset by writing 1 to CONTROL[1] (reset_stats)
- Wraps around at 65535

## FIFO_STAT (0x018, RO, reset=0x0000_0000)

FIFO status and monitoring register.

| Bit(s) | Field        | Access | Reset | Description                             |
|--------|--------------|--------|-------|-----------------------------------------|
| 0      | rx_fifo_full | RO     | 0     | RX FIFO full flag                       |
| 1      | rx_fifo_empty| RO     | 0     | RX FIFO empty flag                      |
| 2      | tx_fifo_full | RO     | 0     | TX FIFO full flag                       |
| 3      | tx_fifo_empty| RO     | 0     | TX FIFO empty flag                      |
| 7:4    | rx_fifo_level| RO     | 0     | RX FIFO fill level (0-15)              |
| 31:8   | reserved     | -      | 0     | Must be 0                               |

## VERSION (0x01C, RO, reset=0x0001_0000)

Hardware version identification register.

| Bit(s) | Field        | Access | Reset | Description                             |
|--------|--------------|--------|-------|-----------------------------------------|
| 7:0    | patch_ver    | RO     | 0     | Patch version number                    |
| 15:8   | minor_ver    | RO     | 0     | Minor version number                    |
| 23:16  | major_ver    | RO     | 1     | Major version number                    |
| 31:24  | reserved     | -      | 0     | Reserved                                |

**Current Version: 1.0.0**

## Address Decoding Notes

- All register addresses must be 32-bit aligned (addr[1:0] = 2'b00)
- Unmapped addresses (0x020-0xFFF) return SLVERR on AXI4-Lite read/write
- Unaligned addresses return SLVERR response
- Writes to RO fields are ignored and return OKAY response
- Reads of W1C fields return the post-clear value (always 0)
- Reserved fields must be written as 0 and will always read as 0

## Register Access Examples

```systemverilog
// Enable UART bridge
axi_write(32'h0000_1000, 32'h0000_0001);

// Configure baud rate and timeout
axi_write(32'h0000_1008, 32'h0000_5A87); // timeout=0x5A, baud_div=0x87

// Reset statistics counters
axi_write(32'h0000_1000, 32'h0000_0003); // enable + reset_stats

// Read system status
bit [31:0] status;
axi_read(32'h0000_1004, status);
if (status[0]) $display("Bridge is busy");

// Read version
bit [31:0] version;
axi_read(32'h0000_101C, version);
$display("Version: %0d.%0d.%0d", version[23:16], version[15:8], version[7:0]);
```

## Change Log

- YYYY-MM-DD: Initial template created
