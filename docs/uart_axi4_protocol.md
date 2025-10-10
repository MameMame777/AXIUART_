# UART–AXI4-Lite Bridge Protocol v0.1.1

Purpose: Define a simple, robust byte-stream protocol over UART to access an AXI4‑Lite bus (register read/write) with minimal overhead and deterministic mapping.

Revision: 2025-10-09 (v0.1.1 - Corrected CRC8 test vectors)
Previous: 2025-09-15 (v0.1 - Initial specification)

Owner: Project UART–AXI4 Bridge

---

## Revision History

| Version | Date | Changes |
|---------|------|---------|
| v0.1.1 | 2025-10-09 | **Critical CRC Specification Correction**<br>- Fixed CRC8 test vectors in Section 10.2 to match implementation algorithm<br>- Corrected CRC values in protocol examples 4.1-4.4<br>- Ensured consistency between CRC algorithm definition and test vectors |
| v0.1 | 2025-09-15 | Initial specification release |

---

## 1. UART link settings (per-byte configuration)

- Line encoding: 8N1 (8 data bits, no parity, 1 stop), LSB-first
- Default baud rate: 115200 bps
  - Supported: 115200, 230400, 460800, 921600, 1_000_000, 2_000_000, 3_000_000
  - Recommendation: Start at 115200 for bring-up; allow host to switch via a config register later
- Flow control: None (default). Optional RTS/CTS can be added later; protocol is independent.
- Idle level: High (standard UART). Minimum inter-frame idle: 1 byte time.
- Byte order in multi-byte fields: Little-endian (least significant byte first)
- Error detection: CRC-8 (polynomial 0x07, init 0x00, refin=false, refout=false, xorout=0x00)
  - Coverage: All bytes from `CMD` through the last payload/status byte (excludes SOF)
  - Frames with CRC mismatch must be discarded and reported with status `CRC_ERR` as applicable

### 1.1 Why 115200 baud as default?

**115200 bps was selected as the default for the following technical and practical reasons:**

**Historical compatibility and ecosystem support:**
- Standard baud rate supported by virtually all UART hardware and software
- Default rate for many development boards, bootloaders, and debug consoles
- Extensive tooling support (terminal programs, debuggers, test equipment)
- Well-established error characteristics and tolerance specifications

**Optimal balance of reliability vs. performance:**
- Low enough for robust operation over various cable lengths and conditions
- High enough to provide acceptable performance for register access (8.5 KB/s sustained)
- ±2% tolerance easily achieved with standard crystal oscillators (e.g., 12MHz, 25MHz)
- Minimal sensitivity to clock jitter and temperature variations

**Hardware implementation considerations:**
- Clean divisor ratios from common FPGA clock frequencies:
  - 125 MHz ÷ 1085 = 115.2 kHz (0.17% error)
  - 100 MHz ÷ 868 = 115.2 kHz (0.17% error)
  - 50 MHz ÷ 434 = 115.2 kHz (0.17% error)
- 16× oversampling easily achievable at reasonable clock frequencies (≥1.8 MHz)
- Comfortable timing margins for frame parsing and AXI transaction latency

**Bring-up and debugging advantages:**
- Slow enough for logic analyzer capture and manual analysis
- Compatible with low-cost USB-UART bridges (FT232, CP2102, etc.)
- Reduces timing-related issues during initial system integration
- Allows software debugging without high-frequency noise concerns

**Power consumption optimization:**
- Lower switching frequency reduces EMI and power consumption
- Suitable for battery-powered or low-power FPGA applications
- Minimal impact on overall system thermal design

**Scalability strategy:**
- Establishes reliable baseline operation before optimization
- Runtime baud rate switching via register interface allows performance tuning
- Progressive speed increase (115200 → 230400 → 921600+) validates system robustness
- Fallback mechanism: return to 115200 on communication errors

**Typical use case alignment:**
- Register access patterns are typically low-frequency (configuration, status monitoring)
- 115200 provides sufficient bandwidth for most control plane operations
- High-speed data transfers should use dedicated data plane interfaces (DMA, PCIe, etc.)

**Error rate and margin analysis:**
```
At 115200 baud with 16× oversampling:
- Bit period: 8.68 μs
- Sample period: 542 ns  
- Timing margin: ±271 ns (±3.1% of bit period)
- Clock jitter tolerance: <100 ns typical
- Cable length: up to 100m with appropriate drivers
```

Notes
- Parity is intentionally disabled to avoid redundancy with CRC-8.
- Receiver should support at least ±2% baud mismatch; oversampling recommended (>=16x).

---

## 2. Frame format (write and read commands)

All transfers are initiated by the host (UART master). The device (bridge) may send responses only after receiving a valid host request.

### 2.1 Common fields

- SOF: 1 byte start-of-frame marker
  - Request (host→device): `0xA5`
  - Response (device→host): `0x5A`
- CMD: 1 byte command code with bit fields
  - `[7]` RW: 0 = write, 1 = read
  - `[6]` INC: 0 = no increment, 1 = address auto-increment between beats
  - `[5:4]` SIZE: 00=8-bit, 01=16-bit, 10=32-bit, 11=reserved
  - `[3:0]` LEN: number of beats minus zero (valid range 1..16)
- ADDR: 4 bytes, little-endian, AXI4-Lite byte address (32-bit)
- DATA: present only in write request (host→device)
  - Byte count = `LEN × (1<<SIZE)`
  - Little-endian within each beat
- STATUS: 1 byte present only in response; `0x00` means OK
- CRC8: 1 byte at end of each frame, computed over `CMD..last payload/STATUS`

### 2.2 Write request (host→device)

- Order: `SOF (0xA5) | CMD | ADDR[3:0] | DATA[...] | CRC8`
- Device action: Perform `LEN` AXI4-Lite writes. For `INC=1`, increment address by beat size each beat. For `INC=0`, repeat the same address.
- Write response (device→host): `SOF (0x5A) | STATUS | CMD | CRC8`
  - Echoes `CMD` for correlation; `ADDR` is omitted to minimize bytes. Error codes explain failure reason.

### 2.3 Read request/response

- Read request (host→device): `SOF (0xA5) | CMD | ADDR[3:0] | CRC8`
  - No `DATA` in request. `LEN` and `SIZE` in `CMD` define how many bytes to read.
- Read response (device→host): `SOF (0x5A) | STATUS | CMD | ADDR[3:0] | DATA[...] | CRC8`
  - Order follows the same conceptual order as the write request (header→address→data), per project guideline.
  - `DATA` byte count = `LEN × (1<<SIZE)`, little-endian per beat.

#### 2.3.1 Read operation detailed specification

**Request frame format:**
```
Byte 0:   SOF = 0xA5 (host→device marker)
Byte 1:   CMD with RW=1 (bit[7]=1 indicates read)
Bytes 2-5: ADDR[3:0] in little-endian format
Byte 6:   CRC8 computed over bytes 1-5 (CMD through ADDR[3])
Total: 7 bytes
```

**Response frame formats:**

*Success response (STATUS = 0x00):*
```
Byte 0:     SOF = 0x5A (device→host marker)
Byte 1:     STATUS = 0x00 (success)
Byte 2:     CMD (echoed from request for correlation)
Bytes 3-6:  ADDR[3:0] (echoed in little-endian format)
Bytes 7...: DATA[0..N-1] where N = LEN × (1<<SIZE)
Last byte:  CRC8 computed over bytes 1 through last DATA byte
```

*Error response (STATUS ≠ 0x00):*
```
Byte 0: SOF = 0x5A (device→host marker)
Byte 1: STATUS (error code from Section 3)
Byte 2: CMD (echoed from request)
Byte 3: CRC8 computed over bytes 1-2 (STATUS and CMD only)
Total: 4 bytes (no ADDR or DATA in error response)
```

**READ command field encoding:**
```
CMD[7]   = 1 (read operation)
CMD[6]   = INC (0=fixed address, 1=auto-increment)
CMD[5:4] = SIZE (00=8-bit, 01=16-bit, 10=32-bit, 11=reserved)
CMD[3:0] = LEN-1 (0=1 beat, 1=2 beats, ..., 15=16 beats)
```

**Data organization in successful read response:**

For single beat (LEN=1):
- 8-bit read: 1 byte of data
- 16-bit read: 2 bytes of data (little-endian)
- 32-bit read: 4 bytes of data (little-endian)

For multiple beats (LEN>1):
- Data organized as consecutive beats
- Each beat follows little-endian format within the beat
- For INC=1: addresses increment by beat size between beats
- For INC=0: same address accessed LEN times

**Example multi-beat read (LEN=3, SIZE=16-bit, INC=1, ADDR=0x1000):**
```
AXI transactions performed:
1. Read 16-bit from 0x1000 → data_0[15:0]
2. Read 16-bit from 0x1002 → data_1[15:0]  
3. Read 16-bit from 0x1004 → data_2[15:0]

Response DATA field (6 bytes):
data_0[7:0], data_0[15:8], data_1[7:0], data_1[15:8], data_2[7:0], data_2[15:8]
```

#### 2.3.2 Read latency and timeout handling

**Normal operation flow:**
1. Host sends read request
2. Bridge validates request (CMD, ADDR alignment, CRC)
3. Bridge initiates AXI read transaction(s)
4. Bridge waits for AXI read data
5. Bridge sends successful response with data

**Timeout scenarios:**

*AXI Address Channel Timeout:*
- If ARREADY not asserted within AXI_TIMEOUT clocks
- Response: `5A 04 <CMD> <CRC>` (STATUS = TIMEOUT)

*AXI Data Channel Timeout (with early BUSY):*
- If RVALID not asserted within 100 clocks: send BUSY response
- If RVALID not asserted within AXI_TIMEOUT clocks: send TIMEOUT response
- BUSY response: `5A 06 <CMD> <CRC>` (host should retry)
- TIMEOUT response: `5A 04 <CMD> <CRC>` (transaction abandoned)

*Host-side retry strategy for BUSY:*
```c
int retry_count = 0;
while (retry_count < MAX_RETRIES) {
    result = uart_axi_read_reg32(addr, &value);
    if (result == UART_AXI_OK) return UART_AXI_OK;
    if (result == 0x06) { // BUSY
        usleep(retry_delay_ms * 1000);
        retry_count++;
        continue;
    }
    return result; // Other errors
}
return UART_AXI_ERR_TIMEOUT;
```

#### 2.3.3 Read error conditions

**Address alignment errors:**
- 16-bit read: ADDR[0] must be 0
- 32-bit read: ADDR[1:0] must be 00
- Response: `5A 03 <CMD> <CRC>` (STATUS = ADDR_ALIGN)

**AXI response errors:**
- RRESP = 2'b10 (SLVERR) or 2'b11 (DECERR)
- Response: `5A 05 <CMD> <CRC>` (STATUS = AXI_SLVERR)

**Frame validation errors:**
- CRC mismatch: `5A 01 <CMD> <CRC>` (STATUS = CRC_ERR)
- Invalid CMD fields: `5A 02 <CMD> <CRC>` (STATUS = CMD_INV)
- LEN out of range: `5A 07 <CMD> <CRC>` (STATUS = LEN_RANGE)

#### 2.3.4 Read performance characteristics

**Frame size analysis:**

| Operation | Request Size | Response Size (Success) | Response Size (Error) |
|-----------|-------------|------------------------|---------------------|
| 8-bit × 1 | 7 bytes | 9 bytes | 4 bytes |
| 16-bit × 1 | 7 bytes | 10 bytes | 4 bytes |
| 32-bit × 1 | 7 bytes | 12 bytes | 4 bytes |
| 32-bit × 16 | 7 bytes | 76 bytes | 4 bytes |

**Efficiency calculation:**
- Single 32-bit read: 4 data bytes / 12 total response bytes = 33% efficiency
- Burst 16×32-bit read: 64 data bytes / 76 total response bytes = 84% efficiency

**Latency components (at 115200 baud):**
- Request transmission: 7 bytes × 87μs/byte = 609μs
- Processing time: <1ms (typical AXI read)
- Response transmission: 12 bytes × 87μs/byte = 1044μs
- Total round-trip: ~2.7ms for single 32-bit read

### 2.4 AXI4-Lite mapping

- Each beat is a single AXI4-Lite transaction; AXI4-Lite does not support bursts, so `LEN>1` is a sequence of single transactions.
- `SIZE` to `WSTRB` mapping (little-endian):
  - SIZE=32-bit, `ADDR[1:0]==2'b00` required → `WSTRB=4'b1111`
  - SIZE=16-bit → `ADDR[1]==0/1` selects halfword → `WSTRB=4'b0011` or `4'b1100`; require `ADDR[0]==0`
  - SIZE=8-bit → `ADDR[1:0]` selects byte lane → `WSTRB=4'b0001 << ADDR[1:0]`
- Misaligned accesses:
  - For simplicity and correctness, misaligned beats are rejected with `STATUS=ADDR_ALIGN`.
  - Cross-boundary spanning within a beat is not supported.

---

## 3. Status codes

- `0x00` OK: Success
- `0x01` CRC_ERR: CRC mismatch on received frame
- `0x02` CMD_INV: Unsupported/illegal `CMD` (e.g., `SIZE=11`, `LEN=0`)
- `0x03` ADDR_ALIGN: Address/size alignment error
- `0x04` TIMEOUT: AXI or internal timeout
- `0x05` AXI_SLVERR: AXI response SLVERR/DECERR
- `0x06` BUSY: Device busy/resource contention
- `0x07` LEN_RANGE: `LEN` exceeds supported maximum
- `0x08` PARAM: Other parameter error (reserved for future)

---

## 4. Examples

Notation: numbers are hex bytes separated by spaces. `<CRC8(...)>` denotes CRC8 computed over indicated range.

### 4.1 Single 32-bit write (one beat)

- Goal: Write `0xDEADBEEF` to `ADDR=0x4000_0010`
- Fields:
  - SOF = A5
  - CMD: RW=0, INC=0, SIZE=32b (10), LEN=1 → `0b0_0_10_0001` = `0x21`
  - ADDR LE = `10 00 00 40`
  - DATA LE = `EF BE AD DE`
- Host→Device frame:
  - `A5 21 10 00 00 40 EF BE AD DE 1E`
- Device→Host response:
  - `5A 00 21 E0`

### 4.2 Two 8-bit writes with auto-increment

- Goal: Write two bytes `0x11, 0x22` to `ADDR=0x4000_0020` and `0x4000_0021`
- CMD: RW=0, INC=1, SIZE=8b (00), LEN=2 → `0b0_1_00_0010` = `0x42`
- Host→Device: `A5 42 20 00 00 40 11 22 ED`
- Response: `5A 00 42 C9`

### 4.3 Single 16-bit read

- Goal: Read one 16-bit halfword at `ADDR=0x4000_0030` (`ADDR[0]==0` required)
- CMD: RW=1, INC=0, SIZE=16b (01), LEN=1 → `0b1_0_01_0001` = `0x91`
- Host→Device: `A5 91 30 00 00 40 A9`
- Device→Host (OK, data example `0xBEEF` LE `EF BE`):
  - `5A 00 91 30 00 00 40 EF BE 16`

### 4.4 Misaligned 32-bit write (error)

- Host→Device: `A5 21 12 00 00 40 DE AD BE EF 67` (`ADDR[1:0]!=0`)
- Device→Host: `5A 03 21 D8` with `STATUS=ADDR_ALIGN`

---

## 5. Timing and performance requirements

### 5.1 Protocol timing constraints

**Frame timeout and recovery:**

- Receiver shall abort an in-progress frame if idle gap exceeds 10 byte times; partial frames are discarded.
- Minimum inter-frame gap: 1 byte time to ensure deterministic SOF detection.
- Maximum frame processing time: 100ms from SOF to response transmission start

**FIFO and buffering requirements:**

- The bridge should implement RX/TX FIFOs to decouple UART from AXI latency; recommend depths ≥64 bytes.
- The device must not send unsolicited data; responses only follow valid requests.

### 5.2 Performance specifications and targets

**Throughput requirements:**

| Baud Rate | Max Theoretical | Realistic Sustained | Frame Overhead |
|-----------|----------------|-------------------|----------------|
| 115200    | 11.5 KB/s      | 8.5 KB/s          | ~26%          |
| 230400    | 23.0 KB/s      | 17.0 KB/s         | ~26%          |
| 921600    | 92.2 KB/s      | 68.0 KB/s         | ~26%          |
| 2000000   | 200.0 KB/s     | 147.0 KB/s        | ~26%          |

*Note: Overhead includes SOF, CMD, ADDR, CRC, response frame, and inter-frame gaps*

**Latency targets:**

- Single register read/write: < 5ms end-to-end at 115200 baud
- Single register read/write: < 1ms end-to-end at 921600+ baud  
- Bulk transfer (16×32-bit): < 50ms at 115200 baud
- Frame parsing latency: < 10 clock cycles in RTL

**Resource utilization (FPGA):**

- Logic cells: < 2000 LUTs for complete bridge implementation
- Block RAM: 2-4 blocks for FIFO implementation (depending on depth)
- Clock frequency: Minimum 50MHz for proper UART oversampling
- Power consumption: < 100mW additional (target for low-power applications)

### 5.3 Scalability and optimization guidelines

**For high-throughput applications:**

- Use maximum baud rate supported by hardware (2-3 Mbaud typical)
- Prefer 32-bit transfers with LEN=16 for bulk operations
- Implement hardware flow control (RTS/CTS) if available
- Consider parallel processing of multiple AXI transactions

**For latency-critical applications:**

- Use higher baud rates even for single byte transfers
- Minimize software processing overhead with optimized CRC calculation
- Implement interrupt-driven UART handling instead of polling
- Pre-validate addresses and parameters to avoid error round-trips

**For resource-constrained systems:**

- Use smaller FIFO depths (minimum 16 bytes each direction)
- Implement table-driven CRC calculation to reduce logic
- Support subset of operations (e.g., 32-bit only) to reduce complexity
- Use single clock domain to eliminate synchronizers

---

## 6. Implementation notes (bridge RTL)

### 6.1 SystemVerilog module structure

**Top module: `Uart_Axi4_Bridge`**
- Follow project naming convention: Capital first letter, underscores for word separation
- Must include timescale `timescale 1ns / 1ps` at the beginning of all files
- Use 4-space indentation consistently

**Required sub-modules:**
- `Crc8_Calculator`: Streaming CRC8 computation (polynomial 0x07)
- `Frame_Parser`: UART byte stream to protocol frame decoder
- `Frame_Builder`: Protocol frame to UART byte stream encoder  
- `Axi4_Lite_Master`: AXI4-Lite transaction controller
- `Address_Aligner`: Address alignment validation and WSTRB generation

### 6.2 Critical timing requirements

**Clock and reset:**
- Single clock domain design recommended (use UART clock as primary)
- Synchronous reset, active-high: `input logic rst`
- Reset assertion time: minimum 10 clock cycles
- All registers must be properly reset to known states

**UART interface timing:**
- Oversampling factor: minimum 16x for robust operation
- Baud rate tolerance: support ±2% deviation
- Frame timeout: exactly 10 × (1/baud_rate × 8 bits) 
- Inter-frame gap detection: minimum 1 byte time

**AXI4-Lite transaction timeout:**
- Default: 1000 clock cycles for AWREADY/WREADY/BVALID
- Default: 1000 clock cycles for ARREADY/RVALID
- Parameterizable: `parameter AXI_TIMEOUT = 1000`

### 6.3 FIFO design specifications

**RX FIFO (UART → Protocol Parser):**
```systemverilog
// Minimum depth: 64 bytes
parameter RX_FIFO_DEPTH = 64;
parameter RX_FIFO_WIDTH = $clog2(RX_FIFO_DEPTH) + 1;  // 7 bits for 64-deep FIFO
logic [7:0] rx_fifo_data;
logic [RX_FIFO_WIDTH-1:0] rx_fifo_count;
logic rx_fifo_full, rx_fifo_empty;
```

**TX FIFO (Protocol Builder → UART):**
```systemverilog  
// Minimum depth: 64 bytes
parameter TX_FIFO_DEPTH = 64;
parameter TX_FIFO_WIDTH = $clog2(TX_FIFO_DEPTH) + 1;  // 7 bits for 64-deep FIFO
logic [7:0] tx_fifo_data;
logic [TX_FIFO_WIDTH-1:0] tx_fifo_count;
logic tx_fifo_full, tx_fifo_empty;
```

### 6.4 CRC8 implementation requirements

**Streaming CRC8 calculator:**
- Polynomial: 0x07 (x^8 + x^2 + x^1 + 1)
- Initial value: 0x00, no input/output reflection, no XOR output
- Process one byte per clock cycle
- Provide running CRC value and final CRC result
- Enable signal to control when to include byte in calculation

**Reference implementation pattern:**
```systemverilog
always_ff @(posedge clk) begin
    if (rst) begin
        crc_reg <= 8'h00;
    end else if (crc_enable) begin
        crc_reg <= crc_next;
    end
end

always_comb begin
    crc_temp = crc_reg ^ data_byte;
    crc_next = crc_reg;
    for (int i = 0; i < 8; i++) begin
        if (crc_temp[7]) begin
            crc_temp = (crc_temp << 1) ^ 8'h07;
        end else begin
            crc_temp = crc_temp << 1;
        end
        crc_next = crc_temp;
    end
end
```

### 6.5 AXI4-Lite signal assignments

**Fixed signal values:**
```systemverilog
// Write address channel
assign axi_awprot  = 3'b000;  // Non-secure, unprivileged, data access
assign axi_awcache = 4'b0000;  // Device, non-bufferable

// Read address channel  
assign axi_arprot  = 3'b000;  // Non-secure, unprivileged, data access
assign axi_arcache = 4'b0000;  // Device, non-bufferable
```

**WSTRB generation logic:**
```systemverilog
always_comb begin
    case (cmd_size)
        2'b00: begin  // 8-bit
            wstrb = 4'b0001 << addr[1:0];
            addr_align_error = 1'b0;
        end
        2'b01: begin  // 16-bit  
            wstrb = addr[0] ? 4'b1100 : 4'b0011;
            addr_align_error = addr[0];
        end
        2'b10: begin  // 32-bit
            wstrb = 4'b1111;
            addr_align_error = |addr[1:0];
        end
        default: begin
            wstrb = 4'b0000;
            addr_align_error = 1'b1;
        end
    endcase
end
```

### 6.6 State machine design

**Main protocol state machine:**
- `IDLE`: Waiting for SOF (0xA5)
- `CMD`: Receiving command byte
- `ADDR`: Receiving 4-byte address (little-endian)  
- `DATA_RX`: Receiving write data (write command only)
- `CRC_RX`: Receiving and validating CRC8
- `AXI_TRANS`: Executing AXI transaction(s)
- `RESP_TX`: Sending response frame
- `ERROR`: Error state, discard frame and send error response

### 6.7 Parameterization requirements

```systemverilog
module Uart_Axi4_Bridge #(
    parameter MAX_LEN          = 16,        // Maximum LEN field value
    parameter AXI_ADDR_WIDTH   = 32,        // AXI address width
    parameter AXI_DATA_WIDTH   = 32,        // AXI data width (fixed at 32)
    parameter RX_FIFO_DEPTH    = 64,        // RX FIFO depth
    parameter TX_FIFO_DEPTH    = 64,        // TX FIFO depth  
    parameter AXI_TIMEOUT      = 1000,      // AXI timeout in clock cycles
    parameter UART_OVERSAMPLE  = 16         // UART oversampling factor
) (
    // Clock and reset
    input  logic                        clk,
    input  logic                        rst,
    
    // UART interface
    input  logic                        uart_rxd,
    output logic                        uart_txd,
    
    // AXI4-Lite master interface
    // ... AXI signals ...
);
```

---

## 7. UVM verification mapping (checklist)

Planned tests/sequences (tie to `reference/uvm_original` assets):

- Basic R/W, sizes: 8/16/32-bit, `LEN` in {1, 2, 16}
- Alignment checks: valid vs. misaligned → expect `ADDR_ALIGN`
- CRC error injection: single-bit error → expect `CRC_ERR`
- Auto-increment vs. fixed address behavior
- AXI error propagation: force SLVERR/DECERR → expect `AXI_SLVERR`
- Timeout path: hold `AWREADY/ARREADY` low → expect `TIMEOUT`
- Back-to-back frames with minimal gap; long gap abort behavior

Coverage points

- CMD field cross coverage: RW × INC × SIZE × `LEN` buckets
- Address lane selection for 8/16-bit writes (WSTRB mapping)
- Response status distribution

Artifacts

- Reuse `uart_*` agent to drive/monitor byte stream at interface boundary
- Scoreboard to mirror AXI register model and compare responses
- Waveform dumping enabled (MXD) per DSIM guidance; test names reflect case

---

## 8. Host API convenience (optional)

- A thin host library can assemble frames and compute CRC8 using polynomial 0x07; recommend table-driven or bitwise reference implementation.

---

## 9. Open points / future options

- Optional 2-byte SOF (`0x55 0xAA`) and/or byte stuffing if noise susceptibility is a concern
- Optional parity as a link-layer redundancy
- Extended address width (e.g., 64-bit) if needed by system
- IRQ/event notifications (unsolicited) if product scope expands

---

## 10. CRC8 reference implementation and test vectors

### 10.1 Bitwise implementation

Pseudo-code for CRC8 (polynomial 0x07):

```c
crc = 0x00
for byte in bytes:
  crc ^= byte
  for i in 0..7:
    if (crc & 0x80): crc = ((crc << 1) ^ 0x07) & 0xFF
    else:            crc = (crc << 1) & 0xFF
return crc
```

### 10.2 Test vectors for validation

**Critical test cases for both HW and SW implementation:**

| Input Data (hex) | Expected CRC8 | Description |
|------------------|---------------|-------------|
| `21 10 00 00 40 EF BE AD DE` | `0x1E` | Example 4.1: 32-bit write frame |
| `42 20 00 00 40 11 22` | `0xED` | Example 4.2: 8-bit auto-inc frame |
| `91 30 00 00 40` | `0xA9` | Example 4.3: 16-bit read request |
| `00 91 30 00 00 40 EF BE` | `0x16` | Example 4.3: 16-bit read response |
| `21` | `0xE7` | Single byte (CMD only) |
| `00 00 00 00` | `0x00` | All zeros |
| `FF FF FF FF` | `0xDE` | All ones |
| `01 02 03 04 05` | `0xBC` | Sequential bytes |

**Usage in implementation validation:**

```c
// Validation function for both teams
bool validate_crc8_implementation(void) {
    const struct {
        const uint8_t *data;
        size_t length;
        uint8_t expected;
        const char* description;
    } test_vectors[] = {
        {{0x21,0x10,0x00,0x00,0x40,0xEF,0xBE,0xAD,0xDE}, 9, 0x8E, "32-bit write"},
        {{0x42,0x20,0x00,0x00,0x40,0x11,0x22}, 7, 0x23, "8-bit auto-inc"},
        {{0x91,0x30,0x00,0x00,0x40}, 5, 0x77, "16-bit read request"},
        // Add all test vectors...
    };
    
    for (int i = 0; i < sizeof(test_vectors)/sizeof(test_vectors[0]); i++) {
        uint8_t calculated = crc8_calculate(test_vectors[i].data, test_vectors[i].length);
        if (calculated != test_vectors[i].expected) {
            printf("CRC8 validation failed for %s: expected 0x%02X, got 0x%02X\n", 
                   test_vectors[i].description, test_vectors[i].expected, calculated);
            return false;
        }
    }
    return true;
}
```

---

## 11. Software driver implementation guide

### 11.1 Driver architecture overview

**Language recommendations:**

- C/C++ for embedded systems (bare metal or RTOS)
- Python for rapid prototyping and test tools
- Consider thread-safe implementation for multi-threaded environments

**Core driver components:**

- `uart_axi_driver.c/h`: Main driver interface
- `uart_axi_crc8.c/h`: CRC8 calculation utilities
- `uart_axi_frame.c/h`: Frame construction and parsing
- `uart_axi_transport.c/h`: UART transport layer

### 11.2 Critical implementation requirements

**Frame timeout handling:**

```c
#define FRAME_TIMEOUT_MS    100    // Maximum time to wait for complete frame
#define BYTE_TIMEOUT_MS     10     // Maximum time between bytes in a frame
#define MAX_RETRIES         3      // Maximum retry attempts on error
```

**CRC8 implementation:**

```c
uint8_t crc8_calculate(const uint8_t *data, size_t length) {
    uint8_t crc = 0x00;
    for (size_t i = 0; i < length; i++) {
        crc ^= data[i];
        for (int bit = 0; bit < 8; bit++) {
            if (crc & 0x80) {
                crc = ((crc << 1) ^ 0x07) & 0xFF;
            } else {
                crc = (crc << 1) & 0xFF;
            }
        }
    }
    return crc;
}
```

**Required API functions:**

```c
// Initialize driver with UART configuration
int uart_axi_init(const char* uart_device, uint32_t baudrate);

// Single register operations
int uart_axi_write_reg32(uint32_t addr, uint32_t value);
int uart_axi_read_reg32(uint32_t addr, uint32_t *value);
int uart_axi_write_reg16(uint32_t addr, uint16_t value);
int uart_axi_read_reg16(uint32_t addr, uint16_t *value);
int uart_axi_write_reg8(uint32_t addr, uint8_t value);
int uart_axi_read_reg8(uint32_t addr, uint8_t *value);

// Burst operations with auto-increment
int uart_axi_write_burst32(uint32_t start_addr, const uint32_t *data, uint8_t len);
int uart_axi_read_burst32(uint32_t start_addr, uint32_t *data, uint8_t len);

// Low-level frame operations
int uart_axi_send_frame(const uint8_t *frame, size_t frame_len);
int uart_axi_receive_frame(uint8_t *frame, size_t max_len, size_t *actual_len);

// Error handling and diagnostics
const char* uart_axi_get_error_string(int error_code);
void uart_axi_reset_state(void);
```

### 11.3 Error handling strategy

**Error code definitions:**

```c
#define UART_AXI_OK              0x00    // Success
#define UART_AXI_ERR_CRC         0x01    // CRC mismatch
#define UART_AXI_ERR_CMD_INV     0x02    // Invalid command
#define UART_AXI_ERR_ADDR_ALIGN  0x03    // Address alignment error
#define UART_AXI_ERR_TIMEOUT     0x04    // Operation timeout
#define UART_AXI_ERR_AXI_SLVERR  0x05    // AXI slave error
#define UART_AXI_ERR_BUSY        0x06    // Device busy
#define UART_AXI_ERR_LEN_RANGE   0x07    // Length out of range
#define UART_AXI_ERR_PARAM       0x08    // Parameter error

// Driver-specific errors (0x80+)
#define UART_AXI_ERR_UART_INIT   0x80    // UART initialization failed
#define UART_AXI_ERR_UART_WRITE  0x81    // UART write failed
#define UART_AXI_ERR_UART_READ   0x82    // UART read failed
#define UART_AXI_ERR_FRAME_TIMEOUT 0x83  // Frame timeout
#define UART_AXI_ERR_INVALID_RESP  0x84  // Invalid response format
```

**Retry and recovery logic:**

- Implement exponential backoff for timeout errors
- Reset UART state on frame corruption
- Provide diagnostic counters for error tracking

### 11.4 Frame construction examples

**Write frame construction:**

```c
int build_write_frame(uint32_t addr, const uint8_t *data, 
                     uint8_t size, uint8_t len, bool auto_inc,
                     uint8_t *frame, size_t *frame_len) {
    uint8_t cmd = 0;
    cmd |= (0 << 7);          // RW = 0 (write)
    cmd |= (auto_inc << 6);   // INC bit
    cmd |= (size << 4);       // SIZE field
    cmd |= (len - 1);         // LEN field (0-based)
    
    size_t pos = 0;
    frame[pos++] = 0xA5;                    // SOF
    frame[pos++] = cmd;                     // CMD
    
    // Address (little-endian)
    frame[pos++] = (addr >>  0) & 0xFF;
    frame[pos++] = (addr >>  8) & 0xFF;
    frame[pos++] = (addr >> 16) & 0xFF;
    frame[pos++] = (addr >> 24) & 0xFF;
    
    // Data payload
    size_t data_bytes = len * (1 << size);
    memcpy(&frame[pos], data, data_bytes);
    pos += data_bytes;
    
    // CRC8 (from CMD through end of data)
    uint8_t crc = crc8_calculate(&frame[1], pos - 1);
    frame[pos++] = crc;
    
    *frame_len = pos;
    return UART_AXI_OK;
}
```

### 11.5 Thread safety considerations

**For multi-threaded environments:**

- Implement mutex protection around UART operations
- Consider separate read/write locks if performance is critical
- Provide async API with callback mechanisms for high-performance applications

**Resource management:**

```c
typedef struct {
    pthread_mutex_t uart_mutex;
    int uart_fd;
    bool initialized;
    uint32_t error_count;
    uint32_t transaction_count;
} uart_axi_context_t;
```

### 11.6 Performance optimization guidelines

**Minimize latency:**

- Pre-compute CRC lookup tables for faster calculation
- Use buffered I/O to reduce system call overhead
- Implement frame pipelining for burst operations

**Throughput optimization:**

- Use maximum supported LEN (16) for bulk transfers
- Choose optimal SIZE (32-bit preferred) when possible
- Consider hardware flow control at high baud rates

**Memory efficiency:**

- Static allocation for embedded systems
- Bounded buffer sizes to prevent memory exhaustion
- Reuse frame buffers across transactions

---

## 12. Hardware/Software integration and debugging

### 12.1 Development workflow and collaboration

**Phase 1: Standalone development**

- **RTL team**: Implement and verify with UVM testbench using mock UART transactions
- **SW team**: Develop and test driver with UART loopback or virtual UART pairs
- **Integration point**: Both teams use identical frame examples from Section 4

**Phase 2: Hardware-in-the-loop integration**

- **RTL team**: Provide synthesis reports and timing analysis
- **SW team**: Test driver against real hardware with known-good register map
- **Joint debugging**: Use logic analyzer/scope to correlate UART traffic with AXI transactions

### 12.2 Debug interfaces and observability

**RTL debug features (recommended):**

```systemverilog
// Debug register map (AXI4-Lite accessible)
localparam DEBUG_BASE_ADDR    = 32'hFFFF_F000;
localparam REG_STATUS         = DEBUG_BASE_ADDR + 32'h00;  // Bridge status
localparam REG_ERROR_COUNT    = DEBUG_BASE_ADDR + 32'h04;  // Error counters
localparam REG_FRAME_COUNT    = DEBUG_BASE_ADDR + 32'h08;  // Frame counters
localparam REG_LAST_CMD       = DEBUG_BASE_ADDR + 32'h0C;  // Last received CMD
localparam REG_LAST_ADDR      = DEBUG_BASE_ADDR + 32'h10;  // Last accessed address
localparam REG_LAST_CRC       = DEBUG_BASE_ADDR + 32'h14;  // Last computed CRC
```

**Status register bit fields:**

```systemverilog
// REG_STATUS bit definitions
localparam STATUS_IDLE        = 0;   // Bridge in idle state
localparam STATUS_ACTIVE      = 1;   // Transaction in progress  
localparam STATUS_ERROR       = 2;   // Error condition present
localparam STATUS_RX_FIFO_FULL = 8;  // RX FIFO full flag
localparam STATUS_TX_FIFO_FULL = 9;  // TX FIFO full flag
localparam STATUS_AXI_TIMEOUT  = 16; // AXI transaction timeout
```

**Software debug utilities:**

```c
// Debug and diagnostic functions
typedef struct {
    uint32_t total_frames;
    uint32_t error_frames;
    uint32_t crc_errors;
    uint32_t timeout_errors;
    uint32_t alignment_errors;
} uart_axi_stats_t;

int uart_axi_get_statistics(uart_axi_stats_t *stats);
int uart_axi_reset_statistics(void);
int uart_axi_dump_frame(const uint8_t *frame, size_t len, FILE *output);
int uart_axi_self_test(void);  // Built-in self-test using known addresses
```

### 12.3 Common integration issues and solutions

**Issue 1: Frame synchronization loss**

- **Symptom**: Spurious CRC errors, unexpected responses
- **Root cause**: UART baud rate mismatch or noise
- **Solution**: Implement frame resynchronization by searching for valid SOF patterns
- **Prevention**: Use automatic baud rate detection or crystal oscillators

**Issue 2: AXI transaction hang**

- **Symptom**: Timeout errors, bridge becomes unresponsive
- **Root cause**: AXI slave not responding, clock domain issues
- **Solution**: Implement proper timeout handling and watchdog reset
- **Debug**: Monitor AXI bus signals with logic analyzer

**Issue 3: Data corruption**

- **Symptom**: Read data doesn't match written data
- **Root cause**: Endianness issues, alignment problems
- **Solution**: Verify little-endian byte ordering in both HW and SW
- **Test**: Use walking bit patterns and known test vectors

### 12.4 Verification coordination

**Shared test vectors:** Create common test cases that both teams can use:

```c
// Test vector format (shared between HW testbench and SW tests)
typedef struct {
    const char* name;
    uint32_t    address;
    uint8_t     data[64];
    uint8_t     size;       // 0=8bit, 1=16bit, 2=32bit
    uint8_t     length;     // Number of beats (1-16)
    bool        auto_inc;   // Address increment flag
    bool        expect_error;
    uint8_t     expected_status;
} test_vector_t;

// Example test vectors
static const test_vector_t test_vectors[] = {
    {"single_32bit_write", 0x40000010, {0xEF,0xBE,0xAD,0xDE}, 2, 1, false, false, 0x00},
    {"burst_8bit_write",   0x40000020, {0x11,0x22,0x33,0x44}, 0, 4, true,  false, 0x00},
    {"misaligned_32bit",   0x40000012, {0xAA,0xBB,0xCC,0xDD}, 2, 1, false, true,  0x03},
    // Add more test vectors as needed
};
```

**Cross-validation methodology:**

1. **RTL team**: Run UVM testbench with shared test vectors
2. **SW team**: Run driver tests with identical test vectors  
3. **Integration**: Compare results and resolve discrepancies
4. **Documentation**: Update test vectors based on real hardware behavior

### 12.5 Performance benchmarking

**Measurement points for both teams:**

- **Throughput**: Bytes per second for bulk transfers
- **Latency**: Round-trip time for single register access
- **Efficiency**: Protocol overhead vs. payload ratio
- **Error rate**: Errors per transaction under various conditions

**Benchmarking framework:**

```c
typedef struct {
    double throughput_bps;      // Bytes per second
    double latency_us;          // Microseconds per transaction
    double efficiency_percent;  // Payload / total frame size
    double error_rate;          // Errors per transaction
} performance_metrics_t;

int uart_axi_benchmark(uint32_t test_addr, size_t test_size, 
                      uint32_t iterations, performance_metrics_t *metrics);
```
