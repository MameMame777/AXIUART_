I'll set up a short todo plan to create a precise, actionable Claude 4 prompt and then deliver the complete prompt content. 

Created 2 todos

Let’s craft a clear, end-to-end prompt that instructs Claude 4 to implement the UART–AXI4-Lite bridge RTL and a full UVM testbench, aligned with your repo standards and the protocol spec.

## Plan
- workspace is `AXIUART_` 
- Reference repo is `UsbUartAxi` for structure and scripts(Do not edit that repo, just mimic structure)
- Provide Claude 4 with objectives, constraints, and acceptance criteria.
- Specify exact directory structure and file deliverables, mirroring `UsbUartAxi`.
- Define RTL module specs and key logic (UART, parser, AXI master, CRC).
- Define UVM environment architecture, tests, coverage, and DSIM scripts.
- Include run steps (PowerShell/DSIM), naming, timescale, and quality gates.

---

## Prompt for Claude 4

You are designing and verifying a production-quality UART–AXI4-Lite bridge. Follow these instructions exactly and deliver a complete, runnable solution in the attached workspace. Do not produce placeholders or temporary code.

Objectives
- Implement the UART–AXI4-Lite bridge RTL per `AXIUART_/docs/uart_axi4_protocol.md`.
- Provide a complete UVM environment and DSIM run scripts to compile, run, and generate MXD waveforms and coverage.
- Use the `UsbUartAxi` repository’s structure as a reference for folders and scripts; place outputs under the `UsbUartAxi` project.

Key Inputs and Constraints
- Protocol: `AXIUART_/docs/uart_axi4_protocol.md` (rev 2025-09-15). Honor frame formats, status codes, timeouts, and alignment rules exactly.
- Coding guidelines:
  - Timescale: `timescale 1ns / 1ps` at the top of all SV files.
  - Naming: Module `Capital_Underscore`, signals `lower_snake`, constants `ALL_CAPS`.
  - Synchronous, active-high reset.
  - Indentation: 4 spaces; comments in English.
  - 64-deep FIFO count width is 7 bits: `RX/TX_FIFO_WIDTH = $clog2(64) + 1`.
- UVM/DSIM:
  - Use DSIM and MXD waveforms; default waveform dumping on.
  - Provide `dsim_config.f`, `run_uvm.ps1` with environment variable checks (`DSIM_HOME`, `DSIM_LICENSE` if needed, `DSIM_LIB_PATH`, `DSIM_ROOT`), seed/verbosity control, logs, and auto waveform naming by test.
  - UVM component naming: `<module>_tb`, `<module>_agent`, `<module>_driver`, `<module>_monitor`, `<module>_sequence`.
- No hard-coded absolute paths; compose relative paths from repo root; PowerShell-compatible scripts (Windows `pwsh.exe`).
- Instantiate real RTL in testbench (no mocks). Fix real mismatches; do not suppress errors.

Deliverables: Directory Structure (mirror `UsbUartAxi`)
Create these under `UsbUartAxi/`:

- rtl
  - `Uart_Axi4_Bridge.sv` (top)
  - `Uart_Rx.sv`, `Uart_Tx.sv` (8N1, 16× oversampling)
  - `Frame_Parser.sv`, `Frame_Builder.sv`
  - `Axi4_Lite_Master.sv`
  - `Address_Aligner.sv`
  - `Crc8_Calculator.sv`
  - `fifo_sync.sv` (byte-wide 64-depth)
  - `interfaces/axi4_lite_if.sv`, `interfaces/uart_if.sv`
- sim
  - `dsim_config.f` (full file list)
  - `exec/run_uvm.ps1` (see script requirements below)
  - `uvm/`:
    - `packages/uart_axi4_test_pkg.sv` (includes env, agent, sequences, scoreboard)
    - `env/uart_axi4_env.sv`, `env/uart_axi4_env_config.sv`, `env/uart_axi4_scoreboard.sv`, `env/uart_axi4_coverage.sv`
    - `agents/uart/uart_agent.sv`, `uart_driver.sv`, `uart_monitor.sv`
    - `agents/axi4_lite/axi4_lite_agent.sv` (passive monitor for scoreboard/coverage)
    - `sequences/uart_axi_register_sequences.sv` (basic R/W, bursts, errors)
    - `sequences/basic_func_sequence.sv`, `error_injection_sequence.sv`, `performance_test_sequence.sv`
    - `tests/uart_axi4_basic_test.sv`, `tests/uart_axi4_error_paths_test.sv`, `tests/uart_axi4_burst_perf_test.sv`
    - `tb/uart_axi4_tb.sv` (connects DUT to interfaces/agents)
- scripts
  - `universal_uvm_runner.ps1` (reusable DSIM wrapper referenced by `run_uvm.ps1`)
- docs
  - `design_overview.md` (block diagram, FSMs, timing)
  - `uvm_testplan.md` (maps to Section 7 of protocol doc)
  - `run_guide.md` (how to compile/run tests, expected outputs)
- QUICK_START.md (root-level: 10-line “how to run”)

RTL Requirements
- Common
  - Put `timescale 1ns / 1ps` at top of every SV file.
  - Single clock domain (param `CLK_FREQ_HZ`), synchronous active-high `rst`.
  - Parameters:
    - `AXI_TIMEOUT = 1000`, `UART_OVERSAMPLE = 16`, `RX/TX_FIFO_DEPTH = 64`, and widths as documented.
- `Uart_Axi4_Bridge.sv` (top)
  - Ports:
    - `input logic clk, rst`
    - UART: `input logic uart_rx`, `output logic uart_tx`
    - AXI4-Lite master ports (AW, W, B, AR, R) fully typed via `axi4_lite_if.master`
  - Instantiate:
    - `Uart_Rx` and `Uart_Tx` (8N1, LSB-first, baud generator with ±2% tolerance)
    - `fifo_sync` for RX/TX byte buffers
    - `Frame_Parser` (consumes RX FIFO, validates SOF/CMD/ADDR/DATA/CRC)
    - `Axi4_Lite_Master` (per-beat transactions; LEN>1 => loop; `INC` increments address)
    - `Address_Aligner` (returns addr_ok, wstrb based on SIZE/ADDR)
    - `Frame_Builder` (builds responses with STATUS, echo CMD, echo ADDR if read-OK)
    - `Crc8_Calculator` (polynomial 0x07, init 0x00, no reflect/xorout)
- `Uart_Rx.sv` / `Uart_Tx.sv`
  - 8N1, 16× oversampling. Robust start-bit detect, sampling at bit center.
  - Expose byte-valid with error flags (framing error at stop=0).
- `Frame_Parser.sv`
  - Implements the state machine in doc Section 6.6:
    - `IDLE` → SOF `0xA5`
    - `CMD`, `ADDR` (4B LE), `DATA_RX` (for write), `CRC_RX`, `AXI_TRANS`, `RESP_TX`, `ERROR`
  - Validate fields: `SIZE`, `LEN` in [1..16], `INC`, `RW`.
  - Enforce alignment per SIZE; error map to Section 3 status codes.
  - Timeout: abort partial frame after ≥10 byte times of idle (configurable).
- `Axi4_Lite_Master.sv`
  - SIZE→`WSTRB` mapping (8/16/32) per doc, misalign => error.
  - `LEN>1` as repeated single transactions (AXI4-Lite).
  - Timeout counters for AR/AW/W/B/R with `AXI_TIMEOUT`.
  - Return `BUSY` if RVALID or WREADY stalls early (<100 cycles) then continue waiting or escalate to TIMEOUT at `AXI_TIMEOUT`.
- `Frame_Builder.sv`
  - Response for WRITE: `5A | STATUS | CMD | CRC`
  - Response for READ OK: `5A | 00 | CMD | ADDR[3:0] | DATA[...] | CRC`
  - Error response (any): `5A | STATUS | CMD | CRC`
- `Address_Aligner.sv`
  - Check `ADDR` vs `SIZE`. Generate `WSTRB`. `addr_ok` boolean.
- `Crc8_Calculator.sv`
  - Streaming per-byte enable; expose running and final CRC.
  - Match test vectors in Section 10.2 exactly.
- `interfaces/axi4_lite_if.sv` and `interfaces/uart_if.sv`
  - Provide `modport master/slave` for AXI4-Lite; `uart_if` for `rx`, `tx`, and optional events for UVM.

UVM Testbench Requirements
- Testbench top: `uart_axi4_tb.sv`
  - Instantiate DUT with real RTL; connect `uart_if` and `axi4_lite_if`.
  - Create UVM config for baud rate, CLK_FREQ_HZ, timeouts.
  - Enable DSIM waveform dumping (MXD) with file name derived from test name.
- Agents
  - `uart_agent` (active): drives byte stream over `uart_if` using 8N1 framing and idle gaps per doc; monitor collects DUT responses.
  - `axi4_lite_agent` (passive): monitors AXI channels to feed scoreboard/coverage (do not drive).
- Scoreboard
  - Mirror model for expected AXI effects; checks:
    - Correct STATUS mapping for errors: CRC_ERR, CMD_INV, ADDR_ALIGN, TIMEOUT, AXI_SLVERR, BUSY, LEN_RANGE.
    - Read response data and address echo correctness.
    - For write: verify AXI write observed matches DATA and `WSTRB`.
- Sequences and Tests
  - `uart_axi4_basic_test`: sanity for 8/16/32-bit R/W with LEN in {1,2,16}, INC={0,1}.
  - `uart_axi4_error_paths_test`: CRC flip, misalignment, force SLVERR/DECERR, AR/AW timeout hold-offs (with virtual hooks).
  - `uart_axi4_burst_perf_test`: stress/utilization at larger LEN and higher baud.
- Coverage
  - Cross: RW × INC × SIZE × LEN buckets.
  - Byte-lane selection coverage for 8/16-bit writes (WSTRB correctness).
  - Status distribution coverage.
- Reuse
  - Prefer reusing constructs from `AXIUART_/reference/uvm_original` for structure and naming consistency, but do not copy paths.

DSIM Config and Scripts
- `sim/dsim_config.f` must include (relative paths):
  - UVM package path (use DSIM’s built-in if available; do not hardcode absolute paths).
  - All `rtl/*.sv`, `rtl/interfaces/*.sv`.
  - All UVM files in `sim/uvm/**`.
  - Testbench top: `sim/uvm/tb/uart_axi4_tb.sv`
- run_uvm.ps1 (PowerShell):
  - Verify env vars: `$env:DSIM_HOME`, `$env:DSIM_ROOT`, optional `$env:DSIM_LICENSE`, `$env:DSIM_LIB_PATH`. If missing, print a clear error and exit 1.
  - Parameters:
    - `-Test <uvm_testname>`, default `uart_axi4_basic_test`
    - `-Seed <int>`, default random
    - `-Verbosity <UVM_VERBOSITY>`, default `UVM_MEDIUM`
    - `-Mode <direct|compile>`, default `direct`
  - Always enable waves (`-waves`) and output MXD named `<test>.mxd` under exec.
  - Logs: write dsim.log to project root and copy a test-specific log `sim/exec/<test>.log`.
  - Forward plusargs for `+UVM_TESTNAME`, `+UVM_VERBOSITY`, `+ntb_random_seed`.
  - Return non-zero on any `UVM_ERROR` or DSIM compile/run failure.
  - Call `scripts/universal_uvm_runner.ps1` for core logic; this script should be parameterized and reusable.

Quality Gates and Acceptance Criteria
- Build: DSIM compile with no errors.
- Lint/Typecheck: no timescale mismatches; consistent widths (e.g., FIFO count `7` bits).
- Tests:
  - `uart_axi4_basic_test`: `UVM_ERROR: 0`, generates uart_axi4_basic_test.mxd.
  - `uart_axi4_error_paths_test`: positive detection of error statuses (at least one per code).
  - `uart_axi4_burst_perf_test`: executes with sustained traffic; no deadlocks.
- Coverage:
  - Generate `metrics.db` and run `dcreport.exe metrics.db -out_dir coverage_report` (document in `run_guide.md`).
- Protocol Conformance:
  - Exact frame formats for write/read, SOF markers, CRC coverage range, CMD field encoding, LEN=1..16 only, little-endian ordering, INC handling, timeout behavior, and status code mapping per Section 2 and 3.
  - CRC8 matches Section 10.2 test vectors.
- Documentation:
  - `docs/design_overview.md`: block diagram, main FSM state transitions, timeout strategy, WSTRB mapping table.
  - `docs/uvm_testplan.md`: map Section 7 checklist to actual tests and coverage points.
  - `docs/run_guide.md`: include PowerShell commands and expected artifacts.

Minimal Example Commands (PowerShell)
Ensure your scripts make these work from repo root:
```powershell
# Basic test with waves
pwsh -File .\sim\exec\run_uvm.ps1 -Test uart_axi4_basic_test -Verbosity UVM_MEDIUM

# Error-paths test with fixed seed
pwsh -File .\sim\exec\run_uvm.ps1 -Test uart_axi4_error_paths_test -Seed 123456 -Verbosity UVM_HIGH

# Generate coverage report (after run)
dcreport.exe metrics.db -out_dir coverage_report
```

Edge Cases to Cover
- Misaligned ADDR for 16/32-bit → `ADDR_ALIGN`.
- `SIZE=2’b11` or `LEN=0` → `CMD_INV` / `LEN_RANGE`.
- CRC mismatch → `CRC_ERR`.
- AXI SLVERR/DECERR → `AXI_SLVERR`.
- Early `BUSY` followed by final `TIMEOUT` if stall persists.
- Large `LEN=16` with `INC=0` (same address repeatedly).
- Idle gap >10 byte times → abort and recover.

Notes
- Do not create mock DUTs; use the actual RTL modules.
- Do not hardcode paths; relative paths only.
- All SV files must start with `timescale 1ns / 1ps`.
- Keep code readable, commented, and minimal—no unnecessary features.

Start now. When done, provide:
- A bullet list of created files with brief descriptions.
- The DSIM run output summary (PASS/FAIL and UVM errors).
- Quick notes on any trade-offs or constraints encountered.
- Next-step suggestions if any optional enhancements are left out.

---
