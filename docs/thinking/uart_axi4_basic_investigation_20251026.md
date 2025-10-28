# UART AXI4 Basic Test Investigation — 2025-10-26

## Scope

Summarize the debug work performed on 2025-10-26 for `uart_axi4_basic_test` and capture current open questions. The primary objective was to determine why the UVM regression stalls mid-frame.

## Actions Completed

- Instrumented `sim/uvm/agents/uart/uart_driver.sv` with:
  - Forced begin/end markers for every transmitted byte.
  - A byte-level watchdog that raises `UART_DRIVER_BYTE_TIMEOUT` if a byte does not finish within `cfg.byte_time_ns` margin.
- Added payload-size guard in `sim/uvm/sequences/debug_single_write_sequence.sv` (retained from earlier session).
- Rebuilt and re-ran DSIM compile-only check via MCP (success).
- Executed full DSIM run with MCP (`--timeout 420`, verbose plusargs). Latest log: `sim/exec/logs/uart_axi4_basic_test_20251026_185841.log`.

## Key Observations

- Driver logging reaches `Begin byte[2/7]=0x00` at `26612000ns` but there is no corresponding `End byte[2/7]`. The MCP wrapper terminates the run on timeout at 420s.
- DUT side (`BRIDGE_RX`) captures bytes #1–#3 only. `Frame_Parser` transitions through `ADDR_BYTE1` and `bridge_busy` reasserts at `13068000ns`, never returning low afterward.
- No `rx_valid` for byte #4 (`ADDR_BYTE2`) appears; the monitor trace halts with frame contents `0xa5 0x00 0x00`.
- Wave dumping remains disabled because the base test scenario defaults to `default`, ignoring `+WAVES_ON`. The MXD/VCD outputs requested by `+WAVE_SCENARIO=byte_watchdog` were not generated.
- The new byte-level watchdog did **not** fire, meaning the byte-send task is still alive when the overall simulation times out.

## Current Status (Unresolved)

- Root cause remains unknown. The stimulus path appears to stall while transmitting byte[2], and the DUT simultaneously parks in parser state `ADDR_BYTE1`. Further evidence (waveforms, additional assertions) is required to determine whether the blockage originates in the driver timing loop, UART interface handshake, or DUT FIFO back-pressure.

## Next Steps

1. Enable waveform capture by selecting a `wave_debug` scenario (or equivalent) so MXD dumps become available for inspection.
2. With waves active, probe the UART RX line, CTS/RTS flow control, and internal bridge FIFO states during the stall window (~26–40 us).
3. Consider additional DUT-side assertions (e.g., expected `rx_valid` count) to flag incomplete frames proactively.

*Note: Investigation is still in progress; no definitive fix identified as of this entry.*
