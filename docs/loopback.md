# UVM-Only Loopback Verification Plan


## Objectives

- Isolate the UART driver/monitor pair from RTL to confirm frame timing, SOF decode, and CRC handling without DUT side-effects.
- Provide a regression-friendly stimulus path that reproduces monitor decode issues deterministically.
- Preserve existing full-system flows so loopback mode can be toggled per test without impacting DUT regressions.


## Constraints

- Maintain current UART interface definitions; no protocol shortcuts or DPI-based hacks.
- Keep assertions and scoreboard optional so loopback runs do not report false DUT errors.
- Avoid modifying RTL behaviour when loopback mode is disabled; production paths must remain untouched.


## Proposed Architecture

- Extend `uart_axi4_env_config` with `enable_uvm_loopback_mode` and granular knobs to disable scoreboard/coverage when requested.
- Add a lightweight `uart_uvm_loopback_model` component that subscribes to `uart_driver.tx_request_ap`, builds device-to-host frames with SOF `0x5A`, and drives them on `vif.uart_tx` using the same timing model as the DUT TX.
- Gate DUT instantiation in `uart_axi4_tb_top` behind a generate-if: instantiate AXIUART_Top when loopback is off, otherwise instantiate the loopback model and drive idle defaults onto unused DUT signals.
- Reuse the existing monitor TX analysis FIFO path so loopback responses flow through the monitor and back to the driver for closure.
- Provide a `uvm_config_db` hook (plusarg `+UVM_LOOPBACK=1`) so tests can enable the loopback without editing the bench.


## Implementation Steps

- Update `uart_axi4_env_config.sv` with new loopback fields and helper methods that compute UART timing once for both driver and loopback model.
- Modify `uart_axi4_tb_top.sv` to evaluate the new config knob: keep DUT wiring for the default path; when loopback is enabled, instantiate `uart_uvm_loopback_model`, connect it to the shared `uart_if`, and suppress DUT-specific monitors.
- Create `sim/uvm/components/uart_uvm_loopback_model.sv` implementing a reactive driver that consumes request transactions, schedules TX waveforms, and can optionally echo status codes for negative testing.
- Extend `uart_axi4_env.sv` to build and connect the loopback model when `enable_uvm_loopback_mode` is set, including disabling scoreboard/coverage unless explicitly requested.
- Add `uart_axi4_uvm_loopback_test.sv` that inherits from `enhanced_uart_axi4_base_test`, enables loopback via config_db, and runs a deterministic sequence (e.g. `debug_single_write_sequence`) plus randomized stress.
- Inject documentation into `docs/diary_<date>.md` after implementation describing the activation flow and observed results.


## Validation Plan

- Compile-only check: `python mcp_server/mcp_client.py --workspace E:\Nautilus\workspace\fpgawork\AXIUART_ --tool run_uvm_simulation --test-name uart_axi4_uvm_loopback_test --mode compile --verbosity UVM_LOW --timeout 120`.
- Loopback simulation: `python mcp_server/mcp_client.py --workspace E:\Nautilus\workspace\fpgawork\AXIUART_ --tool run_uvm_simulation --test-name uart_axi4_uvm_loopback_test --mode run --verbosity UVM_DEBUG --waves --timeout 180`.
- Confirm monitor publishes both RX and synthesized TX frames without `PARSE_ERROR_SOF_MISMATCH`; capture waveform snapshots under `archive/waveforms/` for baseline.


## Risks and Follow-Up

- Timing drift between driver bit periods and loopback transmitter could reintroduce sampling errors; cross-check `cfg.bit_time_ns` usage in both paths.
- Sequence expects DUT register side-effects; disable or stub AXI scoreboarding when loopback is active.
- Future expansion: allow error injection hooks in the loopback model to exercise monitor recovery logic once the clean path passes.
