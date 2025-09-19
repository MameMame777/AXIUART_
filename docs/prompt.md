# Prompt for Claude 4: Upgrade AXIUART UVM Verification Environment

You are a SystemVerilog/UVM and DSIM expert. Upgrade the AXIUART UVM verification environment to align with best practices and resolve the issues documented in `docs/uvm_verification_review_report.md`. Make high-quality, minimal, maintainable changes directly in this repository. Use only the real RTL under `rtl/` as the DUT.

Context
- Repository root: `e:\Nautilus\workspace\fpgawork\AXIUART_`
- UVM workspace: `sim/uvm/` (contains `dsim_config.f`, `run_uvm.ps1`, env/, agents/, sequences/, packages/, tests/, tb/)
- RTL: `rtl/` and `rtl/interfaces/`
- References: `reference/uvm_original/` and project docs in `docs/`
- Current issues: environment unused by tests, scoreboard incomplete, direct virtual interface access, inconsistent config DB/factory usage, weak coverage/assertions, per the review report.

Rules and conventions (must follow)
- SystemVerilog: Every SV file you create/touch starts with exactly: `timescale 1ns / 1ps` (with the spaces).
- Naming: Modules `Capitalized_With_Underscores`, signals `lower_snake_case`, constants `UPPER_SNAKE_CASE`.
- Indentation 4 spaces; comments in English; prioritize readability.
- Reset is synchronous active-high. If using active-low, invert locally.
- FIFO/counter widths must match spec; 64-deep FIFO has 7-bit count `[6:0]` ($clog2(64)+1).
- UVM: Use factory + `uvm_config_db` consistently. Do not directly get/set virtual interfaces in tests; set in TB top via env config. Use actual RTL as DUT.
- DSIM: No hard-coded absolute paths. Default waveform generation enabled (MXD). Check env vars (`DSIM_HOME`, `DSIM_ROOT`, `DSIM_LIB_PATH`, `DSIM_LICENSE` if required).
- Keep changes minimal and well-commented. Update documentation and add a diary entry.

Primary goals (must implement)
1) Make tests run through `uart_axi4_env` instead of directly accessing interfaces.
2) Fully implement `uart_axi4_scoreboard` with expected vs actual comparison and transaction matching.
3) Connect monitor analysis ports to the scoreboard via analysis FIFOs/exports.
4) Unify configuration via `uart_axi4_env_config` and `uvm_config_db` (no direct IF gets in tests).
5) Integrate existing sequences (`basic_func_sequence.sv`, `error_injection_sequence.sv`, etc.) via agent sequencers.
6) Ensure timescale consistency and correct file list in `sim/uvm/dsim_config.f`.
7) Enable DSIM waves (MXD) by default and verify run script checks env vars.
8) Add essential AXI4-Lite handshake assertions (TB-side bind or interface SVA).
9) Provide a comprehensive test that runs cleanly and generates coverage.

Concrete tasks and file-level instructions

A) Environment usage in tests
- Create/update `sim/uvm/tests/uart_axi4_base_test.sv`:
	- `extends uvm_test`
	- Declare `uart_axi4_env env;`
	- In `build_phase`, create `env` via factory and set/get `uart_axi4_env_config` from `uvm_config_db`. No direct virtual interface gets here.
- Create `sim/uvm/tests/uart_axi4_comprehensive_test.sv`:
	- `extends uart_axi4_base_test`
	- In `run_phase`, raise/drop objections and start `basic_func_sequence` then `error_injection_sequence` on `env.uart_agent.sequencer` (adjust path to match env structure).
	- No direct interface access in tests.

B) Env config and config DB
- Ensure `sim/uvm/env/uart_axi4_env_config.sv` exists (or create):
	- Holds flags: `uart_agent_is_active`, `axi_agent_is_active`, coverage enable, verbosity, timeouts, etc.
	- Contains virtual interface handles for UART and AXI4-Lite. These are set in TB top only.
- In TB top (`sim/uvm/tb/uart_axi4_tb.sv` or equivalent):
	- Instantiate real DUT (`rtl/AXIUART_Top.sv`), interfaces from `rtl/interfaces/`, clocks/resets.
	- Set the env config with virtual IFs into `uvm_config_db` at the env scope.
- Agents and components must retrieve configs via `uvm_config_db::get`.

C) Scoreboard
- Complete `sim/uvm/env/uart_axi4_scoreboard.sv`:
	- Provide analysis exports for expected and actual paths:
		- UART frames expected (from predictor/driver) and actual (from UART monitor)
		- AXI4-Lite transactions expected and actual (if applicable)
	- Use `uvm_tlm_analysis_fifo` or internal queues for matching.
	- Implement `check_uart_frame(exp, act)` and `check_axi_txn(exp, act)` with mismatch reporting using `uvm_error` and pass counters.
	- Provide end-of-test summary with counts via `report_phase`.

D) Monitor/Scoreboard connectivity
- In `sim/uvm/env/uart_axi4_env.sv`:
	- Instantiate scoreboard via factory.
	- Connect analysis ports from monitors to scoreboard analysis exports.
	- Provide an expected path via predictor (driver predict or dedicated predictor component) connected to scoreboard expected exports.

E) Sequences integration
- Ensure the sequences in `sim/uvm/sequences/` are used:
	- Start them on the proper sequencer(s) in `run_phase` or via a virtual sequence (`sim/uvm/sequences/uart_axi4_virtual_sequence.sv`) if coordinating UART + AXI.

F) Assertions (TB-side)
- Create `sim/uvm/tb/axi4_lite_protocol_assertions.sv`:
	- Add SVA for AXI4-Lite handshake rules: `valid & !ready` holds address/data stable; handshake completes correctly per channel.
	- Bind to the AXI4-Lite interface instance in TB.

G) DSIM configuration and run script
- Update `sim/uvm/dsim_config.f` to include all necessary RTL, interfaces, env, agents, sequences, packages, tests, and tb files using relative paths.
- Verify/update `sim/uvm/run_uvm.ps1`:
	- Validate DSIM env vars; emit clear error if missing.
	- Default `-Waves` enabled (MXD), test-named wavefile.
	- Support Mode (compile/run), Seed, Verbosity, and log naming.
	- Avoid hard-coded absolute paths; use env vars/relative paths.

H) Documentation
- Update `docs/uvm_verification_review_report.md` to reflect implemented fixes and current status.
- Update `docs/uvm_testplan.md` with the new test hierarchy, scoreboard checks, and coverage points.
- Add a dev diary `docs/diary_YYYYMMDD.md` summarizing changes, rationale, and any open items.

I) Acceptance criteria
- DSIM build compiles clean with zero errors; all SV files have consistent timescale.
- `uart_axi4_comprehensive_test` finishes with `UVM_ERROR: 0`.
- Scoreboard logs per-transaction checks; no mismatches on the basic path.
- `metrics.db` is produced and `dcreport.exe metrics.db -out_dir sim/uvm/coverage_report` runs.
- MXD waveform file named after the test is generated automatically.
- No test contains direct virtual interface gets; env config distributes IFs.
- Docs updated and diary added.

Run/verify (PowerShell)
```powershell
Set-Location e:\Nautilus\workspace\fpgawork\AXIUART_\sim\uvm
./run_uvm.ps1 -Test uart_axi4_comprehensive_test -Mode run -Seed 1 -Verbosity UVM_MEDIUM -Waves

# Coverage
Set-Location e:\Nautilus\workspace\fpgawork\AXIUART_\sim\uvm
dcreport.exe metrics.db -out_dir coverage_report
```

Notes
- Keep code minimal and readable. If a referenced file is missing, create it with a minimal correct implementation at the specified path.
- Maintain UVM naming consistency: `<module_name>_tb`, `<module_name>_driver`, `<module_name>_monitor`, `<module_name>_agent`, `<module_name>_sequence`.
- Do not change RTL functionality; all assertions/binds are TB-side.
