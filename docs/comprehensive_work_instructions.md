# AXIUART SystemVerilog UVM Verification – Comprehensive Work Instructions

 _Last updated: 2025-10-02_  
_Target environment: DSIM v20240422.0.0 · SystemVerilog UVM 1.2 · Windows PowerShell_

---

## 1. Purpose and scope

- Guarantee a repeatable, high-quality verification workflow for the `AXIUART_Top` UART ⇔ AXI4-Lite bridge.
- Maintain `UVM_ERROR = 0` across all regressions while steadily improving toggle, expression, and functional coverage.
- Ensure every engineer can continue the effort without guesswork by providing precise, English-language guidance tied to the repository structure under `docs/`.

## 2. Working principles

SystemVerilog verification engineers on this project commit to the following:

1. **Quality first** – never ship partial fixes or temporary code. Use the RTL in `rtl/` exactly as the DUT.
2. **Evidence-based decisions** – track metrics (coverage, run time, waveform review) before declaring success.
3. **Consistency** – enforce `timescale 1ns / 1ps`, synchronous active-high reset, English comments, and four-space indentation in every SystemVerilog file.
4. **Security and confidentiality** – keep project data local, avoid hard-coded secrets, and prefer relative paths.
5. **Knowledge sharing** – document insights in `docs/diary_YYYYMMDD.md` and update this guide whenever processes change.

## 3. Project snapshot (02 Oct 2025)

### 3.0 Goal and status summary

- **Project goal**: Deliver a production-ready UART ⇔ AXI4-Lite bridge with UVM-driven verification that maintains `UVM_ERROR = 0`, achieves ≥ 60 % toggle coverage in Phase 4, and progresses toward the Phase 5 stretch targets without sacrificing stability.
- **Current status (2025-10-02)**:
  - `register_comprehensive_test` (executed 2025-10-02 05:35 via `run_uvm.ps1`) finishes with 33 `UVM_ERROR` reports and 16 scoreboard mismatches on reserved register accesses; the reserved-address auto-classification and metadata propagation path must be validated before resuming the coverage push.
  - `coverage_work_plan_20251001.md` captures the latest metrics (Line 100 %, Expression 66.7 %, frame functional 32.05 %, burst functional 47.92 %, error functional 50.00 %) and exposes the blind spots that block the Phase 4 objectives.
  - Tooling (`run_uvm.ps1`, MXD capture, coverage export) remains stable, but every engineer must treat the scoreboard mismatch as a priority defect while layering the new coverage sequences.

### 3.1 System overview

- UART runs at 115 200 bps and bridges to a 32-bit AXI4-Lite interface.
- The design includes a 64-entry synchronous FIFO, CRC8 protection, and custom framing.
- Verification uses SystemVerilog UVM 1.2 with DSIM and MXD waveform dumps.

### 3.2 Verification status

- **Stability**: The latest full regression (`register_comprehensive_test`, 2025-10-02) fails with scoreboard mismatches; treat regression repair as a release blocker.
- **Infrastructure**: `run_uvm.ps1` continues to standardise compilation, execution, waveform (MXD), and coverage export; environment variable checks remain mandatory.
- **Coverage summary (per `coverage_work_plan_20251001.md`)**:

| Metric | Latest value | Short-term goal | Notes |
| ------ | ------------ | ---------------- | ----- |
| Line | 100.0 % | 100 % | Keep regression green while fixing scoreboard defect. |
| Expression (`AXIUART_Top`) | 66.7 % | ≥ 87 % | Missing the `system_busy && (bridge_error_code != 8'h00)` branch. |
| Functional (`frame_coverage`) | 32.05 % | ≥ 40 % | `align_status` bins never sampled; partial WSTRB absent. |
| Functional (`burst_coverage`) | 47.92 % | ≥ 55 % | `burst_len_type_size` cross stuck at 8.33 %. |
| Functional (`error_coverage`) | 50.00 % | ≥ 60 % | Need CRC-bad, timeout, and AXI SLVERR in one regression window. |

> Focus: unblock reserved-address handling, then drive misaligned, partial-strobe, and error-response stimulus to close the identified coverage gaps.

### 3.3 Key achievements to date

- Reserved-address auto-classification and metadata plumbing added to `uart_axi4_scoreboard`; failure analysis is now focused on validating the behaviour against live regressions.
- Timescale aligned across RTL and UVM sources (seven files corrected).
- Advanced coverage sequences and dynamic configuration tests implemented.
- Baud-rate configuration changes validated without regression failures.

### 3.4 Latest regression evidence (02 Oct 2025)

- `sim/uvm/run_uvm.ps1 -TestName register_comprehensive_test` (seed 1) executed at 2025-10-02 05:35 completed with `UVM_ERROR = 33`, `mismatch_count = 16`, and four unmatched AXI transactions attributed to reserved-space accesses (ADDR=0x00001020/0x00001024, RESP=0x2).
- The DSIM transcript (`sim/uvm/dsim.log`) confirms both read and write BRESP/RRESP failures despite the new reserved-address hook; expectation metadata either failed to latch or was dropped when sequences bypassed UART metadata.
- Coverage artefacts were generated under `sim/exec/coverage_report/` and the MXD waveform archived as `archive/waveforms/register_comprehensive_test_20251002_053320.mxd`; reuse these assets when correlating scoreboard behaviour.

## 4. Immediate priorities and success criteria (updated 02 Oct 2025)

The scoreboard regression must be cleared before pursuing the Phase 4 coverage stretch goals. Follow the investigation-first approach, then execute the aligned work plan from `coverage_work_plan_20251001.md`.

### 4.1 Investigation checklist — complete before implementing fixes

- [ ] Review `sim/uvm/dsim.log` around time 21 090 510 000 ps to confirm BRESP/RRESP `0x2` events at ADDR=0x00001020/0x00001024 and capture call stacks for both UART and AXI monitor messages.
- [ ] Inspect the scoreboard expectation queue (enable `UVM_HIGH` for `uart_axi4_scoreboard`) to verify whether `expect_error` is being autocompleted when `is_addr_reserved()` fires.
- [ ] Cross-check UART metadata: ensure `uart_expected_queue` receives entries for sequences that bypass the UART agent (direct AXI stimulus) and document any gaps in `docs/diary_20251002.md`.
- [ ] Confirm DSIM environment variables via `Test-DsimEnvironment` and note the exact `run_uvm.ps1` command (test name, seed, verbosity) used for reproducing the failure.
- [ ] Update the daily diary with the investigation findings before making RTL/UVM edits.

### 4.2 Action plan derived from `coverage_work_plan_20251001.md`

Progress through the phases in order; do not advance until exit criteria for the active phase are satisfied and recorded. Retain MXD waveforms and coverage bundles after every run.

#### Phase 0 – Regression baseline and scoreboard repair (Owner: Verification)

- [ ] Implement targeted logging or assertions inside `uart_axi4_scoreboard::verify_transaction_match()` to trace when reserved-address auto-classification triggers.
- [ ] Audit `register_sequences.sv` and any direct AXI sequences to ensure `expect_error` metadata is set for reserved ranges; patch missing cases.
- [ ] Re-run `register_comprehensive_test` with `-Coverage on -Verbosity UVM_LOW` and capture mismatch deltas; repeat until `mismatch_count == 0` and `UVM_ERROR == 0`.
- [ ] Archive the passing log, MXD, and coverage reports and summarise the fix path in the diary.

#### Phase 1 – Alignment & WSTRB coverage (Priority A)

- [ ] Clone `register_comprehensive_sequence` into `register_alignment_sequence` and randomise misaligned addresses (`ADDR % bytes_per_beat != 0`).
- [ ] Add partial-width write cases (8 b/16 b) with deterministic WSTRB patterns; verify scoreboard acceptance for each pattern.
- [ ] Extend functional coverpoints to sample `align_status` and `wstrb_coverage`, then drive the sequence until each bin records at least one hit.
- [ ] Exit when `align_status > 0 %` and `wstrb_coverage ≥ 40 %` in the coverage report.

#### Phase 2 – Burst cross coverage (Priority A)

- [ ] Introduce `multi_burst_sequence` with configurable burst lengths (1/2/4/8) and both incrementing and fixed-address modes.
- [ ] Ensure AXI monitor captures `burst_len_type_size`; confirm scoreboard handles the additional beats without leaving entries unmatched.
- [ ] Run directed regressions to populate cross bins until `burst_len_type_size ≥ 33 %` and the size distribution exceeds 55 %.

#### Phase 3 – Error/status campaign (Priority B)

- [ ] Augment `error_injection_sequence` to chain CRC faults, forced timeouts, and manual SLVERR responses within one simulation window.
- [ ] Use `bridge_status_vif` to hold the DUT BUSY and observe non-OK UART response statuses; log expected-error classifications in the scoreboard.
- [ ] Exit when `response_status ≥ 50 %` and combined error coverpoints reach ≥ 75 %.

#### Phase 4 – Expression coverage closure (Priority C)

- [ ] Develop `uart_axi4_busy_error_test` that maintains `system_busy` while forcing `bridge_error_code` to a non-zero value (e.g., invalid SOF).
- [ ] Confirm both branches of `system_busy && (bridge_error_code == 8'h00)` record hits in the expression report (target ≥ 87 %).
- [ ] Add assertions or scoreboard messages to detect regressions in future runs.

#### Phase D – Instrumentation & tracking (Priority D)

- [ ] Update `uart_axi4_coverage.sv` to emit per-coverpoint hit summaries during `final_phase` for rapid log triage.
- [ ] Tag all new sequences/tests with unique `uvm_info` headers to simplify log searches.
- [ ] Archive coverage HTML bundles and MXD files under timestamped directories and document paths in the diary.

### 4.3 Active TODO governance

- Every engineer is personally responsible for maintaining the live TODO list. Update the shared tracker (this document plus the repository TODO tooling or issue tracker) before and after each focused work block.
- When a checkbox above is completed, immediately annotate the completion date in the diary and reflect the status in the active TODO list; do not wait until the end of the day.
- New discoveries must result in new TODO entries—capture them in `docs/diary_YYYYMMDD.md` and replicate them in the shared tracker so that ownership remains visible.
- Periodically (at least once per day) reconcile the diary, this document, and the tracker to ensure no task is orphaned.

## 5. Operating procedure

### 5.1 Pre-flight checks

- [ ] Confirm environment variables are set and valid (`DSIM_HOME`, `DSIM_ROOT`, `DSIM_LIB_PATH`, and, if needed, `DSIM_LICENSE`). Avoid hard-coded absolute paths in scripts.
- [ ] Verify structural consistency: every `.sv` file begins with `` `timescale 1ns / 1ps ``, DUT and testbench interfaces match bit widths (see `rtl/AXIUART_Top.sv` and `sim/uvm/tb/uart_axi4_tb_top.sv`), and UVM components follow the required naming scheme.
- [ ] Review `docs/register_map.md`, `docs/uart_axi4_protocol.md`, and prior diaries before modifying sequences.

Suggested PowerShell helper (run from the repository root):

```powershell
function Test-DsimEnvironment {
    $vars = "DSIM_HOME","DSIM_ROOT","DSIM_LIB_PATH"
    foreach ($name in $vars) {
        $value = [Environment]::GetEnvironmentVariable($name)
        if (-not $value) { throw "$name is not set." }
        if (-not (Test-Path $value)) { throw "$name path '$value' does not exist." }
    }
}

Test-DsimEnvironment
```

### 5.2 Running UVM tests (PowerShell in `sim/exec/`)

Use `./run_uvm.ps1` for every compilation and simulation run; the checklist below keeps execution consistent and auditable.

- [ ] Open a PowerShell session in `sim/exec/`.
- [ ] Compile and run the target regression:

```powershell
./run_uvm.ps1 -TestName register_comprehensive_test -Mode run -Seed 12345 -Verbose UVM_MEDIUM
```

- [ ] Perform compile-only passes when validating structural changes:

```powershell
./run_uvm.ps1 -Mode compile
```

- [ ] Reuse the latest build artefacts when sweeping new seeds:

```powershell
./run_uvm.ps1 -Mode run -TestName uart_axi4_basic_test -Seed 67890
```

- [ ] Log each executed command, seed, runtime, and outcome in the daily diary.

Mandatory switches:

- [ ] Keep waveform dumping enabled (`-Waves on`) to generate MXD files under `archive/waveforms/` named after the test.
- [ ] Pass `-Coverage on` to capture `metrics.db`, then regenerate HTML via `dcreport.exe metrics.db -out_dir coverage_report`.
- [ ] Specify `-Verbose` level as needed (default `UVM_MEDIUM`) to aid debug while avoiding log bloat.

### 5.3 Post-run verification

- [ ] Inspect `logs/<testname>_<timestamp>.log` for `UVM_ERROR`, `UVM_FATAL`, and synthesis-style errors. Any non-zero count requires immediate triage.
- [ ] Confirm waveform generation (`archive/waveforms/<testname>.mxd`) and check size sanity (≥ 1 MB for substantive runs).
- [ ] Publish coverage deltas in the diary; if coverage regresses, document the suspected root cause and recovery plan.

## 6. Quality gates

| Gate | Definition | Evidence |
| ---- | ---------- | -------- |
| UVM stability | `UVM_ERROR = 0`, no `UVM_FATAL`, no compilation warnings | Test log excerpt, DSIM summary |
| Structural hygiene | `timescale 1ns / 1ps`, synchronous active-high reset, naming conventions enforced | Spot check scripts, code review |
| Coverage minimums | Line 100 %, Toggle ≥ 60 %, Expression ≥ 92 %, Functional ≥ 70 % | `coverage_report/index.html`, metrics dashboard |
| Artefact retention | MXD waveform, `metrics.db`, diary entry for the day | File sizes, repository history |

Do not close a task until all gates are satisfied or a documented exception is approved.

## 7. Coverage improvement roadmap

### 7.1 Toggle coverage (current 14.0 %)

- **Register map sweep (`register_block_inst`)**: extend `sequences/register_comprehensive_sequence.sv` to exercise every address from `0x1000` to `0x1FFF`, mixing byte/halfword/word accesses and aligned/misaligned cases.
- **Write/read pattern diversity**: randomise read-after-write, back-to-back bursts, and idle gaps. Use coverage bins to confirm each pattern is sampled.
- **Bit-field toggling**: add sequences that individually set/clear control bits and observe status transitions.
- **AXI handshake edges**: create tests forcing VALID/READY stalls, error responses, and outstanding transaction limits.

### 7.2 Expression coverage (current 83.3 %)

- Review all conditional logic in `rtl/Frame_Builder.sv`, `rtl/Frame_Parser.sv`, and `rtl/Axi4_Lite_Master.sv`.
- Ensure sequences trigger every `if/else`, `case` default, and ternary path. Vary timeouts, CRC outcomes, and parity checks.
- Inject UART receive errors (parity, framing, overrun) and FIFO overflow/underflow scenarios.

### 7.3 Functional coverage (current 25.0 %)

- Implement protocol covergroups under `sim/uvm/packages/uart_axi4_test_pkg.sv`:
  - Frame types vs. lengths vs. CRC result
  - AXI transfer alignment, response type, and burst behaviour
  - UART bridge state machine transitions and FIFO depth bins (empty/low/medium/high/full)
- Sample the covergroups in `uart_axi4_monitor` and guarantee instantiation in the monitor constructor.
- Cross-check coverage bins after each regression; expand sequences if bins stay empty for two consecutive runs.

### 7.4 Timeline goals

| Phase | Timebox | Toggle | Expression | Functional |
| ----- | ------- | ------ | ---------- | ---------- |
| 4.1 | Week 1 | ≥ 40 % | ≥ 88 % | ≥ 50 % |
| 4.2 | Week 2 | ≥ 50 % | ≥ 90 % | ≥ 60 % |
| 4.3 | Weeks 3–4 | ≥ 60 % | ≥ 92 % | ≥ 70 % |
| 5.1 | Month 2 | ≥ 75 % | ≥ 94 % | ≥ 80 % |
| 5.2 | Month 3 | ≥ 85 % | ≥ 96 % | ≥ 90 % |

Escalate if a target slips; log mitigation steps in the diary and update this document.

### 7.5 Advanced coverage acceleration (Phase 5)

- **Scenario layering**: Run mixed UART/AXI stress sequences that interleave frame retries, CRC faults, and register window scans to force concurrent state transitions.
- **Error campaign automation**: Build seeded lists of parity, framing, timeout, and CRC faults, then sweep them with constrained random delays to hit rare expression branches.
- **Coverage-directed generation**: Feed empty or low-hit bins from `coverage_report/index.html` back into sequence constraints (e.g., via YAML or JSON config) to bias stimulus toward uncovered cases.
- **Cross-module observations**: Enhance monitors to record FIFO depth, AXI response, and UART state in a single transaction object so cross covergroups fire reliably.
- **Regression hygiene**: Tag every run exceeding 30 minutes or generating new bins, archive MXD snapshots, and capture reproduction seeds in the diary for deterministic reruns.

## 8. Daily operations

### 8.1 Start-of-day checklist

- [ ] Review yesterday’s diary entry and open issues.
- [ ] Sync repository and confirm no outstanding lint or build failures.
- [ ] Re-run `Test-DsimEnvironment` and the timescale/naming spot checks if new files were added.

### 8.2 During the day

- [ ] Work in focused increments (≤ 2 hours).
- [ ] After each increment, record tests executed, seeds, and results.
- [ ] After each increment, update coverage deltas (line/toggle/expression/functional).
- [ ] After each increment, log newly discovered issues or hypotheses.
- [ ] Keep waveforms only for failing or newly exercised scenarios; archive others weekly to manage storage.

### 8.3 End-of-day deliverables

- [ ] Ensure `UVM_ERROR = 0` on the latest run.
- [ ] Update `docs/diary_YYYYMMDD.md` with completed tasks and artefacts.
- [ ] Record the day’s coverage snapshot (with trend vs. previous day).
- [ ] Document remaining blockers and the next-day plan.
- [ ] Submit any documentation updates (including this file) via the standard review process.

### 8.4 Progress report template (paste into the diary)

```markdown
## Phase 4 Daily Progress – YYYY-MM-DD

### Completed today
- [x] Task 1 summary
- Coverage: Line xx % / Toggle xx % / Expression xx % / Functional xx % (Δ vs. previous day)

### Issues and risks
- Issue description → planned fix or owner

### Plan for tomorrow
- [ ] Task 1
- [ ] Task 2
```

## 9. Troubleshooting quick reference

| Symptom | Likely cause | Resolution |
| ------- | ------------ | ---------- |
| `UVM_ERROR` appears in log | Sequence constraints impossible | Relax constraints, rerun with different seed, review driver behaviour |
| No coverage data (`metrics.db` missing) | `-Coverage on` not passed or run aborted | Rerun with coverage enabled and ensure simulation completes |
| Waveform missing | `-Waves` disabled or archive path incorrect | Verify `run_uvm.ps1` arguments; confirm MXD file in `archive/waveforms/` |
| Timescale mismatch errors | File missing the standard directive | Add `` `timescale 1ns / 1ps `` at line 1 and re-run checks |
| DSIM cannot locate libraries | Environment variables not exported | Rerun `Test-DsimEnvironment`, fix PATH/variables in the shell profile |
| Simulation memory exhaustion | Excessive waveform window or large randomisation | Limit captured hierarchy, enable `+define+DSIM_FAST_COMPILE`, or split tests |

Use `Get-Content dsim.log | Select-String -Pattern "UVM_ERROR"` to extract problematic lines during triage.

## 10. Completion checklist and hand-off

Before closing a task or handing off to the next engineer:

- [ ] Latest regression passes with `UVM_ERROR = 0` and no warnings.
- [ ] Coverage targets for the milestone are met or gaps are documented with action items.
- [ ] Waveform (`archive/waveforms/<test>.mxd`), `metrics.db`, and HTML coverage report are stored and referenced in the diary.
- [ ] `docs/diary_YYYYMMDD.md` created or updated with the day’s findings.
- [ ] Create a completion summary if the milestone warrants it: `docs/completion_report_YYYY-MM-DD_HHmm.md` (can reuse the PowerShell helper from `run_guide.md`).

## 11. Reference materials

- `docs/design_overview.md` – architectural summary
- `docs/system_architecture.md` – block-level and interface detail
- `docs/register_map.md` – complete register definitions
- `docs/uart_axi4_protocol.md` – transaction framing rules
- `docs/uvm_testplan.md` – full test matrix and coverage intent
- `docs/uvm_verification_plan.md` – verification strategy baseline
- `docs/coverage_improvement_plan_20250928.md` – detailed backlog supporting this guide
- [DSIM User Manual](https://help.metrics.ca/support/solutions/articles/154000141193)
- IEEE 1800.2-2017 UVM standard

---

Operate with discipline, document every insight, and elevate coverage without sacrificing stability. The next engineer should be able to resume work by following these steps precisely.
