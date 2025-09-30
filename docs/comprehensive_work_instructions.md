# AXIUART SystemVerilog UVM Verification – Comprehensive Work Instructions

_Last updated: 2025-09-30_  
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

## 3. Project snapshot (30 Sep 2025)

### 3.0 Goal and status summary

- **Project goal**: Deliver a production-ready UART ⇔ AXI4-Lite bridge with UVM-driven verification that maintains `UVM_ERROR = 0`, achieves ≥ 60 % toggle coverage in Phase 4, and progresses toward the Phase 5 stretch targets without sacrificing stability.
- **Current status (2025-09-30)**:
  - Regressions finish in ≤ 322 ms with `UVM_ERROR = 0` across curated tests.
  - Coverage snapshot — Line 100 %, Toggle 14.0 %, Expression 83.3 %, Functional 25.0 %; disable-focused `register_comprehensive_test` (seed 12345, quiet-period multiplier 4) now reports Frame 50.13 %, Burst 46.88 %, Error 50.00 %, Total 49.00 %, while the standalone `register_block_test` still lags at Frame 29.55 %, Burst 28.13 %, Error 50.00 %, Total 35.89 % and leaves 17 UART responses unmatched in the scoreboard.
  - Tooling (`run_uvm.ps1`, MXD wave capture, metrics export) is stable; next focus areas are register access diversity and asynchronous UART error scenarios.

### 3.1 System overview

- UART runs at 115 200 bps and bridges to a 32-bit AXI4-Lite interface.
- The design includes a 64-entry synchronous FIFO, CRC8 protection, and custom framing.
- Verification uses SystemVerilog UVM 1.2 with DSIM and MXD waveform dumps.

### 3.2 Verification status

- **Stability**: latest regression completes in ≤ 322 ms with `UVM_ERROR = 0`.
- **Infrastructure**: `run_uvm.ps1` standardises compilation, execution, waveform (MXD), and metrics export.
- **Coverage summary**:

| Metric | Previous | Current | Next milestone | Stretch goal |
| ------ | -------- | ------- | -------------- | ------------ |
| Line | 100.0 % | 100.0 % | 100.0 % (maintain) | 100.0 % |
| Toggle | 22.7 % | 14.0 % | ≥ 60 % (Phase 4 lock-in) | ≥ 85 % (Phase 5) |
| Expression | 66.7 % | 83.3 % | ≥ 92 % (Phase 4) | ≥ 96 % (Phase 5) |
| Functional | 0.0 % | 25.0 % | ≥ 70 % (Phase 4) | ≥ 90 % (Phase 5) |

> Focus: `register_block_inst` toggle coverage is 13.7 %. Prioritise register access diversity, parallel AXI transactions, and asynchronous UART error scenarios to unlock the ≥ 60 % milestone.

### 3.3 Key achievements to date

- `UVM_ERROR = 0` maintained across all curated tests.
- Timescale aligned across RTL and UVM sources (seven files corrected).
- Advanced coverage sequences and dynamic configuration tests implemented.
- Baud-rate configuration changes validated without regression failures.

## 4. Immediate priorities and success criteria

- [ ] **Drive toggle coverage** to ≥ 50 % within the next two regressions and lock in ≥ 60 % before closing Phase 4. Plan follow-up work that elevates the metric to ≥ 85 % during Phase 5 by stressing concurrent register, UART, and AXI activity.
- [ ] **Push expression coverage** past ≥ 92 % in Phase 4 by exhausting every conditional path, then pursue ≥ 96 % in Phase 5 through rare-error injection, timeout variations, and watchdog sequencing.
- [ ] **Build functional coverage** infrastructure that measures ≥ 70 % by the Phase 4 exit review, then extend covergroups (frame cross, AXI response × FIFO depth, recovery paths) to achieve ≥ 90 % in Phase 5.
- [ ] **Retain perfect stability**: any run with `UVM_ERROR > 0` or compilation warnings is a blocker and must be resolved before chasing higher coverage.

### 4.1 Next action checklist – bridge_enable toggle recovery

Use the following checklist to drive the next verification sprint. Replace `□` with `■` (full-width characters) as each item is completed, and record progress in `docs/diary_YYYYMMDD.md`.

#### Phase A – Verify CONTROL register propagation

- ■ Capture the UART-side CONTROL writes
  - ■ Tag the relevant transactions in `register_comprehensive_access_sequence` logs (time stamp and command field) for quick correlation.
  - ■ Add a temporary comment in the diary noting the expected disable window length.
- ■ Read back the CONTROL register immediately after each disable attempt
  - ■ Extend the sequence with a post-write read and compare result; log discrepancies with `uvm_error`.
  - ■ Preserve the change set so it can be reverted once confirmation is complete.

#### Phase B – Observe DUT response during the disable window

- □ Inspect AXI4-Lite handshake in the waveform
  - □ Check that `axi_internal.awvalid/awready` and `wvalid/wready` assert while `bridge_enable` is expected to drop.
  - □ Ensure `internal_rst` within `AXIUART_Top` does not reset the bridge before the write commits.
- □ Instrument additional status if needed
  - □ Enable `bridge_status_monitor` debug messaging (`UVM_MEDIUM`) to capture timestamps for low/high transitions.
  - □ Document any RTL signals that need temporary visibility (`DEFINE_SIM` outputs only).

#### Phase C – Force a confirmed low transition

- ■ Introduce a dedicated disable experiment
  - ■ Add a focused sequence step that writes `0x0000_0000` with extended idle cycles afterward.
  - □ Optionally drive an out-of-band AXI-lite stimulus (compile-time guard) if UART writes still fail to propagate.
- ■ Re-run `register_comprehensive_test`
  - ■ Execute `run_uvm.ps1` with coverage enabled and archive the resulting MXD.
  - ■ Verify that `bridge_status_monitor` reports a low transition and that the toggle bin is no longer empty.

#### Phase D – Close the loop

- ■ Update `docs/diary_YYYYMMDD.md`
  - ■ Summarise observations, commands executed, and coverage deltas.
  - ■ Note any temporary code left in place and the plan for removal.
- ■ Refresh this checklist
  - ■ Replace completed `□` symbols with `■`.
  - □ Add new action items if additional gaps are uncovered during execution.

### 4.2 Next action checklist – Documentation alignment and disable coverage drive

Once the verification plan and register block documentation reflect the current CONTROL disable behaviour, execute the following sequence to lift coverage and solidify scoreboard handling. Replace `□` with `■` as work completes and capture outcomes in the daily diary.

#### Phase E – Synchronise documentation and design intent

- ■ Update `docs/uvm_verification_plan.md`
  - ■ Insert disable/enable scenarios into the feature matrix with explicit coverage targets (toggle ≥ 80 %, functional ≥ 70 %).
  - ■ Document scoreboard expectations for CONTROL writes during the disabled window and the required response handling.
- ■ Refresh `docs/register_map.md`
  - ■ Clarify CONTROL register semantics, including BUSY status returns and permissible operations while the bridge is disabled.
  - ■ Add timing notes for disable window entry/exit so testbench delays can be derived unambiguously.
- ■ Cross-link both documents
  - ■ Reference the updated sections from `docs/design_overview.md` and `docs/system_architecture.md` to keep high-level artefacts consistent.
  - ■ Record document revision IDs in `docs/diary_YYYYMMDD.md` for traceability.

#### Phase F – Expand disable-period stimulus toward ≥ 80 % coverage

- ■ Analyse existing coverage hot spots
  - ■ Parsed `sim/uvm/dsim.log` for `register_block_test`, capturing Frame 29.55 %, Burst 28.13 %, Error 50.00 %, Total 35.89 % and confirming 17 unmatched UART responses pending scoreboard classification.
  - ■ Correlated the results with the `register_comprehensive_test` (seed 12345) snapshot (Frame 50.13 %, Burst 46.88 %, Error 50.00 %, Total 49.00 %) to confirm disable stimulus still under-drives AXI handshake bins and leaves `register_block_inst` toggle coverage at 13.7 %.
- □ Design new UVM sequences
  - □ Create constrained-random disable windows varying idle duration, intervening AXI traffic, and UART command mix.
  - □ Add directed tests that interleave disable periods with read/write bursts and error injection (CRC, timeout) to force rare branches.
- □ Implement and integrate stimulus
  - □ Extend `uart_axi4_register_block_sequence.sv` (or derivative) with parameterised disable patterns and functional coverage sampling.
  - □ Register the new tests in the regression manifest and ensure `run_uvm.ps1` entries include `-Coverage on`.
- □ Validate coverage lift
  - □ Run focused regressions capturing MXD and metrics artefacts; archive seeds that produce new bins.
  - □ Confirm toggle coverage for the disable feature reaches ≥ 80 % and functional coverage crosses ≥ 70 %; document deltas in the diary.

#### Phase G – Refine scoreboard UART response handling

- □ Define response classification rules
  - □ Enumerate which UART frames are acknowledgements without AXI counterparts and codify them as allowable unmatched responses.
  - □ Add requirements to the verification plan so future contributors recognise the expected behaviour.
- □ Implement scoreboard enhancements
  - □ Introduce a dedicated response queue or flag in `uart_axi4_scoreboard` to separate status frames from request transactions.
  - □ Update checks to promote unmatched-but-expected responses to informational logs while preserving true mismatch detection.
- □ Update testbench observability
  - □ Augment monitors or analysis FIFOs to tag UART items with response metadata for the scoreboard.
  - □ Add functional coverage points that validate classification of CONTROL disable acknowledgements.
- □ Regression and documentation closure
  - □ Re-run the disable-focused regression suite and confirm the scoreboard warning about unmatched UART frames is resolved or downgraded per design.
  - □ Capture the implementation summary in `docs/diary_YYYYMMDD.md` and update `docs/uvm_verification_plan.md` with the new checking strategy.

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
