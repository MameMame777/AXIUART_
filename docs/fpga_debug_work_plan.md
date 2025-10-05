# FPGA UART-AXI Bridge RTL Debug Work Plan

- **Author**: GitHub Copilot
- **Created**: 2025-10-05
- **Last Updated**: 2025-10-05
- **Purpose Alignment**: Close the gap between the RTL implementation and the UART-AXI bridge protocol so that hardware and simulation produce identical SOF, STATUS, and CRC8 behaviour.
- **References**: `docs/uart_axi4_protocol.md`, `docs/register_map.md`, `docs/design_overview.md`, `docs/uvm_verification_plan.md`, lab diaries dated 2025-09-28 to 2025-10-05.

---

## 🧭 Objectives and Success Criteria

1. Restore protocol compliance by ensuring SOF=$0x5A$ and STATUS values {0x00 (OK), 0x06 (BUSY), 0x0E (ERROR)} across READ and WRITE transactions.
2. Achieve CRC8 parity between RTL, Python reference (`software/crc8_validation.py`), and captured hardware frames for at least three command types (single READ, single WRITE, burst READ).
3. Deliver a reusable debug instrumentation package (mark-debug nets + ILA configuration) that validates the issue within **two Vivado builds**.
4. Provide a documented root-cause report and mitigation plan within **24 hours** of data capture completion.

Success for this work package is declared when the acceptance checks listed in [✅ Exit Gates](#-exit-gates) are satisfied.

---

## 🚨 Current Symptoms (Measured Baseline)

| ID | Scenario | Expected Behaviour | Observed Behaviour | Evidence Source |
|----|----------|-------------------|--------------------|-----------------|
| P1 | UART command SOF (0x5A) | UART TX first byte = 0x5A | UART TX first byte = 0xAD | Saleae capture run `2025-10-04_23-17`, `protocol_compliant_test.py` log line 143 |
| P2 | READ STATUS response | STATUS byte = 0x06 when bridge busy | STATUS byte = 0x80 | `fpga_register_test.py` case `read_status_busy`, DSIM log snippet stored in `archive/waveforms/uart_status_issue_20251004.mxd` |
| P3 | WRITE STATUS response | STATUS byte ∈ {0x00,0x0E} | STATUS byte = 0x82 | Same as P2 |
| P4 | CRC8 verification | CRC8 RTL = CRC8 Python model | RTL CRC mismatched for 100% of captures | `protocol_compliant_test.py` aggregated summary, run ID `CRCREF_FAIL_20251004` |

Each symptom must be reproducible after reset using `software/protocol_compliant_test.py --seed 20251005 --scenarios basic,burst`.

---

## 🔍 Investigation Backlog (Ranked)

| Priority | Track | Question | Required Signals/Artifacts | Owner | Due |
|----------|-------|----------|----------------------------|-------|-----|
| A1 | RTL: Frame_Builder | Why is 0xAD emitted instead of 0x5A? | `debug_sof_raw`, `debug_sof_sent`, UART TX stream, finite-state step ID | RTL engineer | +0.5 day |
| A2 | RTL: CRC pipeline | Does the CRC accumulator receive the correct byte order? | `debug_crc_input`, `debug_crc_result`, `debug_crc_enable`, DSIM waveform per cycle | RTL engineer | +0.5 day |
| A3 | RTL: Frame_Parser | Where do STATUS codes diverge? | `debug_status_gen`, `debug_error_cause`, `debug_busy_flag`, AXI response flags | Verification lead | +1.0 day |
| B1 | AXI4-Lite interface | Are AXI resp codes mapping correctly to STATUS? | `debug_axi_bresp`, `debug_axi_rresp`, `debug_axi_state` | RTL engineer | +1.0 day |
| C1 | System init | Is `bridge_enable` asserted before first command? | `bridge_enable`, reset synchroniser output, ILA trigger at reset release | Lab engineer | +0.5 day |
| C2 | Clock/timing | Any CDC or baud mismatches? | UART baud counter, AXI clock lock, DSIM timing report | Lab engineer | +1.5 day |

**Assumption**: Roles correspond to the existing project organisation (RTL engineer = design owner, Verification lead = UVM owner, Lab engineer = FPGA operations). Adjust assignments if staffing changes.

---

## 🛠️ Debug Instrumentation Roadmap

### Phase 1 — Frame_Builder Focus (Target completion: +6 hours)

| Signal | Width | Insertion Point | Capture Goal | Acceptance |
|--------|-------|-----------------|--------------|------------|
| `debug_sof_raw` | 8 | `rtl/Frame_Builder.sv` before SOF correction LUT | Confirm raw constant equals 0x5A | Matches 0x5A on every frame start |
| `debug_sof_sent` | 8 | After UART staging FIFO | Confirm transmitted byte | Equals 0x5A when UART `debug_uart_tx_valid` rises |
| `debug_sof_valid` | 1 | FSM state `FRAME_SOF` | Align timing of SOF | High for exactly one cycle per frame |
| `debug_crc_input` | 8 | CRC module input bus | Verify byte ordering | Sequence matches payload order logged by Python script |
| `debug_crc_result` | 8 | End of CRC pipeline | Correlate with transmitted CRC | Matches `crc8_validation.py` output |
| `debug_frame_state` | 4 | Frame builder FSM | Provide state decode | Numeric trace matches state table in `docs/design_overview.md` |

### Phase 2 — Frame_Parser Focus (Target completion: +8 hours)

| Signal | Width | Capture Goal | Cross-Check |
|--------|-------|--------------|-------------|
| `debug_rx_sof_raw` | 8 | Validate received SOF before correction | Compare with UART RX bytes |
| `debug_rx_sof_proc` | 8 | Confirm corrected SOF equals 0x5A | Should equal 0x5A before STATUS stage |
| `debug_crc_match` | 1 | Determine CRC decision timing | Align with STATUS update cycle |
| `debug_status_gen` | 8 | Trace raw STATUS selection | Ensure mapping table matches protocol spec |
| `debug_error_cause` | 4 | Classify error source | Use enumerated decode per table below |

Error cause encoding (update RTL if missing):

| Code | Meaning | Action |
|------|---------|--------|
| 0x0 | No error | Continue |
| 0x1 | CRC mismatch | Flag test vector |
| 0x2 | AXI timeout | Check `debug_axi_timeout` |
| 0x3 | Unsupported command | Confirm register map |
| 0x4 | Parser desync | Inspect UART RX |

### Phase 3 — UART Transport (Target completion: +10 hours)

Attach UART TX/RX signals with MXD depth ≥ 16k samples.

| Signal | Width | Purpose |
|--------|-------|---------|
| `debug_uart_tx_data` | 8 | Cross-check frame emission order |
| `debug_uart_tx_valid` | 1 | Identify start of each byte |
| `debug_uart_rx_data` | 8 | Validate incoming payload |
| `debug_uart_rx_valid` | 1 | Align parser timing |

### Phase 4 — AXI4-Lite Transaction Visibility (Target completion: +12 hours)

| Signal | Width | Purpose | Correlation |
|--------|-------|---------|-------------|
| `debug_axi_awaddr` | 32 | Track write target addresses | Compare with `register_map.md` |
| `debug_axi_wdata` | 32 | Confirm data ordering | Should match Python writes |
| `debug_axi_bresp` | 2 | Bridge AXI errors to STATUS | Map {00→OK, 10→SLVERR} |
| `debug_axi_araddr` | 32 | Track read addresses | |
| `debug_axi_rresp` | 2 | Validate read response | |
| `debug_axi_state` | 4 | Snapshot FSM state | Document decode in RTL comment |

Every marked signal must be added with `(* mark_debug = "true" *)` and documented in `rtl/Frame_Builder.sv`, `rtl/Frame_Parser.sv`, and `rtl/AXIUART_Top.sv` comment blocks.

---

## 📅 Execution Timeline & Responsibilities

| Step | Description | Owner | Duration | Pre-Req | Deliverable | Exit Criteria |
|------|-------------|-------|----------|---------|-------------|---------------|
| S1 | Instrument RTL (Phases 1 & 2) | RTL engineer | 6 h | Code review of signal widths | Git commit `rtl_debug_signals_phase12` | Lint clean, DSIM compile passes |
| S2 | Instrument RTL (Phases 3 & 4) | RTL engineer | 4 h | Completion of S1 | Commit `rtl_debug_signals_phase34` | ILA netlist updated with new probes |
| S3 | Update Vivado project & generate bitstream | Lab engineer | 3 h | S1–S2 | Bitstream `AXIUART_dbg_YYYYMMDD.bit` | Implementation log with 0 critical warnings |
| S4 | Deploy to FPGA, sanity reset check | Lab engineer | 1 h | S3 | Flash log, reset checklist | UART idle pattern `0x55` observed |
| S5 | Run automated protocol sweep | Verification lead | 2 h | S4 | `protocol_compliant_test.py` report, raw UART capture | Report stored under `archive/waveforms/<timestamp>` |
| S6 | Waveform triage & root-cause analysis | Cross team | 4 h | S5 | Annotated MXD snapshot, triage notes in diary | Root cause hypothesis documented |
| S7 | Implement corrective RTL patch | RTL engineer | 4 h | S6 | Commit `rtl_fix_<issue>` | DSIM + FPGA regression clean |
| S8 | Final validation & documentation | Verification lead | 3 h | S7 | Updated docs, diary entry, coverage delta | ✅ Exit Gates passed |

Time estimates assume single-threaded execution; parallelise S1/S2 with code reviews where possible.

---

## ✅ Exit Gates

| Gate | Verification Method | Threshold |
|------|---------------------|-----------|
| G1 | `protocol_compliant_test.py --scenarios basic,burst --iterations 50` | 0 protocol failures, STATUS limited to spec values |
| G2 | Hardware capture vs. Python CRC report | CRC mismatch rate ≤ 1% (allowing for capture noise); target 0% |
| G3 | MXD waveform review | SOF byte equals 0x5A on three consecutive frames |
| G4 | DSIM regression (`sim/run_uvm.ps1 -Test uart_smoke_test`) | No `UVM_ERROR`, coverage ≥ 85% for sequence group `UART_Frame_Sequence` |
| G5 | Documentation | Updated diary entry (`docs/diary_20251005_fpga_issue_solution.md`), this plan, and root-cause memo published |

Failure to meet any gate triggers a return to the corresponding step with a corrective action item recorded in the diary.

---

## 📋 Detailed Task Checklist

### Step 1 — RTL Debug Signals

- [ ] Insert mark-debug nets listed in Phase 1 & Phase 2 tables.
- [ ] Add comments referencing this plan for traceability.
- [ ] Run `sim/run_uvm.ps1 -Mode compile` to confirm DSIM accepts new nets.
- [ ] Capture screenshot of DSIM compile summary and archive under `archive/waveforms/logs/`.

### Step 2 — Vivado Integration

- [ ] Regenerate `sim/exec/dsim_config.f` if file paths changed.
- [ ] Update Vivado ILA core to include all Phase 1–4 signals (grouped by subsystem).
- [ ] Verify environment variables (`DSIM_HOME`, `DSIM_LIB_PATH`, `DSIM_ROOT`) using `scripts/env_check.ps1` (new script requirement).
- [ ] Store the generated bitstream and ILA configuration under `PandR/output/YYYYMMDD/`.

### Step 3 — Data Capture

- [ ] Configure trigger: `debug_sof_sent == 8'hAD` OR `debug_crc_match == 1'b0`.
- [ ] Run `protocol_compliant_test.py --scenarios basic,burst --iterations 20` before final long sweep.
- [ ] Save Saleae/ILA captures using naming convention `YYYYMMDD_HHMM_<test>_<seed>.mxd`.
- [ ] Log ambient lab conditions (supply voltage, FPGA temperature) in diary for repeatability.

### Step 4 — Analysis & Fix

- [ ] Align hardware UART traces with Python transaction logs using the timestamp column.
- [ ] Document the cycle of divergence for STATUS anomalies (include waveform screenshot).
- [ ] Propose RTL fix with state transition diagram update in `docs/design_overview.md`.
- [ ] Perform DSIM regression (`sim/run_uvm.ps1 -Test uart_full_regression`) post-fix.

### Step 5 — Closure

- [ ] Update this plan’s revision table and archive previous revision under `archive/`.
- [ ] Publish `docs/diary_20251005_fpga_issue_solution.md` with root cause narrative.
- [ ] Confirm protocol compliance on hardware with two independent seeds.
- [ ] Submit coverage report (`coverage_report/index.html`) linked from `docs/uvm_verification_review_report.md`.

---

## 🧪 Tooling & Script Usage

### Existing Scripts

| Script | Purpose | Invocation | Expected Output |
|--------|---------|------------|-----------------|
| `protocol_compliant_test.py` | End-to-end protocol validation with CRC sweep | `python protocol_compliant_test.py --seed 20251005 --scenarios basic,burst --iterations 50` | CSV log `output/protocol_summary_<timestamp>.csv`, console summary |
| `uart_axi_register_access.py` | UART-AXI bridge API | Imported by tests | Exceptions on protocol violations |
| `fpga_register_test.py` | Register-level stress | `python fpga_register_test.py --pattern smoke` | Pass/fail summary per register |
| `crc8_validation.py` | Reference CRC model | `python crc8_validation.py --export vectors.csv` | `vectors.csv` with golden frames |

### New Script Requirements

1. `fpga_debug_helper.py`
   - Generate Vivado TCL to attach ILA probes (auto-group by subsystem).
   - Export trigger presets aligned with Phase 1–4 objectives.
   - Provide MXD viewer bookmarks for SOF, CRC, STATUS events.

2. `hardware_verification.py`
   - Reconstruct transformation mapping from captured UART data.
   - Compare hardware vs. software frames and flag byte-level discrepancies.
   - Produce HTML summary for lab review.

Both scripts must log outputs into `archive/waveforms/tools/` and include timestamped filenames.

---

## 📌 Risk Register

| Risk ID | Description | Impact | Mitigation | Owner |
|---------|-------------|--------|------------|-------|
| R1 | Mark-debug nets exceed ILA probe limit | Loss of visibility | Use hierarchical probing, split phases across builds | RTL engineer |
| R2 | DSIM compile time increases significantly | Schedule slip | Enable incremental compilation, run overnight builds | Verification lead |
| R3 | Hardware capture fails due to lab setup | No data | Validate cables, run loopback test before main capture | Lab engineer |
| R4 | CRC mismatch persists after instrumentation | Root cause obscured | Escalate to architecture review, verify Python reference | Cross team |

---

## 🗃️ Deliverables & Documentation

- Updated RTL files with mark-debug nets (Phases 1–4).
- Vivado project snapshot (`PandR/projects/AXIUART_dbg_<timestamp>.xpr`).
- Hardware capture set (`archive/waveforms/YYYYMMDD/` with MXD and CSV logs).
- Root-cause report appended to `docs/diary_20251005_fpga_issue_solution.md`.
- Coverage report generated via `dcreport.exe metrics.db -out_dir coverage_report` and linked in `docs/uvm_verification_review_report.md`.

All documents must be in English, follow existing naming conventions, and include revision history.

---

## 📞 Communication Cadence

- Daily 09:00 stand-up (15 minutes) — focus on blockers for S1–S8 steps.
- Ad-hoc sync immediately after any failed exit gate (G1–G4).
- Final review meeting once ✅ Exit Gates are met; include architecture and verification leads.

Meeting notes are to be stored in `docs/diary_YYYYMMDD.md` with clear action items.

---

## 📄 Revision History

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 1.0 | 2025-10-05 | GitHub Copilot | Initial English rewrite with concrete tasks, metrics, and exit gates. |
