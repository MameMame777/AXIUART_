# AXIUART Coverage Improvement Work Plan (2025-10-01)

## Purpose

- Restore momentum on the Phase 4 coverage campaign by documenting the latest metrics and the concrete steps required to reach the short-term targets from `coverage_improvement_plan_20250928.md`.
- Focus on functional and expression coverage blind spots revealed by the most recent DSIM run (`uart_axi4_multi_beat_write_test`, seed 20251001).
- Provide an actionable playbook that fits within the existing verification methodology (UVM on DSIM, MXD waveform capture, mandatory `run_uvm.ps1` harness).

## Current Coverage Snapshot

| Metric | Latest Value | Short-Term Goal | Notes |
|--------|--------------|-----------------|-------|
| Line | 100.0% | 100% | Stable; keep regression green. |
| Expression (AXIUART_Top) | 66.7% | ≥87% | Single conditional `system_busy && (bridge_error_code == 8'h00)` missing the "false" branch. |
| Functional (frame_coverage) | 32.05% | ≥40% | `align_status` bins never sampled; `wstrb_coverage` and `rw_size_len` very sparse. |
| Functional (burst_coverage) | 47.92% | ≥55% | Cross `burst_len_type_size` stuck at 8.33% because only one combination has been exercised. |
| Functional (error_coverage) | 50.00% | ≥60% | Need explicit exercises of CRC bad, timeout, and AXI error scenarios in the same regression window. |

### Coverpoint Gaps

- `align_status`: 0% — no misaligned frames sampled after the parser alignment fixes.
- `wstrb_coverage`: 14.29% — only full-word writes observed; partial strobes absent.
- `rw_size_len`: 8.33% — limited cross combinations between read/write, size, and burst length.
- `burst_len_type_size`: 8.33% — only a single size/length combination logged for burst coverage.
- `response_status`: 12.50% — UART status responses rarely leave `STATUS_OK`.
- Expression hole: need a stimulus where `system_busy` is high while `bridge_error_code != 8'h00`.

## Improvement Strategy

1. **Stimulus Expansion (Priority A)**
   - Enhance the register sweep sequence to request misaligned writes/reads (`ADDR % bytes_per_beat != 0`) over multi-beat bursts.
   - Introduce partial-width write scenarios by generating UART commands with size=8b/16b and targeted WSTRB patterns.
   - Randomize burst lengths up to 8 beats with both incrementing and fixed address modes to populate `burst_len_type_size`.

2. **Error-Response Campaign (Priority B)**
   - Extend `error_injection_sequence` to inject CRC faults, forced timeouts, and manual AXI SLVERR responses in a single regression run.
   - Hold the bridge in a BUSY state via `bridge_status_vif` to hit non-OK UART response bins.

3. **Expression Coverage Closure (Priority C)**
   - Create a directed test that keeps the DUT busy while forcing a non-zero bridge error code (e.g., invalid SOF → parser error).
   - Ensure both the true and false branches of the `system_busy && (bridge_error_code == 8'h00)` condition are observed within one scenario.

4. **Instrumentation & Tracking (Priority D)
   - Update `uart_axi4_coverage.sv` to log per-coverpoint hit counts during final phase to ease tracking.
   - Tag new sequences with `uvm_info` headers for easier log grep and wave debug.

## Execution Roadmap

| Phase | Objective | Key Actions | Owner | Exit Criteria |
|-------|-----------|-------------|-------|----------------|
| Phase 0 | Baseline confirmation | Re-run `uart_axi4_multi_beat_write_test` after each sequence change with `-Coverage on` | Verification | Coverage report captured, UVM_ERROR == 0 |
| Phase 1 | Address alignment & WSTRB coverage | Modify `register_comprehensive_sequence` (new variant `register_alignment_sequence`) to sweep misaligned addresses and partial strobes | Verification | `align_status` > 0%, `wstrb_coverage` ≥ 40% |
| Phase 2 | Expand burst cross coverage | Add multi-size burst scenarios in `basic_func_sequence` extension (`multi_burst_sequence`) | Verification | `burst_len_type_size` ≥ 33%, `size_field` ≥ 55% |
| Phase 3 | Error/Status coverage push | Augment `error_injection_sequence` with chained CRC/timeout/AXI error stimuli; gate responses through scoreboard | Verification + Design | `response_status` ≥ 50%, error coverpoints ≥ 75% |
| Phase 4 | Expression closure | Create `uart_axi4_busy_error_test` to exercise `system_busy` with non-zero `bridge_error_code` | Verification | Expression coverage ≥ 87% |

## Test & Tooling Requirements

- Always launch simulations via PowerShell:

   ```powershell
   Set-Location -Path "e:\Nautilus\workspace\fpgawork\AXIUART_\sim\exec"
   ./run_uvm.ps1 -TestName <target_test> -Mode run -Seed <seed> -Waves on -Coverage on -Verbosity UVM_LOW
   ```

- Confirm DSIM environment variables (`DSIM_HOME`, `DSIM_LIB_PATH`, `DSIM_ROOT`) before regression.
- Enable MXD waveform dumping; name files `<test>_<timestamp>.mxd` (already automatic).
- After each regression, archive the coverage HTML bundle and update this plan if metrics shift.

## Risks & Mitigations

| Risk | Impact | Mitigation |
|------|--------|------------|
| Misaligned access may trigger DUT assertion failures | High | Leverage existing scoreboard checks; add incremental ramp-up (single beat → multi beat). |
| Error-injection may destabilize regression (timeouts) | Medium | Add watchdog to stop sequence after error response, ensure scoreboard filters expected errors. |
| Additional covergroups raise simulation time | Medium | Use incremental compilation (`run_uvm.ps1 -Mode compile`) and selective test lists. |

## Reporting & Handover

- Record daily progress in the `docs/diary_YYYYMMDD.md` series (next entry: `diary_20251001.md`).
- Capture any new coverage artifacts in `archive/waveforms/` with accompanying README updates.
- Review progress against the original `coverage_improvement_plan_20250928.md` each Friday.
- Share updated metrics and open issues in the weekly verification sync.

## Next Actions (2025-10-02)

1. Implement `register_alignment_sequence` under `sim/uvm/sequences/register_sequences.sv`.
2. Add BUSY/ERROR response hooks to the UART scoreboard so expected error bins are recognized.
3. Draft diary entry summarizing the new plan and initial implementation steps.
