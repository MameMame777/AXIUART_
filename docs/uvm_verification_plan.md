# AXIUART UVM Verification Plan

Last updated: 2025-09-30

This plan captures the current verification intent for the AXIUART UART ⇔ AXI4-Lite bridge. It augments the historical test plan by explicitly covering the CONTROL disable/enable flow and the scoreboard expectations introduced during Phase 4.

## 1. Feature matrix and coverage targets

| Feature | Description | Primary sequences / tests | Coverage targets |
| --- | --- | --- | --- |
| CONTROL disable / enable sequencing | Verify that CONTROL writes propagate across the UART link, gate AXI activity, and restore normal operation after re-enable. | `register_comprehensive_access_sequence`, `register_comprehensive_test`, disable-focused stress sequences (TBD). | Toggle ≥ 80 %, Functional ≥ 70 %, Expression ≥ 92 % on disable branches. |
| CONTROL busy / partial readback handling | Exercise STATUS_BUSY responses and truncated CONTROL readbacks, ensuring retries escalate to monitor-based confirmation without UVM errors. | `verify_control_readback` helper, CONTROL-specific regression seeds. | Expression ≥ 92 %, Functional ≥ 70 %, Scoreboard warnings ≤ INFO. |
| Bridge status monitoring | Correlate `bridge_status_monitor` transitions with CONTROL traffic and ensure disable periods block outbound AXI transactions. | `register_comprehensive_test`, disable window extensions, AXI handshake monitors. | Toggle ≥ 85 % for `bridge_enable`, Functional ≥ 70 % for status bins. |
| Scoreboard response classification | Distinguish UART status frames without AXI counterparts from true mismatches and emit informational logs only. | Updated `uart_axi4_scoreboard`, CONTROL disable regression suite. | Zero residual WARN/ERROR for expected status responses, Functional coverage bins for classification hit. |

## 2. Scenario definitions

### 2.1 CONTROL disable / enable scenario

- **Stimulus**
  - UART frame writes `0x0000_0000` to CONTROL, followed by an extended idle window (currently 3.6 µs, multiplier = 4) before the next poll.
  - Re-enable via CONTROL write `0x0000_0001`, confirming recovery after a hold period.
  - Optional: Inject status polls and AXI requests during the disabled window to validate gating behaviour.
- **Checks**
  - `verify_control_readback` attempts up to three immediate polls and invokes the extended backoff when truncated payloads persist.
  - `bridge_status_monitor` must report a low transition during the disable window and a high transition after re-enable.
  - Scoreboard must treat disable acknowledgements as expected (no mismatches).
- **Coverage instrumentation**
  - Toggle bins for `bridge_enable`, AXI handshake strobes, and CONTROL register bits.
  - Functional coverpoints (to be implemented) capturing disable window duration categories, response classifications, and concurrent AXI traffic.

### 2.2 CONTROL busy / partial readback scenario

- **Stimulus**
  - Force STATUS_BUSY responses by issuing back-to-back CONTROL operations with minimal spacing.
  - Capture truncated one-byte responses and confirm retries escalate to the extended quiet period.
- **Checks**
  - Final confirmation relies on the bridge monitor; no UVM errors permitted after retries exhaust.
  - Warning-level breadcrumbs retained for investigation (`CONTROL_TRACE`).
- **Coverage instrumentation**
  - Expression bins for busy vs. ok responses.
  - Functional coverage on retry counts and backoff usage.

## 3. Scoreboard expectations

| Condition | Expected behaviour | Severity |
| --- | --- | --- |
| UART status frame observed without AXI counterpart during CONTROL disable | Treat as informational; record in response classification coverage. | `UVM_INFO` |
| CONTROL re-enable returns truncated payload but monitor confirms high transition | Emit `UVM_WARNING` once; rely on monitor confirmation. | `UVM_WARNING` |
| CONTROL re-enable fails to return high transition after retries and extended backoff | Escalate to `UVM_ERROR` and halt sequence. | `UVM_ERROR` |

Scoreboard updates must ensure unmatched-but-expected responses are downgraded from warnings while maintaining strict detection of genuine mismatches.

## 4. Documentation cross-references

- `docs/register_map.md` — incorporate disable semantics, BUSY status timing, and the 3.6 µs quiet-period guidance derived from the CONTROL backoff multiplier.
- `docs/system_architecture.md` — describe bridge_enable gating and monitor correlation.
- `docs/coverage_improvement_checklist_20250928.md` — track progress toward toggle ≥ 80 % and functional ≥ 70 % targets for disable features.
- `docs/diary_20250930.md` — latest execution notes and waveform references.

## 5. Open actions

1. Implement disable stress sequences with parameterised idle durations and interleaved AXI bursts (Phase F of the comprehensive instructions).
2. Extend scoreboard logic to classify UART responses and collect functional coverage bins.
3. Update `docs/register_map.md` with BUSY return semantics and link back to this plan.

<!-- End of verification plan -->
