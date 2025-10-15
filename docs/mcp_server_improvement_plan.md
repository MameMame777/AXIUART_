# MCP Server Improvement Plan

## Context

- Workspace: AXIUART_
- Current MCP implementation: `mcp_server/dsim_uvm_server.py` (FastMCP 2.12.4)
- Reference specification: `mcp_server/mcp_add_debug.md`
- Status: MCP server and DSIM integration operational; verification features remain minimal.

## Verified Baseline

- ✅ MCP client/server communication via stdio.
- ✅ DSIM compile/run executed successfully through `run_uvm_simulation`.
- ✅ Environment diagnostics available (`check_dsim_environment`).
- ✅ DSIM log rotation implemented (limit 50 files).

## Capability Gaps

1. **Missing Log Intelligence**
   - No automated parsing for UVM severities, assertions, or runtime stats.
   - Error detection relies on manual log inspection; UVM_ERRORS do not flip MCP status.

2. **Regression Support Deficit**
   - No mechanism to cache last failing test, re-run on demand, or summarise outcomes.
   - Results returned as raw log text; lacks structured JSON for dashboards.

3. **Coverage & Waveform Controls**
   - Coverage and waveform generation require manual command-line flags.
   - No API to report coverage metrics or produced waveform files.

4. **Parameter Validation & Safety**
   - DSIM arguments (`verbosity`, `mode`, `timeout`, etc.) are unchecked.
   - Workspace/log paths are not exposed in responses, complicating automation.

5. **Documentation Gap**
   - README lacks a feature matrix, usage examples, or roadmap alignment with `mcp_add_debug.md`.

## Proposed Enhancements (Phase Alignment)

| Priority | Feature | Reference Phase | Notes |
|----------|---------|-----------------|-------|
| High | `analyze_uvm_log(log_path)` | Phase 2.1 | Parse INFO/ERROR/FATAL counts, per-component breakdown. |
| High | `summarize_test_result(log_path)` | Phase 2.2 | Extract test name, seed, runtime, severity counts; return concise summary. |
| High | UVM error detection in `run_uvm_simulation` | — | Mark MCP response as failure if log contains UVM_ERROR/ASSERTION FAIL. |
| Medium | `report_assertion_summary(log_path)` | Phase 2.4 | Collect assertion failures for quick diagnosis. |
| Medium | `rerun_last_failed_test()` | Phase 2.3 | Persist failing test parameters to `.last_failed.json`. |
| Medium | API options for `waves` / `coverage` with result paths | — | Include generated file locations in response payload. |
| Low | `grep_uvm_error(pattern)` | Phase 2.5 | Async search using `aiofiles`. |
| Low | README update + feature checklist | — | Ensure onboarding clarity, capture roadmap linkage. |

## Progress Update – 2025-10-15

- Phase 2.1/2.2 delivered: `tools/utils.py` parses DSIM logs, summarises results, and captures assertion statistics.
- `run_uvm_simulation` now emits structured JSON, flips status on UVM errors/assertions, and attaches warning/assertion excerpts.
- Added `analyze_uvm_log` MCP tool with configurable list limits and workspace-relative path resolution for standalone analytics.
- Assertion summaries surfaced across simulation responses and log-analysis payloads to support dashboards.

## Implementation Notes

- All new tools should follow FastMCP `@mcp.tool()` pattern and return JSON/dict structures.
- Encapsulate log parsing regex helpers inside `mcp_server/tools/utils.py` (new module).
- Centralise DSIM command construction; add parameter validation (modes, verbosity enums, timeout bounds).
- Extend `run_uvm_simulation` response schema:

  ```json
  {
    "status": "success" | "failure",
    "log_file": "sim/exec/logs/<file>.log",
    "summary": { ... },
    "details": "<truncated text>",
    "warnings": [ ... ]
  }
  ```

- Document configuration and workflows in README + this plan after each milestone.

## Next Actions

1. Document the new JSON response schema and `analyze_uvm_log` workflow in README and quick-start guides.
2. Implement regression support via `rerun_last_failed_test` and persist structured artifacts for triage.
3. Extend waveform/coverage reporting with explicit output paths and summary metrics.
4. Prototype targeted log search (`grep_uvm_error`) using async IO after regression tooling stabilises.

---

Last updated: 2025-10-15
