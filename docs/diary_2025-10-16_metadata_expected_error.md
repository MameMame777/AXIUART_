# 2025-10-16 Metadata Expected Error Test Verification Notes

- Executed `uart_axi4_metadata_expected_error_test` through MCP client with coverage enabled (`UVM_MEDIUM`, seed 1).
- DSIM run passed without UVM errors; collected log at `sim/exec/logs/uart_axi4_metadata_expected_error_test_20251016_053219.log`.
- Observed seven UVM warnings: two factory duplicate notices (expected), four scoreboard metadata mismatch alerts, and one coverage <80% reminder.
- Scoreboard warnings indicate UART error responses (status 0x05) were returned while AXI BRESP remained OK (0), suggesting DUT does not propagate error onto AXI bus; needs design/spec alignment review.
- Coverage summary: total 47.45% (Frame 38.17%, Burst 37.50%, Error 66.67%).
- Confirmed waveform dump generated (`uart_axi4_minimal_test.mxd`); MXD path available for deep-dive if required.
- Next steps: (1) decide whether scoreboard expectations should accept UART-only error signaling or require AXI BRESP error; (2) extend sequences to exercise additional error codes to push coverage above the 80% threshold or formally waive.
