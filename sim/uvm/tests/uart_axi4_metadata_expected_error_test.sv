`timescale 1ns / 1ps

class uart_axi4_metadata_expected_error_test extends enhanced_uart_axi4_base_test;

    `uvm_component_utils(uart_axi4_metadata_expected_error_test)

    metadata_expected_error_sequence_20251015 error_seq;

    function new(string name = "uart_axi4_metadata_expected_error_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        cfg.enable_coverage = 1;
        cfg.enable_scoreboard = 1;
        cfg.enable_protocol_checking = 1;
        cfg.enable_scoreboard_metadata_logs = 1;
        cfg.enable_driver_runtime_logs = 0;
        cfg.enable_scoreboard_runtime_logs = 0;
        cfg.enable_driver_debug_logs = 0;
    cfg.coverage_warning_threshold = 40.0; // Error-focused stimulus targets limited bins

        uvm_config_db#(uart_axi4_env_config)::set(this, "env", "config", cfg);
        `uvm_info("TEST_METADATA_ERROR_CONFIG", "Metadata expected-error test configured with scoreboard metadata logging", UVM_LOW)
    endfunction

    virtual task main_phase(uvm_phase phase);
        `uvm_info("METADATA_ERROR_TEST", "===============================================", UVM_LOW)
        `uvm_info("METADATA_ERROR_TEST", "  UART-AXI4 METADATA EXPECTED ERROR TEST", UVM_LOW)
        `uvm_info("METADATA_ERROR_TEST", "===============================================", UVM_LOW)

        phase.raise_objection(this, "Metadata expected-error test running");

        wait (uart_axi4_tb_top.dut.rst == 1'b0);
        repeat (10) @(posedge uart_axi4_tb_top.dut.clk);

        `uvm_info("METADATA_ERROR_TEST", "Running metadata expected-error sequence", UVM_MEDIUM)
        error_seq = metadata_expected_error_sequence_20251015::type_id::create("error_seq");
        error_seq.start(env.uart_agt.sequencer);

        repeat (2000) @(posedge uart_axi4_tb_top.dut.clk);
        `uvm_info("METADATA_ERROR_TEST", "Metadata expected-error test completed", UVM_LOW)

        phase.drop_objection(this, "Metadata expected-error test completed");
    endtask

endclass
