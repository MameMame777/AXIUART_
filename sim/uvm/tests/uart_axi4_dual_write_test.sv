`timescale 1ns / 1ps

class uart_axi4_dual_write_test extends enhanced_uart_axi4_base_test;

    `uvm_component_utils(uart_axi4_dual_write_test)

    simple_dual_write_sequence_20251015 dual_seq;

    function new(string name = "uart_axi4_dual_write_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        cfg.enable_coverage = 1;
        cfg.enable_scoreboard = 1;
        cfg.enable_protocol_checking = 1;
        cfg.enable_driver_debug_logs = 0;
        cfg.enable_driver_runtime_logs = 0;
        cfg.enable_scoreboard_runtime_logs = 0;
        cfg.driver_runtime_verbosity = UVM_LOW;
        cfg.scoreboard_runtime_verbosity = UVM_LOW;
        cfg.enable_scoreboard_metadata_logs = 1;
    cfg.coverage_warning_threshold = 30.0; // Align threshold with achievable dual-write coverage footprint

        uvm_config_db#(uart_axi4_env_config)::set(this, "env", "config", cfg);
        `uvm_info("TEST_DUAL_WRITE_CONFIG", "Dual write test configured with scoreboard enabled", UVM_LOW)
    endfunction

    virtual task main_phase(uvm_phase phase);
        `uvm_info("DUAL_WRITE_TEST", "===============================================", UVM_LOW)
        `uvm_info("DUAL_WRITE_TEST", "     UART-AXI4 DUAL WRITE FUNCTIONAL TEST", UVM_LOW)
        `uvm_info("DUAL_WRITE_TEST", "===============================================", UVM_LOW)

        phase.raise_objection(this, "Dual write test running");

        wait (uart_axi4_tb_top.dut.rst == 1'b0);
        repeat (10) @(posedge uart_axi4_tb_top.dut.clk);

        `uvm_info("DUAL_WRITE_TEST", "Running dual write debug sequence", UVM_MEDIUM)
        dual_seq = simple_dual_write_sequence_20251015::type_id::create("dual_seq");
        dual_seq.start(env.uart_agt.sequencer);

        repeat (2000) @(posedge uart_axi4_tb_top.dut.clk);
        `uvm_info("DUAL_WRITE_TEST", "Dual write test completed", UVM_LOW)

        phase.drop_objection(this, "Dual write test completed");
    endtask

endclass
