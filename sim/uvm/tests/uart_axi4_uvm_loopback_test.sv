`timescale 1ns / 1ps

class uart_axi4_uvm_loopback_test extends enhanced_uart_axi4_base_test;

    `uvm_component_utils(uart_axi4_uvm_loopback_test)

    function new(string name = "uart_axi4_uvm_loopback_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void configure_test();
        super.configure_test();

        cfg.enable_uvm_loopback_mode = 1'b1;
        cfg.loopback_disable_scoreboard = 1'b1;
        cfg.loopback_disable_coverage = 1'b1;
        cfg.loopback_disable_axi_monitor = 1'b1;
        cfg.enable_scoreboard = 1'b0;
        cfg.enable_coverage = 1'b0;
        cfg.enable_axi_monitor = 1'b0;
        cfg.enable_system_status_monitoring = 1'b0;
    cfg.enable_correlation = 1'b0;
    cfg.enable_protocol_checking = 1'b0;
        cfg.enable_driver_runtime_logs = 1'b1;
        cfg.enable_driver_debug_logs = 1'b1;
        cfg.driver_runtime_verbosity = UVM_LOW;
        cfg.driver_debug_verbosity = UVM_MEDIUM;

        begin
            bit tb_loopback_from_tb;
            if (!uvm_config_db#(bit)::get(this, "", "tb_loopback_mode", tb_loopback_from_tb)) begin
                tb_loopback_from_tb = 1'b0;
            end

            if (!tb_loopback_from_tb) begin
                `uvm_fatal("LOOPBACK_CFG", "+UVM_LOOPBACK=1 must be supplied when running uart_axi4_uvm_loopback_test to enable testbench overrides")
            end
        end

        begin
            uvm_cmdline_processor cmdp;
            string arg_matches[$];
            cmdp = uvm_cmdline_processor::get_inst();

            if (cmdp.get_arg_matches("+LOOPBACK_ENABLE_SCOREBOARD", arg_matches) > 0) begin
                cfg.loopback_disable_scoreboard = 1'b0;
                cfg.enable_scoreboard = 1'b1;
                cfg.enable_correlation = 1'b1;
                `uvm_info("LOOPBACK_CFG", "Scoreboard re-enabled for loopback run", UVM_LOW)
            end

            arg_matches = {};
            if (cmdp.get_arg_matches("+LOOPBACK_ENABLE_COVERAGE", arg_matches) > 0) begin
                cfg.loopback_disable_coverage = 1'b0;
                cfg.enable_coverage = 1'b1;
                `uvm_info("LOOPBACK_CFG", "Coverage collection re-enabled for loopback run", UVM_LOW)
            end

            arg_matches = {};
            if (cmdp.get_arg_matches("+LOOPBACK_ENABLE_AXI_MONITOR", arg_matches) > 0) begin
                cfg.loopback_disable_axi_monitor = 1'b0;
                cfg.enable_axi_monitor = 1'b1;
                `uvm_info("LOOPBACK_CFG", "AXI monitor re-enabled for loopback run", UVM_LOW)
            end
        end

        `uvm_info("LOOPBACK_CFG", "Configured UVM-only loopback mode", UVM_LOW)
    endfunction

    virtual task run_phase(uvm_phase phase);
    simple_debug_write_sequence_20250923 single_seq;

        phase.raise_objection(this, "uart_axi4_uvm_loopback_test run");

    single_seq = simple_debug_write_sequence_20250923::type_id::create("single_seq");
        if (single_seq == null) begin
            `uvm_fatal("LOOPBACK_SEQ", "Failed to create debug_single_write_sequence")
        end

        `uvm_info("LOOPBACK_TEST", "Starting debug_single_write_sequence in loopback mode", UVM_LOW)
        single_seq.start(env.uart_agt.sequencer);

        // Allow additional time for synthesized responses to propagate
        repeat (200) @(posedge uart_axi4_tb_top.clk);

        phase.drop_objection(this, "uart_axi4_uvm_loopback_test run");
    endtask

endclass
