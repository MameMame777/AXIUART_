`timescale 1ns / 1ps

class uart_axi4_single_read_test extends enhanced_uart_axi4_base_test;

    `uvm_component_utils(uart_axi4_single_read_test)

    simple_debug_read_sequence_20251015 read_seq;

    function new(string name = "uart_axi4_single_read_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        cfg.enable_coverage = 1;
        cfg.enable_scoreboard = 1;
        cfg.enable_protocol_checking = 1;

        uvm_config_db#(uart_axi4_env_config)::set(this, "env", "config", cfg);
        `uvm_info("TEST_SINGLE_READ_CONFIG", "Single read test configured with scoreboard enabled", UVM_LOW)
    endfunction

    virtual task main_phase(uvm_phase phase);
        `uvm_info("SINGLE_READ_TEST", "===============================================", UVM_LOW)
        `uvm_info("SINGLE_READ_TEST", "     UART-AXI4 SINGLE READ FUNCTIONAL TEST", UVM_LOW)
        `uvm_info("SINGLE_READ_TEST", "===============================================", UVM_LOW)

        phase.raise_objection(this, "Single read test running");

        wait (uart_axi4_tb_top.rst_n == 1'b1);
        repeat (10) @(posedge uart_axi4_tb_top.clk);

        `uvm_info("SINGLE_READ_TEST", "Running single read debug sequence", UVM_MEDIUM)
        read_seq = simple_debug_read_sequence_20251015::type_id::create("read_seq");
        read_seq.start(env.uart_agt.sequencer);

        repeat (2000) @(posedge uart_axi4_tb_top.clk);
        `uvm_info("SINGLE_READ_TEST", "Single read test completed", UVM_LOW)

        phase.drop_objection(this, "Single read test completed");
    endtask

endclass
