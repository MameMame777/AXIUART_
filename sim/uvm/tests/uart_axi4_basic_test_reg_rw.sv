`timescale 1ns / 1ps

class uart_axi4_basic_test_reg_rw extends uart_axi4_basic_test;

    `uvm_component_utils(uart_axi4_basic_test_reg_rw)

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        if (cfg.byte_time_ns > 0) begin
            cfg.frame_timeout_ns = cfg.byte_time_ns * 512;
        end else begin
            cfg.frame_timeout_ns = 2_000_000; // Fallback guard when byte time is unavailable
        end

        `uvm_info("BASIC_TEST_REG_RW_CFG",
            $sformatf("Extended frame_timeout_ns=%0d for multi-pattern register sweep", cfg.frame_timeout_ns),
            UVM_LOW)
    endfunction

    function new(string name = "uart_axi4_basic_test_reg_rw", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    protected virtual task run_primary_sequence(output bit sequence_completed);
        test_reg_rw_sequence seq;

        if (env == null || env.uart_agt == null || env.uart_agt.sequencer == null) begin
            `uvm_fatal("BASIC_TEST_REG_RW", "UART agent sequencer unavailable for TEST_REG access")
        end

        seq = test_reg_rw_sequence::type_id::create("test_reg_rw_seq");
        if (seq == null) begin
            `uvm_fatal("BASIC_TEST_REG_RW", "Failed to create test_reg_rw_sequence instance")
        end

        `uvm_info("BASIC_TEST_REG_RW", "Starting TEST_REG read/write validation sequence", UVM_LOW)
        seq.start(env.uart_agt.sequencer);
        `uvm_info("BASIC_TEST_REG_RW", "TEST_REG read/write validation sequence completed", UVM_LOW)
        sequence_completed = 1;
    endtask

endclass
