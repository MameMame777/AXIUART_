`timescale 1ns / 1ps

class uart_axi4_basic_test extends enhanced_uart_axi4_base_test;

    // UVM factory registration macro
    `uvm_component_utils(uart_axi4_basic_test)
    
    // Test sequence handles
    simple_debug_write_sequence_20250923 debug_seq;
    bit basic_verbose_mode = 1'b0;
    string verbose_plusarg_name = "UART_BASIC_VERBOSE";

    // Constructor
    function new(string name = "uart_axi4_basic_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Build phase - configure test environment
    virtual function void build_phase(uvm_phase phase);
        string verbose_arg_pattern;
        string verbose_arg_matches[$];

        super.build_phase(phase);

        verbose_arg_pattern = {"+", verbose_plusarg_name};
        basic_verbose_mode = (uvm_cmdline_processor::get_inst().get_arg_matches(verbose_arg_pattern, verbose_arg_matches) > 0);
        
        // Configure test-specific reporting
        configure_test_specific_reporting();
        
        // Configure environment for basic functional testing
        cfg.enable_coverage = 1;
        cfg.enable_scoreboard = 1;
        cfg.enable_protocol_checking = 1;
        cfg.enable_driver_runtime_logs = 1'b1;  // Force driver visibility during hang debug
        cfg.enable_driver_debug_logs = 1'b1;
        cfg.enable_scoreboard_runtime_logs = basic_verbose_mode;
        cfg.enable_scoreboard_metadata_logs = basic_verbose_mode;
        cfg.driver_runtime_verbosity = UVM_MEDIUM;
        cfg.driver_debug_verbosity = UVM_HIGH;
        cfg.scoreboard_runtime_verbosity = basic_verbose_mode ? UVM_MEDIUM : UVM_LOW;
    // Keep the driver watchdog comfortably above the longest UART frame (8 bytes @115.2kbaud ~0.7ms)
        cfg.frame_timeout_ns = cfg.byte_time_ns * 32;
        
        uvm_config_db#(uart_axi4_env_config)::set(this, "env", "config", cfg);
        if (basic_verbose_mode) begin
            `uvm_info("TEST_BASIC_CONFIG", "UART_BASIC_VERBOSE plusarg detected; retaining debug reporting", UVM_LOW)
        end else begin
            `uvm_info("TEST_BASIC_CONFIG", "Runtime debug reporting disabled for performance (set +UART_BASIC_VERBOSE to re-enable)", UVM_LOW)
        end
    endfunction
    
    // Test-specific reporting configuration
    virtual function void configure_test_specific_reporting();
        // Configure test-specific IDs
        this.set_report_id_verbosity_hier("TEST_BASIC_START", UVM_HIGH);
        this.set_report_id_verbosity_hier("TEST_BASIC_SEQ", UVM_MEDIUM);
        this.set_report_id_verbosity_hier("TEST_BASIC_COMPLETE", UVM_MEDIUM);
        this.set_report_id_verbosity_hier("TEST_BASIC_CONFIG", UVM_LOW);

        if (!basic_verbose_mode) begin
            this.set_report_id_verbosity_hier("DEBUG_SEQ*", UVM_NONE);
            this.set_report_id_verbosity_hier("UART_DRIVER_HANDSHAKE", UVM_NONE);
            this.set_report_id_verbosity_hier("UART_DRIVER_DEBUG", UVM_NONE);
            this.set_report_id_verbosity_hier("UART_DRIVER", UVM_LOW);
            this.set_report_id_verbosity_hier("BASIC_TEST_LOOP", UVM_NONE);
            this.set_report_id_verbosity_hier("BASIC_TEST_WAIT", UVM_NONE);
            this.set_report_id_verbosity_hier("OBJECTION_DEBUG", UVM_NONE);
        end
    endfunction

    // Primary stimulus hook; derived tests can override to supply custom sequences.
    // Default implementation executes the legacy single-write debug sequence.
    protected virtual task run_primary_sequence(output bit sequence_completed);
        `uvm_info("BASIC_TEST", "Running single write debug sequence", UVM_MEDIUM)

        debug_seq = simple_debug_write_sequence_20250923::type_id::create("debug_seq");
        if (debug_seq == null) begin
            `uvm_fatal("BASIC_TEST", "Failed to create debug sequence")
        end

        `uvm_info("BASIC_TEST_SEQ", "Calling debug_seq.start()", UVM_HIGH)
        debug_seq.start(env.uart_agt.sequencer);
        sequence_completed = 1;
        `uvm_info("BASIC_TEST", "Sequence.start() returned successfully - no timeout", UVM_LOW)
    endtask

    // Override run_phase instead of main_phase to avoid phase conflicts
    virtual task run_phase(uvm_phase phase);
    bit sequence_completed;
    bit axi_done_seen;
    bit builder_done_seen;
    time seq_timeout_ns;
    time poll_interval_ns;
    time handshake_timeout_ns;
    time handshake_deadline;
    time timeout_deadline;
    time next_status_log;
    int objection_total;
    int objection_local;
    uvm_objection run_phase_objection;

        `uvm_info("BASIC_TEST", "===============================================", UVM_LOW)
        `uvm_info("BASIC_TEST", "     UART-AXI4 BASIC FUNCTIONAL TEST", UVM_LOW)
        `uvm_info("BASIC_TEST", "===============================================", UVM_LOW)
        `uvm_info("BASIC_TEST", "Test started with comprehensive UVM reporting", UVM_LOW)

    phase.raise_objection(this, "Basic test running");
    run_phase_objection = phase.get_objection();

        // Print UVM topology and the active phase for immediate hierarchy visibility
        if (basic_verbose_mode) begin
            uvm_top.print_topology();
        end
        `uvm_info("BASIC_TEST", $sformatf("Phase: %s", phase.get_name()), UVM_LOW)
        `uvm_info("BASIC_TEST", "=== Starting Basic Functional Test ===", UVM_LOW)

        // Wait for reset to complete and let the DUT exit reset
        wait (uart_axi4_tb_top.rst_n == 1'b1);
        repeat (10) @(posedge uart_axi4_tb_top.clk);

        `uvm_info("BASIC_TEST", "Reset completed, starting sequence", UVM_MEDIUM)

        if (env == null || env.uart_agt == null || env.uart_agt.sequencer == null) begin
            phase.drop_objection(this, "Environment is not ready for sequence start");
            `uvm_fatal("BASIC_TEST_ENV",
                "Environment hierarchy missing (env/uart_agt/sequencer). Aborting test before sequence start")
        end

        `uvm_info("BASIC_TEST_CFG",
            $sformatf("frame_timeout_ns=%0d byte_time_ns=%0d", cfg.frame_timeout_ns, cfg.byte_time_ns), UVM_LOW)

        // Run debug single write sequence with timeout protection (no forced thread kill)
        sequence_completed = 0;

        if (cfg.frame_timeout_ns > 0) begin
            seq_timeout_ns = cfg.frame_timeout_ns * 4; // Allow margin above driver frame timeout
        end else begin
            seq_timeout_ns = 4_000_000; // Default to 4us if configuration missing
        end

        if (cfg.byte_time_ns > 0) begin
            poll_interval_ns = cfg.byte_time_ns;
        end else begin
            poll_interval_ns = 1_000;
        end

        if (seq_timeout_ns > 16 && poll_interval_ns > seq_timeout_ns / 16) begin
            poll_interval_ns = seq_timeout_ns / 16;
        end

        if (seq_timeout_ns > 0) begin
            handshake_timeout_ns = seq_timeout_ns;
        end else begin
            handshake_timeout_ns = 4_000_000;
        end

        `uvm_info("BASIC_TEST_CFG",
            $sformatf("frame_timeout_ns=%0d byte_time_ns=%0d poll_interval_ns=%0d seq_timeout_ns=%0d handshake_timeout_ns=%0d",
                cfg.frame_timeout_ns, cfg.byte_time_ns, poll_interval_ns, seq_timeout_ns, handshake_timeout_ns), UVM_LOW)

        `uvm_info("BASIC_TEST_SEQ", "About to fork primary test sequence thread", UVM_LOW)
        fork : primary_sequence_execution
            begin
                run_primary_sequence(sequence_completed);
            end
        join_none

        axi_done_seen = 0;
        builder_done_seen = 0;

        fork : handshake_monitors
            begin : monitor_axi_transaction_done
                wait (uart_axi4_tb_top.rst_n == 1'b1);
                @(posedge uart_axi4_tb_top.dut.uart_bridge_inst.axi_transaction_done);
                axi_done_seen = 1;
                if (basic_verbose_mode) begin
                    `uvm_info("BASIC_TEST_HANDSHAKE",
                        $sformatf("Detected axi_transaction_done at time=%0t", $time), UVM_HIGH)
                end
            end
            begin : monitor_builder_response_complete
                wait (uart_axi4_tb_top.rst_n == 1'b1);
                @(posedge uart_axi4_tb_top.dut.uart_bridge_inst.builder_response_complete);
                builder_done_seen = 1;
                if (basic_verbose_mode) begin
                    `uvm_info("BASIC_TEST_HANDSHAKE",
                        $sformatf("Detected builder_response_complete at time=%0t", $time), UVM_HIGH)
                end
            end
            begin : handshake_timeout_guard
                wait (uart_axi4_tb_top.rst_n == 1'b1);
                @(posedge uart_axi4_tb_top.dut.uart_bridge_inst.axi_start_transaction);
                handshake_deadline = $time + handshake_timeout_ns;
                forever begin
                    if (axi_done_seen && builder_done_seen) begin
                        disable handshake_timeout_guard;
                    end
                    if ($time >= handshake_deadline) begin
                        string missing_signals;
                        if (!axi_done_seen && !builder_done_seen) begin
                            missing_signals = "axi_transaction_done and builder_response_complete";
                        end else if (!axi_done_seen) begin
                            missing_signals = "axi_transaction_done";
                        end else begin
                            missing_signals = "builder_response_complete";
                        end
                        if (run_phase_objection != null) begin
                            run_phase_objection.display_objections();
                        end
                        phase.drop_objection(this, "Bridge handshake timeout");
                        `uvm_fatal("BASIC_TEST_HANDSHAKE_TIMEOUT",
                            $sformatf("No %s observed by %0t (timeout=%0dns) while monitoring bridge handshakes",
                                missing_signals, handshake_deadline, handshake_timeout_ns))
                    end
                    #(poll_interval_ns);
                end
            end
        join_none

        if (basic_verbose_mode) begin
            fork : verbose_handshake_assertions
                begin : handshake_order_assertion
                    bit handshake_active;
                    bit seen_axi_start;
                    bit seen_axi_done;
                    bit seen_builder_done;
                    bit prev_axi_start;
                    bit prev_axi_done;
                    bit prev_builder_done;
                    bit prev_parser_consumed;
                    bit prev_parser_error;

                    forever begin
                        @(posedge uart_axi4_tb_top.clk);
                        if (uart_axi4_tb_top.rst) begin
                            handshake_active = 0;
                            seen_axi_start = 0;
                            seen_axi_done = 0;
                            seen_builder_done = 0;
                            prev_axi_start = 0;
                            prev_axi_done = 0;
                            prev_builder_done = 0;
                            prev_parser_consumed = 0;
                            prev_parser_error = 0;
                        end else begin
                            bit axi_start_now = uart_axi4_tb_top.dut.uart_bridge_inst.axi_start_transaction;
                            bit axi_done_now = uart_axi4_tb_top.dut.uart_bridge_inst.axi_transaction_done;
                            bit builder_done_now = uart_axi4_tb_top.dut.uart_bridge_inst.builder_response_complete;
                            bit parser_consumed_now = uart_axi4_tb_top.dut.uart_bridge_inst.parser_frame_consumed;
                            bit parser_error_now = uart_axi4_tb_top.dut.uart_bridge_inst.parser_frame_error;

                            bit axi_start_rise = axi_start_now && !prev_axi_start;
                            bit axi_done_rise = axi_done_now && !prev_axi_done;
                            bit builder_done_rise = builder_done_now && !prev_builder_done;
                            bit parser_consumed_rise = parser_consumed_now && !prev_parser_consumed;
                            bit parser_error_rise = parser_error_now && !prev_parser_error;

                            if (axi_start_rise) begin
                                if (handshake_active) begin
                                    `uvm_error("BASIC_VERBOSE_ASSERT",
                                        "axi_start_transaction asserted while a prior handshake is still active")
                                end
                                handshake_active = 1;
                                seen_axi_start = 1;
                                seen_axi_done = 0;
                                seen_builder_done = 0;
                            end

                            if (axi_done_rise) begin
                                if (!(handshake_active && seen_axi_start)) begin
                                    `uvm_error("BASIC_VERBOSE_ASSERT",
                                        "axi_transaction_done observed without a preceding axi_start_transaction")
                                end
                                seen_axi_done = 1;
                            end

                            if (builder_done_rise) begin
                                if (!(handshake_active && seen_axi_done)) begin
                                    `uvm_error("BASIC_VERBOSE_ASSERT",
                                        "builder_response_complete observed before axi_transaction_done")
                                end
                                seen_builder_done = 1;
                            end

                            if (parser_consumed_rise) begin
                                if (!handshake_active) begin
                                    `uvm_error("BASIC_VERBOSE_ASSERT",
                                        "parser_frame_consumed asserted without an active handshake")
                                end
                                if (!seen_builder_done) begin
                                    `uvm_error("BASIC_VERBOSE_ASSERT",
                                        "parser_frame_consumed asserted before builder_response_complete")
                                end
                                handshake_active = 0;
                                seen_axi_start = 0;
                                seen_axi_done = 0;
                                seen_builder_done = 0;
                            end

                            if (parser_error_rise) begin
                                handshake_active = 0;
                                seen_axi_start = 0;
                                seen_axi_done = 0;
                                seen_builder_done = 0;
                            end

                            prev_axi_start = axi_start_now;
                            prev_axi_done = axi_done_now;
                            prev_builder_done = builder_done_now;
                            prev_parser_consumed = parser_consumed_now;
                            prev_parser_error = parser_error_now;
                        end
                    end
                end
            join_none
        end

        timeout_deadline = $time + seq_timeout_ns;
        next_status_log = $time + (poll_interval_ns << 3);

        // Monitor completion without cancelling the executing thread to respect sequencer handshakes
        while (!sequence_completed) begin
            if (basic_verbose_mode) begin
                // Loop trace to prove the monitoring thread remains active.
                `uvm_info("BASIC_TEST_LOOP",
                    $sformatf("Polling sequence completion at time=%0t (deadline=%0t)", $time, timeout_deadline),
                    UVM_LOW)
            end
            if ($time >= timeout_deadline) begin
                if (run_phase_objection != null) begin
                    run_phase_objection.display_objections();
                end
                phase.drop_objection(this, "Basic test aborted due to timeout");
                `uvm_fatal("BASIC_TEST_TIMEOUT",
                    $sformatf("Sequence did not complete within %0dns (frame timeout basis)", seq_timeout_ns))
            end

            if (basic_verbose_mode && $time >= next_status_log) begin
                `uvm_info("BASIC_TEST_WAIT",
                    $sformatf("Waiting for sequence completion. time=%0t deadline=%0t", $time, timeout_deadline),
                    UVM_LOW)
                objection_total = (run_phase_objection != null) ? run_phase_objection.get_objection_count() : -1;
                objection_local = (run_phase_objection != null) ? run_phase_objection.get_objection_count(this) : -1;
                `uvm_info("OBJECTION_DEBUG",
                    $sformatf("run_phase objections: total=%0d local=%0d", objection_total, objection_local),
                    UVM_LOW)
                if (env != null && env.uart_agt != null && env.uart_agt.sequencer != null) begin
                    uvm_sequencer_base seq_base;
                    if ($cast(seq_base, env.uart_agt.sequencer)) begin
                        seq_base.print();
                    end else begin
                        `uvm_warning("OBJECTION_DEBUG", "Failed to cast sequencer to uvm_sequencer_base; skipping sequence dump")
                    end
                end
                next_status_log += (poll_interval_ns << 3);
            end

            #(poll_interval_ns);
        end

        disable handshake_monitors;
        if (basic_verbose_mode) begin
            disable verbose_handshake_assertions;
        end
        wait fork;

        // Wait for system stabilization (reduced from 1000 to 100 clocks)
        repeat (100) @(posedge uart_axi4_tb_top.clk);
        `uvm_info("BASIC_TEST", "=== Basic Test Completed Successfully ===", UVM_LOW)

        phase.drop_objection(this, "Basic test completed");
    endtask

endclass
