`timescale 1ns / 1ps

class uart_axi4_basic_test extends enhanced_uart_axi4_base_test;

    // UVM factory registration macro
    `uvm_component_utils(uart_axi4_basic_test)
    
    // Test sequence handles
    simple_debug_write_sequence_20250923 debug_seq;

    // Constructor
    function new(string name = "uart_axi4_basic_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Build phase - configure test environment
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Configure test-specific reporting
        configure_test_specific_reporting();
        
        // Configure environment for basic functional testing
        cfg.enable_coverage = 1;
        cfg.enable_scoreboard = 1;
        cfg.enable_protocol_checking = 1;
        
        uvm_config_db#(uart_axi4_env_config)::set(this, "env", "config", cfg);
        `uvm_info("TEST_BASIC_CONFIG", "Basic functional test configured with enhanced reporting", UVM_LOW)
    endfunction
    
    // Test-specific reporting configuration
    virtual function void configure_test_specific_reporting();
        // Configure test-specific IDs
        this.set_report_id_verbosity_hier("TEST_BASIC_START", UVM_HIGH);
        this.set_report_id_verbosity_hier("TEST_BASIC_SEQ", UVM_MEDIUM);
        this.set_report_id_verbosity_hier("TEST_BASIC_COMPLETE", UVM_MEDIUM);
        this.set_report_id_verbosity_hier("TEST_BASIC_CONFIG", UVM_LOW);
    endfunction

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
        uvm_top.print_topology();
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
        `uvm_info("BASIC_TEST", "Running single write debug sequence", UVM_MEDIUM)
        debug_seq = simple_debug_write_sequence_20250923::type_id::create("debug_seq");
        if (debug_seq == null) begin
            `uvm_fatal("BASIC_TEST", "Failed to create debug sequence")
        end

        `uvm_info("BASIC_TEST", "Sequence handle created; invoking start()", UVM_LOW)
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

        `uvm_info("BASIC_TEST_SEQ", "About to fork debug sequence thread", UVM_LOW)
        fork : debug_sequence_execution
            begin
                `uvm_info("BASIC_TEST_SEQ", "Calling debug_seq.start()", UVM_HIGH)
                debug_seq.start(env.uart_agt.sequencer);
                sequence_completed = 1;
                `uvm_info("BASIC_TEST", "Sequence.start() returned successfully - no timeout", UVM_LOW)
            end
        join_none

        axi_done_seen = 0;
        builder_done_seen = 0;

        fork : handshake_monitors
            begin : monitor_axi_transaction_done
                wait (uart_axi4_tb_top.rst_n == 1'b1);
                @(posedge uart_axi4_tb_top.dut.uart_bridge_inst.axi_transaction_done);
                axi_done_seen = 1;
                `uvm_info("BASIC_TEST_HANDSHAKE",
                    $sformatf("Detected axi_transaction_done at time=%0t", $time), UVM_HIGH)
            end
            begin : monitor_builder_response_complete
                wait (uart_axi4_tb_top.rst_n == 1'b1);
                @(posedge uart_axi4_tb_top.dut.uart_bridge_inst.builder_response_complete);
                builder_done_seen = 1;
                `uvm_info("BASIC_TEST_HANDSHAKE",
                    $sformatf("Detected builder_response_complete at time=%0t", $time), UVM_HIGH)
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

        timeout_deadline = $time + seq_timeout_ns;
        next_status_log = $time + (poll_interval_ns << 3);

        // Monitor completion without cancelling the executing thread to respect sequencer handshakes
        while (!sequence_completed) begin
            // Loop trace to prove the monitoring thread remains active.
            `uvm_info("BASIC_TEST_LOOP",
                $sformatf("Polling sequence completion at time=%0t (deadline=%0t)", $time, timeout_deadline),
                UVM_LOW)
            if ($time >= timeout_deadline) begin
                if (run_phase_objection != null) begin
                    run_phase_objection.display_objections();
                end
                phase.drop_objection(this, "Basic test aborted due to timeout");
                `uvm_fatal("BASIC_TEST_TIMEOUT",
                    $sformatf("Sequence did not complete within %0dns (frame timeout basis)", seq_timeout_ns))
            end

            if ($time >= next_status_log) begin
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
        wait fork;

        // Wait for system stabilization (reduced from 1000 to 100 clocks)
        repeat (100) @(posedge uart_axi4_tb_top.clk);
        `uvm_info("BASIC_TEST", "=== Basic Test Completed Successfully ===", UVM_LOW)

        phase.drop_objection(this, "Basic test completed");
    endtask

endclass
