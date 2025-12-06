`timescale 1ns / 1ps

class uart_axi4_basic_test extends enhanced_uart_axi4_base_test;

    // UVM factory registration macro
    `uvm_component_utils(uart_axi4_basic_test)
    
    // Test sequence handles - using correct class name from debug_sequences.sv
    uart_debug_simple_write_seq debug_seq;
    bit basic_verbose_mode = 1'b0;
    string verbose_plusarg_name = "UART_BASIC_VERBOSE";
    
    // Sequence completion flag (class member for thread-safe sharing between run_phase and run_primary_sequence)
    protected bit sequence_completed;

    // Constructor
    function new(string name = "uart_axi4_basic_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Build phase - configure test environment
    virtual function void build_phase(uvm_phase phase);
        string verbose_arg_pattern;
        string verbose_arg_matches[$];

        super.build_phase(phase);
        // Note: uart_vif, bridge_status_vif, axi_vif are inherited from uart_axi4_base_test

        verbose_arg_pattern = {"+", verbose_plusarg_name};
        basic_verbose_mode = (uvm_cmdline_processor::get_inst().get_arg_matches(verbose_arg_pattern, verbose_arg_matches) > 0);
        
        // Configure test-specific reporting
        configure_test_specific_reporting();
        
        // Configure environment for basic functional testing
        cfg.enable_coverage = 1;
        cfg.enable_scoreboard = 1;
        cfg.enable_protocol_checking = 1;
        cfg.enable_driver_runtime_logs = basic_verbose_mode ? 1'b1 : 1'b0;  // Disable for performance unless verbose mode
        cfg.enable_driver_debug_logs = basic_verbose_mode ? 1'b1 : 1'b0;
        cfg.enable_scoreboard_runtime_logs = basic_verbose_mode;
        cfg.enable_scoreboard_metadata_logs = basic_verbose_mode;
        cfg.driver_runtime_verbosity = UVM_LOW;  // Reduced from UVM_MEDIUM
        cfg.driver_debug_verbosity = UVM_MEDIUM;  // Reduced from UVM_HIGH
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

    // ========================================================================
    // UVM Phase-Based Architecture (IEEE 1800.2 Compliant)
    // ========================================================================
    // run_phase: Execute all time-consuming operations (reset + functional test)
    // This is the ONLY phase where @(posedge clk), #delay, wait are allowed
    // ========================================================================
    
    virtual task run_phase(uvm_phase phase);
        // Do NOT call super.run_phase() as we override completely
        
        begin : run_phase_body
            uart_reset_sequence reset_seq;
            uart_debug_simple_write_seq debug_seq;
            
            `uvm_info("BASIC_TEST", "===============================================", UVM_LOW)
            `uvm_info("BASIC_TEST", "     UART-AXI4 BASIC FUNCTIONAL TEST", UVM_LOW)
            `uvm_info("BASIC_TEST", "===============================================", UVM_LOW)
        
        // Validate environment was built correctly
        if (env == null || env.uart_agt == null || env.uart_agt.sequencer == null) begin
            `uvm_fatal("BASIC_TEST", "Environment not built correctly - sequencer unavailable")
        end
        
        // ★★★ CRITICAL: Raise objection BEFORE any clock-dependent operations
        phase.raise_objection(this, "Executing reset and functional test");
        
        // ★★★ UBUS PATTERN: Wait for clock stabilization after objection
        // At time 0, clocking blocks are not yet initialized - must synchronize to clock edge
        repeat (2) @(posedge env.uart_agt.driver.vif.clk);
        
        // Step 1: Reset DUT
        `uvm_info("BASIC_TEST", "Executing DUT reset (driver-controlled sequence)", UVM_MEDIUM)
        reset_seq = uart_reset_sequence::type_id::create("reset_seq");
        reset_seq.reset_cycles = 100;
        reset_seq.start(env.uart_agt.sequencer);
        `uvm_info("BASIC_TEST", "Reset completed", UVM_MEDIUM)
        
        // Step 2: Functional test
        `uvm_info("BASIC_TEST", "Starting functional test", UVM_MEDIUM)
        
        // Create sequence using correct class name
        debug_seq = uart_debug_simple_write_seq::type_id::create("debug_seq");
        if (debug_seq == null) begin
            `uvm_fatal("BASIC_TEST", "Failed to create debug sequence")
        end
        
        // DIAGNOSTIC: Check sequencer handle before start()
        if (env == null) `uvm_fatal("BASIC_TEST", "env is null")
        if (env.uart_agt == null) `uvm_fatal("BASIC_TEST", "env.uart_agt is null")
        if (env.uart_agt.sequencer == null) begin
            `uvm_error("BASIC_TEST", $sformatf("sequencer is NULL! env.uart_agt=%0p", env.uart_agt))
        end else begin
            `uvm_info("BASIC_TEST", $sformatf("[OK] Sequencer found: %s (type=%s)",
                         env.uart_agt.sequencer.get_full_name(),
                         env.uart_agt.sequencer.get_type_name()), UVM_LOW)
        end
        
        `uvm_info("BASIC_TEST", "Starting debug write sequence", UVM_MEDIUM)
        
        // Start sequence
        debug_seq.start(env.uart_agt.sequencer);
        
        `uvm_info("BASIC_TEST", "Sequence completed successfully", UVM_LOW)
        `uvm_info("BASIC_TEST", "===============================================", UVM_LOW)
        
        // Drop objection after all sequences complete
        phase.drop_objection(this, "All test sequences completed");
        end : run_phase_body
    endtask

endclass