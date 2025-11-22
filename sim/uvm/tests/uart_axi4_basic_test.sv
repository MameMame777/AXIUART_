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

    // UVM-compliant run_phase: reset then sequence execution
    // Standard pattern: test controls reset via sequence, then runs functional tests
    virtual task run_phase(uvm_phase phase);
        uart_reset_seq reset_seq;
        uart_debug_simple_write_seq debug_seq;
        
        `uvm_info("BASIC_TEST", "===============================================", UVM_LOW)
        `uvm_info("BASIC_TEST", "     UART-AXI4 BASIC FUNCTIONAL TEST", UVM_LOW)
        `uvm_info("BASIC_TEST", "===============================================", UVM_LOW)
        
        // Validate environment was built correctly
        if (env == null || env.uart_agt == null || env.uart_agt.sequencer == null) begin
            `uvm_fatal("BASIC_TEST", "Environment not built correctly - sequencer unavailable")
        end
        
        // ========================================================================
        // STEP 1: Execute DUT reset via interface (UVM standard pattern)
        // ========================================================================
        phase.raise_objection(this, "Executing DUT reset");
        
        reset_seq = uart_reset_seq::type_id::create("reset_seq");
        if (reset_seq == null) begin
            `uvm_fatal("BASIC_TEST", "Failed to create reset sequence")
        end
        
        // Set virtual interface for reset sequence
        if (!uvm_config_db#(virtual uart_if)::get(this, "", "vif", reset_seq.vif)) begin
            `uvm_fatal("BASIC_TEST", "Failed to get virtual interface for reset sequence")
        end
        
        `uvm_info("BASIC_TEST", "Executing DUT reset sequence", UVM_MEDIUM)
        reset_seq.start(null);  // Reset doesn't need sequencer
        
        phase.drop_objection(this, "DUT reset completed");
        
        // ========================================================================
        // STEP 2: Execute functional test sequences
        // ========================================================================
        
        // Create sequence using correct class name
        debug_seq = uart_debug_simple_write_seq::type_id::create("debug_seq");
        if (debug_seq == null) begin
            `uvm_fatal("BASIC_TEST", "Failed to create debug sequence")
        end
        
        `uvm_info("BASIC_TEST", "Starting debug write sequence", UVM_MEDIUM)
        
        // Set starting_phase so sequence can manage objections (UVM standard pattern)
        debug_seq.starting_phase = phase;
        
        // Start sequence - this is a blocking call that returns when sequence completes
        debug_seq.start(env.uart_agt.sequencer);
        
        `uvm_info("BASIC_TEST", "Sequence completed successfully", UVM_LOW)
        `uvm_info("BASIC_TEST", "===============================================", UVM_LOW)
    endtask

endclass
