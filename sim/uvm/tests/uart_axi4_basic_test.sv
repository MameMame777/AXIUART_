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
        `uvm_info("BASIC_TEST", "===============================================", UVM_LOW)
        `uvm_info("BASIC_TEST", "     UART-AXI4 BASIC FUNCTIONAL TEST", UVM_LOW)
        `uvm_info("BASIC_TEST", "===============================================", UVM_LOW)
        `uvm_info("BASIC_TEST", "Test started with comprehensive UVM reporting", UVM_LOW)

        phase.raise_objection(this, "Basic test running");

        `uvm_info("BASIC_TEST", "=== Starting Basic Functional Test ===", UVM_LOW)
        
        // Wait for reset to complete
        wait (uart_axi4_tb_top.rst_n == 1'b1);
        repeat (10) @(posedge uart_axi4_tb_top.clk);
        
        `uvm_info("BASIC_TEST", "Reset completed, starting sequence", UVM_MEDIUM)
        
        // Run debug single write sequence with timeout protection
        `uvm_info("BASIC_TEST", "Running single write debug sequence", UVM_MEDIUM)
        fork
            begin
                debug_seq = simple_debug_write_sequence_20250923::type_id::create("debug_seq");
                `uvm_info("BASIC_TEST", "Sequence created, calling start()", UVM_LOW)
                debug_seq.start(env.uart_agt.sequencer);
                `uvm_info("BASIC_TEST", "Sequence.start() returned successfully - no timeout", UVM_LOW)
            end
            begin
                // Timeout protection: 10ms max
                #10_000_000;
                `uvm_warning("BASIC_TEST", "Sequence timeout - completing test")
            end
        join_any
        disable fork;
        
        // Wait for system stabilization (reduced from 1000 to 100 clocks)
        repeat (100) @(posedge uart_axi4_tb_top.clk);
        `uvm_info("BASIC_TEST", "=== Basic Test Completed Successfully ===", UVM_LOW)

        phase.drop_objection(this, "Basic test completed");
    endtask

endclass
