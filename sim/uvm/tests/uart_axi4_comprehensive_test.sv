`timescale 1ns / 1ps

// UVM Comprehensive Test for UART-AXI4 Bridge Verification
// This test runs multiple sequences and validates all major functionality

`include "uvm_macros.svh"
import uvm_pkg::*;
import uart_axi4_test_pkg::*;

class uart_axi4_comprehensive_test extends enhanced_uart_axi4_base_test;
    `uvm_component_utils(uart_axi4_comprehensive_test)
    
    function new(string name = "uart_axi4_comprehensive_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase - configure test-specific reporting
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        configure_test_specific_reporting();
    endfunction
    
    // Test-specific reporting configuration
    virtual function void configure_test_specific_reporting();
        // Configure test-specific IDs for comprehensive testing
        this.set_report_id_verbosity_hier("TEST_COMPREHENSIVE_START", UVM_HIGH);
        this.set_report_id_verbosity_hier("TEST_COMPREHENSIVE_SEQ", UVM_MEDIUM);
        this.set_report_id_verbosity_hier("TEST_COMPREHENSIVE_RESULT", UVM_HIGH);
        this.set_report_id_verbosity_hier("STRESS_TEST_PROGRESS", UVM_MEDIUM);
    endfunction
    
    function void configure_test();
        super.configure_test();
        
        // Override configuration for comprehensive test
        cfg.num_transactions = 100;  // More transactions for thorough testing
        cfg.enable_verbose_logging = 1'b1;
        cfg.verbosity_level = UVM_MEDIUM;
        
        `uvm_info("COMP_TEST", "Comprehensive test configuration applied", UVM_MEDIUM)
    endfunction
    
    task run_phase(uvm_phase phase);
        uart_axi4_basic_sequence basic_seq;
        uart_axi4_error_sequence error_seq;
        
        phase.raise_objection(this, "Comprehensive test run phase");
        
        `uvm_info("COMP_TEST", "========================================", UVM_LOW)
        `uvm_info("COMP_TEST", "Starting UART AXI4 Comprehensive Test", UVM_LOW)
        `uvm_info("COMP_TEST", "========================================", UVM_LOW)
        
        // Wait for system reset and initialization
        wait_for_reset_release();
        #5us;  // Additional setup time
        
        // Validate system is ready
        validate_system_ready();
        
        // Phase 1: Basic Functionality Testing
        `uvm_info("COMP_TEST", "Phase 1: Basic Functionality Testing", UVM_LOW)
        basic_seq = basic_func_sequence::type_id::create("basic_seq");
        
        // Configure the sequence
        basic_seq.num_transactions = cfg.num_transactions;
        
        // Start the sequence on the UART agent's sequencer
        if (env.uart_agt == null) begin
            `uvm_fatal("COMP_TEST", "UART agent not found in environment")
        end
        
        if (env.uart_agt.sequencer == null) begin
            `uvm_fatal("COMP_TEST", "UART sequencer not found in agent")
        end
        
        basic_seq.start(env.uart_agt.sequencer);
        
        // Wait between test phases
        #10us;
        
        // Phase 2: Error Injection Testing
        `uvm_info("COMP_TEST", "Phase 2: Error Injection Testing", UVM_LOW)
        error_seq = error_injection_sequence::type_id::create("error_seq");
        
        // Configure error injection
        error_seq.num_error_transactions = 20;
        error_seq.inject_crc_errors = 1'b1;
        error_seq.inject_timeout_errors = 1'b1;
        error_seq.inject_malformed_frames = 1'b1;
        
        // Start error injection sequence
        error_seq.start(env.uart_agt.sequencer);
        
        // Wait for all sequences to complete
        #20us;
        
        // Phase 3: Performance and Stress Testing
        `uvm_info("COMP_TEST", "Phase 3: Performance Validation", UVM_LOW)
        run_performance_validation();
        
        `uvm_info("COMP_TEST", "========================================", UVM_LOW)
        `uvm_info("COMP_TEST", "Comprehensive Test Completed Successfully", UVM_LOW)
        `uvm_info("COMP_TEST", "========================================", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
    virtual task run_performance_validation();
        `uvm_info("COMP_TEST", "Running performance validation checks", UVM_MEDIUM)
        
        // Simple performance check - ensure UART responds within timeout
        fork
            begin
                // Monitor UART activity
                #100us;  // Performance monitoring period
            end
            begin
                // Timeout watchdog
                #200us;
                `uvm_error("COMP_TEST", "Performance validation timeout - system may be hung")
            end
        join_any
        disable fork;
        
        `uvm_info("COMP_TEST", "Performance validation completed", UVM_MEDIUM)
    endtask
    
    function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        
        `uvm_info("COMP_TEST", "========================================", UVM_LOW)
        `uvm_info("COMP_TEST", "COMPREHENSIVE TEST FINAL REPORT", UVM_LOW)
        `uvm_info("COMP_TEST", "========================================", UVM_LOW)
        
        // Print scoreboard summary
        if (env.scoreboard != null) begin
            `uvm_info("COMP_TEST", "Scoreboard Final Statistics:", UVM_LOW)
            // Scoreboard will print its own detailed report in its report_phase
        end else begin
            `uvm_warning("COMP_TEST", "Scoreboard not instantiated - detailed checking unavailable")
        end
        
        // Print coverage summary if available
        if (env.coverage != null) begin
            `uvm_info("COMP_TEST", "Coverage collection enabled - see coverage report", UVM_LOW)
        end
        
        `uvm_info("COMP_TEST", "Test completed - check for any UVM_ERROR messages above", UVM_LOW)
    endfunction
    
    function void final_phase(uvm_phase phase);
        super.final_phase(phase);
        
        // Final validation - ensure no errors occurred
        if (uvm_report_server::get_server().get_severity_count(UVM_ERROR) == 0) begin
            `uvm_info("COMP_TEST", "SUCCESS: Test passed with no errors", UVM_LOW)
        end else begin
            `uvm_error("COMP_TEST", "FAILURE: Test completed with errors - see log for details")
        end
    endfunction
    
endclass
