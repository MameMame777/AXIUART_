`timescale 1ns / 1ps

// Frame Parser Diagnostic Test - Implementation per UVM Reporting Strategy Guidelines
// Purpose: Isolate captured_cmd=0x00 root cause with fixed values
// All report IDs follow hierarchical naming: TEST_FRAME_PARSER_DIAG_*

class frame_parser_diagnostic_test extends enhanced_uart_axi4_base_test;
    `uvm_component_utils(frame_parser_diagnostic_test)

    function new(string name = "frame_parser_diagnostic_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Build phase - configure test-specific reporting
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        configure_test_specific_reporting();
    endfunction

    // Test-specific reporting configuration (hierarchical IDs)
    virtual function void configure_test_specific_reporting();
        // Hierarchical report ID configuration per guidelines
        this.set_report_id_verbosity_hier("TEST_FRAME_PARSER_DIAG_START", UVM_HIGH);
        this.set_report_id_verbosity_hier("TEST_FRAME_PARSER_DIAG_CRC_CHECK", UVM_MEDIUM);
        this.set_report_id_verbosity_hier("TEST_FRAME_PARSER_DIAG_STATE_TRANSITION", UVM_MEDIUM);
        this.set_report_id_verbosity_hier("TEST_FRAME_PARSER_DIAG_RESULT", UVM_HIGH);
        this.set_report_id_verbosity_hier("TEST_FRAME_PARSER_DIAG_SUMMARY", UVM_LOW);
    endfunction

    virtual task run_phase(uvm_phase phase);
        simple_debug_write_sequence_20250923 seq;
        phase.raise_objection(this);
        `uvm_info("TEST_FRAME_PARSER_DIAG_START", "========== FRAME PARSER DIAGNOSTIC TEST START ==========" , UVM_LOW)
        `uvm_info("TEST_FRAME_PARSER_DIAG_START", "Purpose: Isolate captured_cmd=0x00 root cause with fixed values", UVM_LOW)
        // Run diagnostic sequence
        seq = simple_debug_write_sequence_20250923::type_id::create("diagnostic_seq");
        `uvm_info("TEST_FRAME_PARSER_DIAG_CRC_CHECK", "Starting diagnostic sequence with fixed values", UVM_LOW)
        seq.start(env.uart_agt.sequencer);
        `uvm_info("TEST_FRAME_PARSER_DIAG_CRC_CHECK", "Waiting for sequence completion...", UVM_LOW)
        #10000;
        // Output detailed result log
        check_frame_parser_state();
        `uvm_info("TEST_FRAME_PARSER_DIAG_SUMMARY", "========== FRAME PARSER DIAGNOSTIC TEST END ==========" , UVM_LOW)
        phase.drop_objection(this);
    endtask

    // Frame parser state check (to be implemented via testbench interface)
    virtual task check_frame_parser_state();
        `uvm_info("TEST_FRAME_PARSER_DIAG_STATE_TRANSITION", "=== FRAME PARSER STATE DIAGNOSTIC ===", UVM_LOW)
        // TODO: Check via testbench interface
        // - parser_frame_error value
        // - captured_cmd value (expected: 0x01)
        // - parser_error_status value
        // - Frame Parser FSM current state
        `uvm_info("TEST_FRAME_PARSER_DIAG_RESULT", "Frame Parser state check implementation needed in testbench", UVM_LOW)
        `uvm_info("TEST_FRAME_PARSER_DIAG_RESULT", "Expected: captured_cmd=0x01, parser_frame_error=0", UVM_LOW)
        `uvm_info("TEST_FRAME_PARSER_DIAG_RESULT", "Actual values to be read from DUT interface", UVM_LOW)
    endtask
endclass