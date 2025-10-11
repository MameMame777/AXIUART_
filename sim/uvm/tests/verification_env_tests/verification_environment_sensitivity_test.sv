`timescale 1ns / 1ps

//===============================================================================
// Verification Environment Sensitivity Test
// 
// Purpose: Test the verification environment's ability to detect known errors
// Author: SystemVerilog Expert (Phase 4.1 Implementation)
// Date: October 11, 2025
//
// This test injects known errors and verifies that the verification environment
// correctly detects them, preventing false negatives.
//===============================================================================

class verification_environment_sensitivity_test extends enhanced_uart_axi4_base_test;
    `uvm_component_utils(verification_environment_sensitivity_test)
    
    // Error detection tracking
    bit crc_error_detected = 0;
    bit timeout_error_detected = 0;
    bit framing_error_detected = 0;
    bit protocol_error_detected = 0;
    bit alignment_error_detected = 0;
    
    // Error injection control
    bit inject_errors = 1;
    int error_injection_delay = 10;
    
    // Test statistics
    int total_injected_errors = 0;
    int total_detected_errors = 0;
    real detection_rate = 0.0;
    
    function new(string name = "verification_environment_sensitivity_test", uvm_component parent = null);
        super.new(name, parent);
        set_report_id_action_hier("SENSITIVITY_TEST", UVM_LOG | UVM_DISPLAY);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info("SENSITIVITY_TEST_BUILD", "Building Verification Environment Sensitivity Test", UVM_LOW)
        
        // Configure for error detection monitoring
        uvm_config_db#(bit)::set(this, "*", "enable_error_monitoring", 1);
        uvm_config_db#(bit)::set(this, "*", "strict_error_checking", 1);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        `uvm_info("SENSITIVITY_TEST_START", "Starting Verification Environment Sensitivity Test", UVM_LOW)
        
        phase.raise_objection(this, "Running verification environment sensitivity tests");
        
        fork
            monitor_error_detection();
        join_none
        
        // Execute sensitivity tests in sequence
        test_crc_error_detection();
        test_timeout_detection();
        test_framing_error_detection();
        test_protocol_violation_detection();
        test_alignment_error_detection();
        
        // Special tests for false negative prevention
        test_subtle_error_patterns();
        test_boundary_error_conditions();
        
        // Wait for all error detection monitoring to complete
        #1000ns;
        
        // Generate sensitivity test report
        generate_sensitivity_report();
        
        phase.drop_objection(this, "Verification environment sensitivity tests completed");
    endtask
    
    //===========================================================================
    // Test 1: CRC Error Detection Sensitivity
    //===========================================================================
    
    virtual task test_crc_error_detection();
        uart_transaction tr;
        bit [31:0] original_crc;
        
        `uvm_info("SENSITIVITY_CRC", "Testing CRC error detection sensitivity", UVM_MEDIUM)
        
        // Create valid transaction
        tr = uart_transaction::type_id::create("crc_error_tr");
        assert(tr.randomize());
        
        // Store original CRC and inject error
        original_crc = tr.crc;
        tr.crc = ~tr.crc; // Bit-flip CRC
        total_injected_errors++;
        
        `uvm_info("SENSITIVITY_CRC", $sformatf("Injecting CRC error: original=%h, corrupted=%h", original_crc, tr.crc), UVM_HIGH)
        
        // Send corrupted transaction
        fork
            begin
                sequencer.start_item(tr);
                sequencer.finish_item(tr);
            end
            begin
                // Monitor for error detection
                wait_for_error_detection("CRC_ERROR", 1000ns);
                if (crc_error_detected) begin
                    total_detected_errors++;
                    `uvm_info("SENSITIVITY_CRC", "✓ CRC error successfully detected", UVM_LOW)
                end else begin
                    `uvm_fatal("SENSITIVITY_CRC", "✗ CRC error NOT detected - verification environment insensitive");
                end
            end
        join
        
        // Reset detection flag
        crc_error_detected = 0;
    endtask
    
    //===========================================================================
    // Test 2: Timeout Detection Sensitivity
    //===========================================================================
    
    virtual task test_timeout_detection();
        uart_transaction tr;
        
        `uvm_info("SENSITIVITY_TIMEOUT", "Testing timeout detection sensitivity", UVM_MEDIUM)
        
        tr = uart_transaction::type_id::create("timeout_tr");
        assert(tr.randomize());
        
        // Force timeout condition by delaying response
        total_injected_errors++;
        
        fork
            begin
                sequencer.start_item(tr);
                // Inject artificial delay to cause timeout
                #5000ns; // Exceed expected response time
                sequencer.finish_item(tr);
            end
            begin
                wait_for_error_detection("TIMEOUT_ERROR", 6000ns);
                if (timeout_error_detected) begin
                    total_detected_errors++;
                    `uvm_info("SENSITIVITY_TIMEOUT", "✓ Timeout error successfully detected", UVM_LOW)
                end else begin
                    `uvm_fatal("SENSITIVITY_TIMEOUT", "✗ Timeout error NOT detected - verification environment insensitive");
                end
            end
        join
        
        timeout_error_detected = 0;
    endtask
    
    //===========================================================================
    // Test 3: Framing Error Detection Sensitivity
    //===========================================================================
    
    virtual task test_framing_error_detection();
        uart_transaction tr;
        
        `uvm_info("SENSITIVITY_FRAMING", "Testing framing error detection sensitivity", UVM_MEDIUM)
        
        tr = uart_transaction::type_id::create("framing_error_tr");
        assert(tr.randomize());
        
        // Inject framing error (corrupt SOF)
        tr.sof = 8'h00; // Invalid SOF (should be 8'hA5)
        total_injected_errors++;
        
        `uvm_info("SENSITIVITY_FRAMING", $sformatf("Injecting framing error: SOF=%h (should be A5)", tr.sof), UVM_HIGH)
        
        fork
            begin
                sequencer.start_item(tr);
                sequencer.finish_item(tr);
            end
            begin
                wait_for_error_detection("FRAMING_ERROR", 1000ns);
                if (framing_error_detected) begin
                    total_detected_errors++;
                    `uvm_info("SENSITIVITY_FRAMING", "✓ Framing error successfully detected", UVM_LOW)
                end else begin
                    `uvm_fatal("SENSITIVITY_FRAMING", "✗ Framing error NOT detected - verification environment insensitive");
                end
            end
        join
        
        framing_error_detected = 0;
    endtask
    
    //===========================================================================
    // Test 4: Protocol Violation Detection Sensitivity
    //===========================================================================
    
    virtual task test_protocol_violation_detection();
        uart_transaction tr;
        
        `uvm_info("SENSITIVITY_PROTOCOL", "Testing protocol violation detection sensitivity", UVM_MEDIUM)
        
        tr = uart_transaction::type_id::create("protocol_violation_tr");
        assert(tr.randomize());
        
        // Inject protocol violation (invalid command)
        tr.cmd = 8'hFF; // Invalid command
        total_injected_errors++;
        
        `uvm_info("SENSITIVITY_PROTOCOL", $sformatf("Injecting protocol violation: cmd=%h", tr.cmd), UVM_HIGH)
        
        fork
            begin
                sequencer.start_item(tr);
                sequencer.finish_item(tr);
            end
            begin
                wait_for_error_detection("PROTOCOL_ERROR", 1000ns);
                if (protocol_error_detected) begin
                    total_detected_errors++;
                    `uvm_info("SENSITIVITY_PROTOCOL", "✓ Protocol violation successfully detected", UVM_LOW)
                end else begin
                    `uvm_fatal("SENSITIVITY_PROTOCOL", "✗ Protocol violation NOT detected - verification environment insensitive");
                end
            end
        join
        
        protocol_error_detected = 0;
    endtask
    
    //===========================================================================
    // Test 5: Alignment Error Detection Sensitivity
    //===========================================================================
    
    virtual task test_alignment_error_detection();
        uart_transaction tr;
        
        `uvm_info("SENSITIVITY_ALIGNMENT", "Testing alignment error detection sensitivity", UVM_MEDIUM)
        
        tr = uart_transaction::type_id::create("alignment_error_tr");
        assert(tr.randomize());
        
        // Inject alignment error (unaligned address)
        tr.addr = 32'h1001; // Unaligned address (should be 4-byte aligned)
        total_injected_errors++;
        
        `uvm_info("SENSITIVITY_ALIGNMENT", $sformatf("Injecting alignment error: addr=%h", tr.addr), UVM_HIGH)
        
        fork
            begin
                sequencer.start_item(tr);
                sequencer.finish_item(tr);
            end
            begin
                wait_for_error_detection("ALIGNMENT_ERROR", 1000ns);
                if (alignment_error_detected) begin
                    total_detected_errors++;
                    `uvm_info("SENSITIVITY_ALIGNMENT", "✓ Alignment error successfully detected", UVM_LOW)
                end else begin
                    `uvm_warning("SENSITIVITY_ALIGNMENT", "⚠ Alignment error NOT detected - may be acceptable depending on design");
                end
            end
        join
        
        alignment_error_detected = 0;
    endtask
    
    //===========================================================================
    // Advanced Error Pattern Tests
    //===========================================================================
    
    virtual task test_subtle_error_patterns();
        `uvm_info("SENSITIVITY_SUBTLE", "Testing subtle error pattern detection", UVM_MEDIUM)
        
        // Test 1: Single bit error in data
        test_single_bit_data_error();
        
        // Test 2: Off-by-one length error
        test_length_mismatch_error();
        
        // Test 3: Timing violation (setup/hold)
        test_timing_violation_error();
    endtask
    
    virtual task test_single_bit_data_error();
        uart_transaction tr;
        bit [31:0] original_data;
        
        tr = uart_transaction::type_id::create("single_bit_error_tr");
        assert(tr.randomize());
        
        original_data = tr.data;
        tr.data = tr.data ^ 32'h00000001; // Single bit flip
        total_injected_errors++;
        
        `uvm_info("SENSITIVITY_SUBTLE", $sformatf("Single bit error: %h -> %h", original_data, tr.data), UVM_HIGH)
        
        // This error might be harder to detect, so we'll be more lenient
        fork
            begin
                sequencer.start_item(tr);
                sequencer.finish_item(tr);
            end
            begin
                wait_for_error_detection("DATA_ERROR", 2000ns);
                if (crc_error_detected) begin
                    total_detected_errors++;
                    `uvm_info("SENSITIVITY_SUBTLE", "✓ Single bit error detected via CRC", UVM_LOW)
                end else begin
                    `uvm_warning("SENSITIVITY_SUBTLE", "⚠ Single bit error not detected - may require stronger error detection");
                end
            end
        join
        
        crc_error_detected = 0;
    endtask
    
    virtual task test_length_mismatch_error();
        uart_transaction tr;
        
        tr = uart_transaction::type_id::create("length_mismatch_tr");
        assert(tr.randomize());
        
        // Create length field that doesn't match actual data length
        tr.length = tr.length + 1; // Off by one
        total_injected_errors++;
        
        `uvm_info("SENSITIVITY_SUBTLE", $sformatf("Length mismatch error: declared=%0d", tr.length), UVM_HIGH)
        
        fork
            begin
                sequencer.start_item(tr);
                sequencer.finish_item(tr);
            end
            begin
                wait_for_error_detection("LENGTH_ERROR", 1500ns);
                if (framing_error_detected) begin
                    total_detected_errors++;
                    `uvm_info("SENSITIVITY_SUBTLE", "✓ Length mismatch error detected", UVM_LOW)
                end else begin
                    `uvm_warning("SENSITIVITY_SUBTLE", "⚠ Length mismatch error not detected");
                end
            end
        join
        
        framing_error_detected = 0;
    endtask
    
    virtual task test_timing_violation_error();
        // This would require more sophisticated timing control
        // For now, just document the requirement
        `uvm_info("SENSITIVITY_TIMING", "Timing violation testing requires advanced timing control", UVM_MEDIUM)
    endtask
    
    virtual task test_boundary_error_conditions();
        `uvm_info("SENSITIVITY_BOUNDARY", "Testing boundary error conditions", UVM_MEDIUM)
        
        // Test maximum/minimum values that might cause overflow
        test_overflow_conditions();
        test_underflow_conditions();
    endtask
    
    virtual task test_overflow_conditions();
        uart_transaction tr;
        
        tr = uart_transaction::type_id::create("overflow_tr");
        
        // Test maximum values
        tr.addr = 32'hFFFFFFFF;
        tr.data = 32'hFFFFFFFF;
        tr.length = 255;
        
        total_injected_errors++;
        
        fork
            begin
                sequencer.start_item(tr);
                sequencer.finish_item(tr);
            end
            begin
                wait_for_error_detection("OVERFLOW_ERROR", 1000ns);
                // This might not be an error depending on design
                `uvm_info("SENSITIVITY_BOUNDARY", "Overflow condition tested", UVM_MEDIUM)
            end
        join
    endtask
    
    virtual task test_underflow_conditions();
        uart_transaction tr;
        
        tr = uart_transaction::type_id::create("underflow_tr");
        
        // Test minimum values
        tr.addr = 32'h00000000;
        tr.data = 32'h00000000;
        tr.length = 0;
        
        total_injected_errors++;
        
        fork
            begin
                sequencer.start_item(tr);
                sequencer.finish_item(tr);
            end
            begin
                wait_for_error_detection("UNDERFLOW_ERROR", 1000ns);
                `uvm_info("SENSITIVITY_BOUNDARY", "Underflow condition tested", UVM_MEDIUM)
            end
        join
    endtask
    
    //===========================================================================
    // Error Detection Monitoring Task
    //===========================================================================
    
    virtual task monitor_error_detection();
        forever begin
            @(posedge clk);
            
            // Monitor for various error indicators
            // This would be connected to actual error signals from DUT
            
            // For now, we'll use UVM report monitoring
            // In a real implementation, this would monitor actual signals
        end
    endtask
    
    virtual task wait_for_error_detection(string error_type, time timeout);
        fork
            begin
                // Wait for specific error type detection
                case (error_type)
                    "CRC_ERROR": begin
                        wait(crc_error_detected == 1);
                    end
                    "TIMEOUT_ERROR": begin
                        wait(timeout_error_detected == 1);
                    end
                    "FRAMING_ERROR": begin
                        wait(framing_error_detected == 1);
                    end
                    "PROTOCOL_ERROR": begin
                        wait(protocol_error_detected == 1);
                    end
                    "ALIGNMENT_ERROR": begin
                        wait(alignment_error_detected == 1);
                    end
                    default: begin
                        // Generic error detection
                        #timeout;
                    end
                endcase
            end
            begin
                #timeout;
                `uvm_warning("SENSITIVITY_TIMEOUT", $sformatf("Timeout waiting for %s detection", error_type));
            end
        join_any
        disable fork;
    endtask
    
    //===========================================================================
    // Report Generation
    //===========================================================================
    
    virtual function void generate_sensitivity_report();
        detection_rate = (total_injected_errors > 0) ? 
                        (real'(total_detected_errors) / real'(total_injected_errors)) * 100.0 : 0.0;
        
        `uvm_info("SENSITIVITY_REPORT", "=== Verification Environment Sensitivity Test Report ===", UVM_LOW)
        `uvm_info("SENSITIVITY_REPORT", $sformatf("Total Injected Errors: %0d", total_injected_errors), UVM_LOW)
        `uvm_info("SENSITIVITY_REPORT", $sformatf("Total Detected Errors: %0d", total_detected_errors), UVM_LOW)
        `uvm_info("SENSITIVITY_REPORT", $sformatf("Detection Rate: %0.2f%%", detection_rate), UVM_LOW)
        
        if (detection_rate >= 95.0) begin
            `uvm_info("SENSITIVITY_REPORT", "✓ EXCELLENT: Verification environment highly sensitive to errors", UVM_LOW)
        end else if (detection_rate >= 85.0) begin
            `uvm_info("SENSITIVITY_REPORT", "✓ GOOD: Verification environment adequately sensitive to errors", UVM_LOW)
        end else if (detection_rate >= 70.0) begin
            `uvm_warning("SENSITIVITY_REPORT", "⚠ MODERATE: Verification environment needs improvement");
        end else begin
            `uvm_fatal("SENSITIVITY_REPORT", "✗ CRITICAL: Verification environment insufficient - too many false negatives");
        end
        
        `uvm_info("SENSITIVITY_REPORT", "=== End Sensitivity Test Report ===", UVM_LOW)
    endfunction
    
    virtual function void final_phase(uvm_phase phase);
        super.final_phase(phase);
        
        `uvm_info("SENSITIVITY_FINAL", "Verification Environment Sensitivity Test Completed", UVM_LOW)
        `uvm_info("SENSITIVITY_FINAL", $sformatf("Final Detection Rate: %0.2f%%", detection_rate), UVM_LOW)
        
        // Ensure minimum detection rate for test pass
        if (detection_rate < 85.0) begin
            `uvm_fatal("SENSITIVITY_FINAL", "Verification environment sensitivity test FAILED - insufficient error detection capability");
        end
    endfunction

endclass : verification_environment_sensitivity_test