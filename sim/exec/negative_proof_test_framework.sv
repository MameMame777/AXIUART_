`timescale 1ns / 1ps

//==============================================================================
// Negative Proof Test Framework
// Phase 4.2 Implementation - Systematic Error Injection for Detection Capability Verification
//==============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class Negative_Proof_Test_Framework extends Enhanced_Uart_Axi4_Base_Test;
    `uvm_component_utils(Negative_Proof_Test_Framework)

    // Error injection control
    typedef enum {
        NO_ERROR,
        CRC_ERROR,
        TIMEOUT_ERROR,
        PROTOCOL_VIOLATION_ERROR,
        FRAMING_ERROR,
        PARITY_ERROR,
        OVERFLOW_ERROR,
        UNDERFLOW_ERROR,
        BOUNDARY_ERROR
    } error_type_e;

    // Detection capability metrics
    typedef struct {
        int total_injected;
        int correctly_detected;
        int false_positives;
        int false_negatives;
        int detection_delay_sum;
        int min_detection_delay;
        int max_detection_delay;
        real detection_rate;
        real average_delay;
    } detection_metrics_t;

    // Error injection configuration
    rand error_type_e injected_error_type;
    rand int error_injection_cycle;
    rand bit[31:0] error_data_pattern;
    rand int error_duration;
    
    // Metrics storage
    detection_metrics_t crc_metrics;
    detection_metrics_t timeout_metrics;
    detection_metrics_t protocol_metrics;
    detection_metrics_t framing_metrics;
    detection_metrics_t parity_metrics;
    detection_metrics_t overflow_metrics;
    detection_metrics_t underflow_metrics;
    detection_metrics_t boundary_metrics;

    // Event tracking
    event error_injected;
    event error_detected;
    event false_positive_detected;
    event false_negative_confirmed;

    // Time tracking
    time error_injection_time;
    time error_detection_time;
    
    // Detection state tracking
    bit error_injection_active;
    bit error_detected_flag;
    int current_test_id;

    // Constraints for realistic error scenarios
    constraint error_timing_c {
        error_injection_cycle inside {[100:10000]};
        error_duration inside {[1:100]};
    }

    constraint error_pattern_c {
        error_data_pattern != 32'h0;
        error_data_pattern != 32'hFFFFFFFF;
    }

    function new(string name = "Negative_Proof_Test_Framework", uvm_component parent = null);
        super.new(name, parent);
        initialize_metrics();
    endfunction

    function void initialize_metrics();
        // Initialize all metric structures
        crc_metrics = '{0, 0, 0, 0, 0, 999999, 0, 0.0, 0.0};
        timeout_metrics = '{0, 0, 0, 0, 0, 999999, 0, 0.0, 0.0};
        protocol_metrics = '{0, 0, 0, 0, 0, 999999, 0, 0.0, 0.0};
        framing_metrics = '{0, 0, 0, 0, 0, 999999, 0, 0.0, 0.0};
        parity_metrics = '{0, 0, 0, 0, 0, 999999, 0, 0.0, 0.0};
        overflow_metrics = '{0, 0, 0, 0, 0, 999999, 0, 0.0, 0.0};
        underflow_metrics = '{0, 0, 0, 0, 0, 999999, 0, 0.0, 0.0};
        boundary_metrics = '{0, 0, 0, 0, 0, 999999, 0, 0.0, 0.0};
        
        error_injection_active = 1'b0;
        error_detected_flag = 1'b0;
        current_test_id = 0;
    endfunction

    virtual task main_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        `uvm_info("NEGATIVE_PROOF", "Starting Negative Proof Test Framework", UVM_LOW)
        
        // Execute systematic error injection tests
        execute_crc_error_injection_tests();
        execute_timeout_error_injection_tests();
        execute_protocol_violation_injection_tests();
        execute_framing_error_injection_tests();
        execute_parity_error_injection_tests();
        execute_overflow_error_injection_tests();
        execute_underflow_error_injection_tests();
        execute_boundary_error_injection_tests();
        
        // Generate comprehensive detection capability report
        generate_detection_capability_report();
        
        // Validate zero-tolerance detection requirements
        validate_zero_tolerance_detection();
        
        phase.drop_objection(this);
    endtask

    //==========================================================================
    // CRC Error Injection Tests
    //==========================================================================
    virtual task execute_crc_error_injection_tests();
        `uvm_info("CRC_ERROR_TEST", "Starting CRC Error Injection Tests", UVM_LOW)
        
        for (int test_iteration = 0; test_iteration < 100; test_iteration++) begin
            current_test_id = test_iteration;
            
            // Inject CRC error
            inject_crc_error();
            
            // Wait for detection or timeout
            fork
                wait_for_error_detection();
                detection_timeout_monitor();
            join_any
            disable fork;
            
            // Update metrics
            update_crc_metrics();
            
            // Reset for next iteration
            reset_error_injection_state();
            
            // Wait between tests
            #1000;
        end
        
        calculate_final_crc_metrics();
        `uvm_info("CRC_ERROR_TEST", $sformatf("CRC Detection Rate: %0.2f%%", crc_metrics.detection_rate), UVM_LOW)
    endtask

    virtual task inject_crc_error();
        bit[31:0] corrupted_data;
        
        // Wait for normal transaction
        wait_for_transaction_start();
        
        // Corrupt CRC data
        corrupted_data = error_data_pattern ^ 32'hDEADBEEF;
        
        // Record injection time
        error_injection_time = $time;
        error_injection_active = 1'b1;
        crc_metrics.total_injected++;
        
        // Inject corrupted CRC
        force_crc_corruption(corrupted_data);
        
        ->error_injected;
        `uvm_info("CRC_INJECT", $sformatf("CRC error injected at time %0t", $time), UVM_DEBUG)
    endtask

    virtual task force_crc_corruption(bit[31:0] corrupt_pattern);
        // This would interface with the DUT to corrupt CRC
        // Implementation depends on specific DUT interface
        `uvm_info("CRC_CORRUPT", $sformatf("Forcing CRC corruption with pattern 0x%08h", corrupt_pattern), UVM_DEBUG)
        
        // Simulate CRC corruption timing
        #(error_duration);
    endtask

    //==========================================================================
    // Timeout Error Injection Tests  
    //==========================================================================
    virtual task execute_timeout_error_injection_tests();
        `uvm_info("TIMEOUT_ERROR_TEST", "Starting Timeout Error Injection Tests", UVM_LOW)
        
        for (int test_iteration = 0; test_iteration < 50; test_iteration++) begin
            current_test_id = test_iteration;
            
            // Inject timeout error
            inject_timeout_error();
            
            // Wait for detection
            fork
                wait_for_error_detection();
                detection_timeout_monitor();
            join_any
            disable fork;
            
            // Update metrics
            update_timeout_metrics();
            
            // Reset for next iteration
            reset_error_injection_state();
            
            #2000;
        end
        
        calculate_final_timeout_metrics();
        `uvm_info("TIMEOUT_ERROR_TEST", $sformatf("Timeout Detection Rate: %0.2f%%", timeout_metrics.detection_rate), UVM_LOW)
    endtask

    virtual task inject_timeout_error();
        // Record injection time
        error_injection_time = $time;
        error_injection_active = 1'b1;
        timeout_metrics.total_injected++;
        
        // Inject timeout by delaying response
        inject_response_delay(error_duration * 100);
        
        ->error_injected;
        `uvm_info("TIMEOUT_INJECT", $sformatf("Timeout error injected at time %0t", $time), UVM_DEBUG)
    endtask

    virtual task inject_response_delay(int delay_cycles);
        `uvm_info("TIMEOUT_DELAY", $sformatf("Injecting %0d cycle delay", delay_cycles), UVM_DEBUG)
        #(delay_cycles);
    endtask

    //==========================================================================
    // Protocol Violation Injection Tests
    //==========================================================================
    virtual task execute_protocol_violation_injection_tests();
        `uvm_info("PROTOCOL_ERROR_TEST", "Starting Protocol Violation Injection Tests", UVM_LOW)
        
        for (int test_iteration = 0; test_iteration < 75; test_iteration++) begin
            current_test_id = test_iteration;
            
            // Inject protocol violation
            inject_protocol_violation();
            
            // Wait for detection
            fork
                wait_for_error_detection();
                detection_timeout_monitor();
            join_any
            disable fork;
            
            // Update metrics
            update_protocol_metrics();
            
            // Reset for next iteration
            reset_error_injection_state();
            
            #1500;
        end
        
        calculate_final_protocol_metrics();
        `uvm_info("PROTOCOL_ERROR_TEST", $sformatf("Protocol Violation Detection Rate: %0.2f%%", protocol_metrics.detection_rate), UVM_LOW)
    endtask

    virtual task inject_protocol_violation();
        // Record injection time
        error_injection_time = $time;
        error_injection_active = 1'b1;
        protocol_metrics.total_injected++;
        
        // Inject various protocol violations
        case (current_test_id % 4)
            0: inject_invalid_command();
            1: inject_invalid_sequence();
            2: inject_invalid_state_transition();
            3: inject_invalid_handshake();
        endcase
        
        ->error_injected;
        `uvm_info("PROTOCOL_INJECT", $sformatf("Protocol violation injected at time %0t", $time), UVM_DEBUG)
    endtask

    virtual task inject_invalid_command();
        `uvm_info("PROTOCOL_CMD", "Injecting invalid command", UVM_DEBUG)
        // Implementation specific to DUT command interface
        #(error_duration);
    endtask

    virtual task inject_invalid_sequence();
        `uvm_info("PROTOCOL_SEQ", "Injecting invalid sequence", UVM_DEBUG)
        // Implementation specific to DUT sequence requirements
        #(error_duration);
    endtask

    virtual task inject_invalid_state_transition();
        `uvm_info("PROTOCOL_STATE", "Injecting invalid state transition", UVM_DEBUG)
        // Implementation specific to DUT state machine
        #(error_duration);
    endtask

    virtual task inject_invalid_handshake();
        `uvm_info("PROTOCOL_HANDSHAKE", "Injecting invalid handshake", UVM_DEBUG)
        // Implementation specific to DUT handshake protocol
        #(error_duration);
    endtask

    //==========================================================================
    // Framing Error Injection Tests
    //==========================================================================
    virtual task execute_framing_error_injection_tests();
        `uvm_info("FRAMING_ERROR_TEST", "Starting Framing Error Injection Tests", UVM_LOW)
        
        for (int test_iteration = 0; test_iteration < 60; test_iteration++) begin
            current_test_id = test_iteration;
            
            inject_framing_error();
            
            fork
                wait_for_error_detection();
                detection_timeout_monitor();
            join_any
            disable fork;
            
            update_framing_metrics();
            reset_error_injection_state();
            
            #1200;
        end
        
        calculate_final_framing_metrics();
        `uvm_info("FRAMING_ERROR_TEST", $sformatf("Framing Error Detection Rate: %0.2f%%", framing_metrics.detection_rate), UVM_LOW)
    endtask

    virtual task inject_framing_error();
        error_injection_time = $time;
        error_injection_active = 1'b1;
        framing_metrics.total_injected++;
        
        // Inject framing errors
        case (current_test_id % 3)
            0: inject_start_bit_error();
            1: inject_stop_bit_error();
            2: inject_bit_width_error();
        endcase
        
        ->error_injected;
        `uvm_info("FRAMING_INJECT", $sformatf("Framing error injected at time %0t", $time), UVM_DEBUG)
    endtask

    virtual task inject_start_bit_error();
        `uvm_info("FRAMING_START", "Injecting start bit error", UVM_DEBUG)
        #(error_duration);
    endtask

    virtual task inject_stop_bit_error();
        `uvm_info("FRAMING_STOP", "Injecting stop bit error", UVM_DEBUG)
        #(error_duration);
    endtask

    virtual task inject_bit_width_error();
        `uvm_info("FRAMING_WIDTH", "Injecting bit width error", UVM_DEBUG)
        #(error_duration);
    endtask

    //==========================================================================
    // Additional Error Type Tests (Parity, Overflow, Underflow, Boundary)
    //==========================================================================
    virtual task execute_parity_error_injection_tests();
        `uvm_info("PARITY_ERROR_TEST", "Starting Parity Error Injection Tests", UVM_LOW)
        
        for (int test_iteration = 0; test_iteration < 40; test_iteration++) begin
            current_test_id = test_iteration;
            inject_parity_error();
            
            fork
                wait_for_error_detection();
                detection_timeout_monitor();
            join_any
            disable fork;
            
            update_parity_metrics();
            reset_error_injection_state();
            #800;
        end
        
        calculate_final_parity_metrics();
        `uvm_info("PARITY_ERROR_TEST", $sformatf("Parity Error Detection Rate: %0.2f%%", parity_metrics.detection_rate), UVM_LOW)
    endtask

    virtual task execute_overflow_error_injection_tests();
        `uvm_info("OVERFLOW_ERROR_TEST", "Starting Overflow Error Injection Tests", UVM_LOW)
        
        for (int test_iteration = 0; test_iteration < 30; test_iteration++) begin
            current_test_id = test_iteration;
            inject_overflow_error();
            
            fork
                wait_for_error_detection();
                detection_timeout_monitor();
            join_any
            disable fork;
            
            update_overflow_metrics();
            reset_error_injection_state();
            #1000;
        end
        
        calculate_final_overflow_metrics();
        `uvm_info("OVERFLOW_ERROR_TEST", $sformatf("Overflow Error Detection Rate: %0.2f%%", overflow_metrics.detection_rate), UVM_LOW)
    endtask

    virtual task execute_underflow_error_injection_tests();
        `uvm_info("UNDERFLOW_ERROR_TEST", "Starting Underflow Error Injection Tests", UVM_LOW)
        
        for (int test_iteration = 0; test_iteration < 30; test_iteration++) begin
            current_test_id = test_iteration;
            inject_underflow_error();
            
            fork
                wait_for_error_detection();
                detection_timeout_monitor();
            join_any
            disable fork;
            
            update_underflow_metrics();
            reset_error_injection_state();
            #1000;
        end
        
        calculate_final_underflow_metrics();
        `uvm_info("UNDERFLOW_ERROR_TEST", $sformatf("Underflow Error Detection Rate: %0.2f%%", underflow_metrics.detection_rate), UVM_LOW)
    endtask

    virtual task execute_boundary_error_injection_tests();
        `uvm_info("BOUNDARY_ERROR_TEST", "Starting Boundary Error Injection Tests", UVM_LOW)
        
        for (int test_iteration = 0; test_iteration < 50; test_iteration++) begin
            current_test_id = test_iteration;
            inject_boundary_error();
            
            fork
                wait_for_error_detection();
                detection_timeout_monitor();
            join_any
            disable fork;
            
            update_boundary_metrics();
            reset_error_injection_state();
            #1200;
        end
        
        calculate_final_boundary_metrics();
        `uvm_info("BOUNDARY_ERROR_TEST", $sformatf("Boundary Error Detection Rate: %0.2f%%", boundary_metrics.detection_rate), UVM_LOW)
    endtask

    //==========================================================================
    // Error Injection Implementation Tasks
    //==========================================================================
    virtual task inject_parity_error();
        error_injection_time = $time;
        error_injection_active = 1'b1;
        parity_metrics.total_injected++;
        
        `uvm_info("PARITY_INJECT", "Injecting parity error", UVM_DEBUG)
        #(error_duration);
        ->error_injected;
    endtask

    virtual task inject_overflow_error();
        error_injection_time = $time;
        error_injection_active = 1'b1;
        overflow_metrics.total_injected++;
        
        `uvm_info("OVERFLOW_INJECT", "Injecting overflow error", UVM_DEBUG)
        #(error_duration * 2); // Longer duration for overflow
        ->error_injected;
    endtask

    virtual task inject_underflow_error();
        error_injection_time = $time;
        error_injection_active = 1'b1;
        underflow_metrics.total_injected++;
        
        `uvm_info("UNDERFLOW_INJECT", "Injecting underflow error", UVM_DEBUG)
        #(error_duration * 2); // Longer duration for underflow
        ->error_injected;
    endtask

    virtual task inject_boundary_error();
        error_injection_time = $time;
        error_injection_active = 1'b1;
        boundary_metrics.total_injected++;
        
        `uvm_info("BOUNDARY_INJECT", "Injecting boundary condition error", UVM_DEBUG)
        #(error_duration);
        ->error_injected;
    endtask

    //==========================================================================
    // Detection Monitoring and Metrics Update
    //==========================================================================
    virtual task wait_for_error_detection();
        wait(error_detected);
        error_detection_time = $time;
        error_detected_flag = 1'b1;
        ->error_detected;
    endtask

    virtual task detection_timeout_monitor();
        #10000; // 10us timeout
        if (!error_detected_flag) begin
            ->false_negative_confirmed;
            `uvm_warning("DETECTION_TIMEOUT", "Error detection timeout - possible false negative")
        end
    endtask

    virtual task wait_for_transaction_start();
        // Wait for DUT transaction activity
        #100;
    endtask

    virtual function void update_crc_metrics();
        if (error_detected_flag) begin
            crc_metrics.correctly_detected++;
            update_detection_delay(crc_metrics);
        end else begin
            crc_metrics.false_negatives++;
        end
    endfunction

    virtual function void update_timeout_metrics();
        if (error_detected_flag) begin
            timeout_metrics.correctly_detected++;
            update_detection_delay(timeout_metrics);
        end else begin
            timeout_metrics.false_negatives++;
        end
    endfunction

    virtual function void update_protocol_metrics();
        if (error_detected_flag) begin
            protocol_metrics.correctly_detected++;
            update_detection_delay(protocol_metrics);
        end else begin
            protocol_metrics.false_negatives++;
        end
    endfunction

    virtual function void update_framing_metrics();
        if (error_detected_flag) begin
            framing_metrics.correctly_detected++;
            update_detection_delay(framing_metrics);
        end else begin
            framing_metrics.false_negatives++;
        end
    endfunction

    virtual function void update_parity_metrics();
        if (error_detected_flag) begin
            parity_metrics.correctly_detected++;
            update_detection_delay(parity_metrics);
        end else begin
            parity_metrics.false_negatives++;
        end
    endfunction

    virtual function void update_overflow_metrics();
        if (error_detected_flag) begin
            overflow_metrics.correctly_detected++;
            update_detection_delay(overflow_metrics);
        end else begin
            overflow_metrics.false_negatives++;
        end
    endfunction

    virtual function void update_underflow_metrics();
        if (error_detected_flag) begin
            underflow_metrics.correctly_detected++;
            update_detection_delay(underflow_metrics);
        end else begin
            underflow_metrics.false_negatives++;
        end
    endfunction

    virtual function void update_boundary_metrics();
        if (error_detected_flag) begin
            boundary_metrics.correctly_detected++;
            update_detection_delay(boundary_metrics);
        end else begin
            boundary_metrics.false_negatives++;
        end
    endfunction

    virtual function void update_detection_delay(ref detection_metrics_t metrics);
        int detection_delay = error_detection_time - error_injection_time;
        
        metrics.detection_delay_sum += detection_delay;
        if (detection_delay < metrics.min_detection_delay) 
            metrics.min_detection_delay = detection_delay;
        if (detection_delay > metrics.max_detection_delay) 
            metrics.max_detection_delay = detection_delay;
    endfunction

    virtual function void reset_error_injection_state();
        error_injection_active = 1'b0;
        error_detected_flag = 1'b0;
        error_injection_time = 0;
        error_detection_time = 0;
    endfunction

    //==========================================================================
    // Final Metrics Calculation
    //==========================================================================
    virtual function void calculate_final_crc_metrics();
        if (crc_metrics.total_injected > 0) begin
            crc_metrics.detection_rate = (real'(crc_metrics.correctly_detected) / real'(crc_metrics.total_injected)) * 100.0;
            if (crc_metrics.correctly_detected > 0)
                crc_metrics.average_delay = real'(crc_metrics.detection_delay_sum) / real'(crc_metrics.correctly_detected);
        end
    endfunction

    virtual function void calculate_final_timeout_metrics();
        if (timeout_metrics.total_injected > 0) begin
            timeout_metrics.detection_rate = (real'(timeout_metrics.correctly_detected) / real'(timeout_metrics.total_injected)) * 100.0;
            if (timeout_metrics.correctly_detected > 0)
                timeout_metrics.average_delay = real'(timeout_metrics.detection_delay_sum) / real'(timeout_metrics.correctly_detected);
        end
    endfunction

    virtual function void calculate_final_protocol_metrics();
        if (protocol_metrics.total_injected > 0) begin
            protocol_metrics.detection_rate = (real'(protocol_metrics.correctly_detected) / real'(protocol_metrics.total_injected)) * 100.0;
            if (protocol_metrics.correctly_detected > 0)
                protocol_metrics.average_delay = real'(protocol_metrics.detection_delay_sum) / real'(protocol_metrics.correctly_detected);
        end
    endfunction

    virtual function void calculate_final_framing_metrics();
        if (framing_metrics.total_injected > 0) begin
            framing_metrics.detection_rate = (real'(framing_metrics.correctly_detected) / real'(framing_metrics.total_injected)) * 100.0;
            if (framing_metrics.correctly_detected > 0)
                framing_metrics.average_delay = real'(framing_metrics.detection_delay_sum) / real'(framing_metrics.correctly_detected);
        end
    endfunction

    virtual function void calculate_final_parity_metrics();
        if (parity_metrics.total_injected > 0) begin
            parity_metrics.detection_rate = (real'(parity_metrics.correctly_detected) / real'(parity_metrics.total_injected)) * 100.0;
            if (parity_metrics.correctly_detected > 0)
                parity_metrics.average_delay = real'(parity_metrics.detection_delay_sum) / real'(parity_metrics.correctly_detected);
        end
    endfunction

    virtual function void calculate_final_overflow_metrics();
        if (overflow_metrics.total_injected > 0) begin
            overflow_metrics.detection_rate = (real'(overflow_metrics.correctly_detected) / real'(overflow_metrics.total_injected)) * 100.0;
            if (overflow_metrics.correctly_detected > 0)
                overflow_metrics.average_delay = real'(overflow_metrics.detection_delay_sum) / real'(overflow_metrics.correctly_detected);
        end
    endfunction

    virtual function void calculate_final_underflow_metrics();
        if (underflow_metrics.total_injected > 0) begin
            underflow_metrics.detection_rate = (real'(underflow_metrics.correctly_detected) / real'(underflow_metrics.total_injected)) * 100.0;
            if (underflow_metrics.correctly_detected > 0)
                underflow_metrics.average_delay = real'(underflow_metrics.detection_delay_sum) / real'(underflow_metrics.correctly_detected);
        end
    endfunction

    virtual function void calculate_final_boundary_metrics();
        if (boundary_metrics.total_injected > 0) begin
            boundary_metrics.detection_rate = (real'(boundary_metrics.correctly_detected) / real'(boundary_metrics.total_injected)) * 100.0;
            if (boundary_metrics.correctly_detected > 0)
                boundary_metrics.average_delay = real'(boundary_metrics.detection_delay_sum) / real'(boundary_metrics.correctly_detected);
        end
    endfunction

    //==========================================================================
    // Comprehensive Detection Capability Report Generation
    //==========================================================================
    virtual function void generate_detection_capability_report();
        string report_file = "negative_proof_detection_report.txt";
        int file_handle;
        
        file_handle = $fopen(report_file, "w");
        if (file_handle == 0) begin
            `uvm_error("REPORT_GEN", $sformatf("Failed to open report file: %s", report_file))
            return;
        end
        
        // Write comprehensive report
        $fwrite(file_handle, "=================================================================\n");
        $fwrite(file_handle, "NEGATIVE PROOF TEST - DETECTION CAPABILITY REPORT\n");
        $fwrite(file_handle, "Generated at: %0t\n", $time);
        $fwrite(file_handle, "=================================================================\n\n");
        
        // CRC Error Detection Results
        write_error_metrics_to_file(file_handle, "CRC ERROR", crc_metrics);
        write_error_metrics_to_file(file_handle, "TIMEOUT ERROR", timeout_metrics);
        write_error_metrics_to_file(file_handle, "PROTOCOL VIOLATION", protocol_metrics);
        write_error_metrics_to_file(file_handle, "FRAMING ERROR", framing_metrics);
        write_error_metrics_to_file(file_handle, "PARITY ERROR", parity_metrics);
        write_error_metrics_to_file(file_handle, "OVERFLOW ERROR", overflow_metrics);
        write_error_metrics_to_file(file_handle, "UNDERFLOW ERROR", underflow_metrics);
        write_error_metrics_to_file(file_handle, "BOUNDARY ERROR", boundary_metrics);
        
        // Overall Summary
        write_overall_summary_to_file(file_handle);
        
        $fclose(file_handle);
        `uvm_info("REPORT_GEN", $sformatf("Detection capability report generated: %s", report_file), UVM_LOW)
    endfunction

    virtual function void write_error_metrics_to_file(int file_handle, string error_type, detection_metrics_t metrics);
        $fwrite(file_handle, "-----------------------------------------------------------------\n");
        $fwrite(file_handle, "%s DETECTION METRICS:\n", error_type);
        $fwrite(file_handle, "-----------------------------------------------------------------\n");
        $fwrite(file_handle, "Total Errors Injected:     %0d\n", metrics.total_injected);
        $fwrite(file_handle, "Correctly Detected:        %0d\n", metrics.correctly_detected);
        $fwrite(file_handle, "False Positives:           %0d\n", metrics.false_positives);
        $fwrite(file_handle, "False Negatives:           %0d\n", metrics.false_negatives);
        $fwrite(file_handle, "Detection Rate:            %0.2f%%\n", metrics.detection_rate);
        $fwrite(file_handle, "Average Detection Delay:   %0.2f ns\n", metrics.average_delay);
        $fwrite(file_handle, "Min Detection Delay:       %0d ns\n", metrics.min_detection_delay);
        $fwrite(file_handle, "Max Detection Delay:       %0d ns\n", metrics.max_detection_delay);
        
        // Zero-tolerance validation
        if (metrics.detection_rate < 100.0) begin
            $fwrite(file_handle, "*** ZERO-TOLERANCE VIOLATION: Detection rate below 100%% ***\n");
        end
        if (metrics.false_positives > 0) begin
            $fwrite(file_handle, "*** ZERO-TOLERANCE VIOLATION: False positives detected ***\n");
        end
        if (metrics.false_negatives > 0) begin
            $fwrite(file_handle, "*** ZERO-TOLERANCE VIOLATION: False negatives detected ***\n");
        end
        
        $fwrite(file_handle, "\n");
    endfunction

    virtual function void write_overall_summary_to_file(int file_handle);
        int total_injected = crc_metrics.total_injected + timeout_metrics.total_injected + 
                            protocol_metrics.total_injected + framing_metrics.total_injected +
                            parity_metrics.total_injected + overflow_metrics.total_injected +
                            underflow_metrics.total_injected + boundary_metrics.total_injected;
                            
        int total_detected = crc_metrics.correctly_detected + timeout_metrics.correctly_detected + 
                            protocol_metrics.correctly_detected + framing_metrics.correctly_detected +
                            parity_metrics.correctly_detected + overflow_metrics.correctly_detected +
                            underflow_metrics.correctly_detected + boundary_metrics.correctly_detected;
                            
        int total_false_positives = crc_metrics.false_positives + timeout_metrics.false_positives + 
                                   protocol_metrics.false_positives + framing_metrics.false_positives +
                                   parity_metrics.false_positives + overflow_metrics.false_positives +
                                   underflow_metrics.false_positives + boundary_metrics.false_positives;
                                   
        int total_false_negatives = crc_metrics.false_negatives + timeout_metrics.false_negatives + 
                                   protocol_metrics.false_negatives + framing_metrics.false_negatives +
                                   parity_metrics.false_negatives + overflow_metrics.false_negatives +
                                   underflow_metrics.false_negatives + boundary_metrics.false_negatives;
        
        real overall_detection_rate = (total_injected > 0) ? (real'(total_detected) / real'(total_injected)) * 100.0 : 0.0;
        
        $fwrite(file_handle, "=================================================================\n");
        $fwrite(file_handle, "OVERALL DETECTION CAPABILITY SUMMARY\n");
        $fwrite(file_handle, "=================================================================\n");
        $fwrite(file_handle, "Total Errors Injected:     %0d\n", total_injected);
        $fwrite(file_handle, "Total Correctly Detected:  %0d\n", total_detected);
        $fwrite(file_handle, "Total False Positives:     %0d\n", total_false_positives);
        $fwrite(file_handle, "Total False Negatives:     %0d\n", total_false_negatives);
        $fwrite(file_handle, "Overall Detection Rate:    %0.2f%%\n", overall_detection_rate);
        $fwrite(file_handle, "\n");
        
        // Zero-tolerance final assessment
        $fwrite(file_handle, "ZERO-TOLERANCE ASSESSMENT:\n");
        if (overall_detection_rate == 100.0 && total_false_positives == 0 && total_false_negatives == 0) begin
            $fwrite(file_handle, "*** ZERO-TOLERANCE REQUIREMENTS MET ***\n");
            $fwrite(file_handle, "Verification environment meets zero-tolerance detection standards.\n");
        end else begin
            $fwrite(file_handle, "*** ZERO-TOLERANCE REQUIREMENTS VIOLATED ***\n");
            $fwrite(file_handle, "Verification environment does not meet zero-tolerance standards.\n");
            $fwrite(file_handle, "IMMEDIATE ACTION REQUIRED.\n");
        end
        
        $fwrite(file_handle, "=================================================================\n");
    endfunction

    //==========================================================================
    // Zero-Tolerance Validation
    //==========================================================================
    virtual function void validate_zero_tolerance_detection();
        bit zero_tolerance_met = 1'b1;
        string violation_summary = "";
        
        // Check each error type for zero-tolerance compliance
        if (!check_zero_tolerance_metrics(crc_metrics, "CRC")) zero_tolerance_met = 1'b0;
        if (!check_zero_tolerance_metrics(timeout_metrics, "TIMEOUT")) zero_tolerance_met = 1'b0;
        if (!check_zero_tolerance_metrics(protocol_metrics, "PROTOCOL")) zero_tolerance_met = 1'b0;
        if (!check_zero_tolerance_metrics(framing_metrics, "FRAMING")) zero_tolerance_met = 1'b0;
        if (!check_zero_tolerance_metrics(parity_metrics, "PARITY")) zero_tolerance_met = 1'b0;
        if (!check_zero_tolerance_metrics(overflow_metrics, "OVERFLOW")) zero_tolerance_met = 1'b0;
        if (!check_zero_tolerance_metrics(underflow_metrics, "UNDERFLOW")) zero_tolerance_met = 1'b0;
        if (!check_zero_tolerance_metrics(boundary_metrics, "BOUNDARY")) zero_tolerance_met = 1'b0;
        
        if (zero_tolerance_met) begin
            `uvm_info("ZERO_TOLERANCE", "*** ZERO-TOLERANCE DETECTION REQUIREMENTS MET ***", UVM_LOW)
            `uvm_info("ZERO_TOLERANCE", "Verification environment successfully achieves 100% error detection", UVM_LOW)
        end else begin
            `uvm_error("ZERO_TOLERANCE", "*** ZERO-TOLERANCE DETECTION REQUIREMENTS VIOLATED ***")
            `uvm_error("ZERO_TOLERANCE", "Verification environment fails to achieve zero-tolerance standards")
            `uvm_error("ZERO_TOLERANCE", "IMMEDIATE INVESTIGATION AND CORRECTION REQUIRED")
        end
    endfunction

    virtual function bit check_zero_tolerance_metrics(detection_metrics_t metrics, string error_type);
        bit compliance = 1'b1;
        
        if (metrics.total_injected > 0) begin
            if (metrics.detection_rate < 100.0) begin
                `uvm_error("ZERO_TOLERANCE", $sformatf("%s: Detection rate %0.2f%% below 100%% requirement", error_type, metrics.detection_rate))
                compliance = 1'b0;
            end
            
            if (metrics.false_positives > 0) begin
                `uvm_error("ZERO_TOLERANCE", $sformatf("%s: %0d false positives detected (requirement: 0)", error_type, metrics.false_positives))
                compliance = 1'b0;
            end
            
            if (metrics.false_negatives > 0) begin
                `uvm_error("ZERO_TOLERANCE", $sformatf("%s: %0d false negatives detected (requirement: 0)", error_type, metrics.false_negatives))
                compliance = 1'b0;
            end
        end
        
        return compliance;
    endfunction

endclass

//==============================================================================
// Test Registration
//==============================================================================
typedef uvm_component_registry #(Negative_Proof_Test_Framework, "negative_proof_test") negative_proof_test_type;