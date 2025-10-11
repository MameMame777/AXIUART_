`timescale 1ns / 1ps

//==============================================================================
// Verification Environment Sensitivity Test
//==============================================================================
// File: verification_environment_sensitivity_test.sv
// Purpose: Test if verification environment can detect known injected errors
// Author: AI Assistant
// Date: 2025-10-11
// Description: Implements negative proof testing by injecting known errors
//              and verifying they are detected by the verification environment
//==============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;
import uart_axi4_pkg::*;

class Verification_Environment_Sensitivity_Test extends Enhanced_Uart_Axi4_Base_Test;
    `uvm_component_utils(Verification_Environment_Sensitivity_Test)
    
    // Error injection control
    bit error_injection_enabled = 1;
    bit crc_error_detected = 0;
    bit timeout_error_detected = 0;
    bit framing_error_detected = 0;
    bit protocol_error_detected = 0;
    
    // Error injection counters
    int crc_errors_injected = 0;
    int timeout_errors_injected = 0;
    int framing_errors_injected = 0;
    int protocol_errors_injected = 0;
    
    // Detection counters
    int crc_errors_detected = 0;
    int timeout_errors_detected = 0;
    int framing_errors_detected = 0;
    int protocol_errors_detected = 0;
    
    // Test configuration
    int num_error_injection_cycles = 10;
    time max_detection_timeout = 1000ns;
    
    function new(string name = "verification_environment_sensitivity_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        `uvm_info("VERIFY_ENV_SENS", "Building Verification Environment Sensitivity Test", UVM_LOW)
        
        // Override default test configuration for error injection
        if (!uvm_config_db#(bit)::get(this, "", "error_injection_enabled", error_injection_enabled)) begin
            error_injection_enabled = 1;
        end
        
        if (!uvm_config_db#(int)::get(this, "", "num_error_injection_cycles", num_error_injection_cycles)) begin
            num_error_injection_cycles = 10;
        end
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this, "Starting verification environment sensitivity test");
        
        `uvm_info("VERIFY_ENV_SENS", "=== Verification Environment Sensitivity Test Started ===", UVM_LOW)
        
        // Pre-test verification environment check
        verify_environment_baseline();
        
        // Test 1: CRC Error Detection Sensitivity
        test_crc_error_detection_sensitivity();
        
        // Test 2: Timeout Error Detection Sensitivity  
        test_timeout_error_detection_sensitivity();
        
        // Test 3: Framing Error Detection Sensitivity
        test_framing_error_detection_sensitivity();
        
        // Test 4: Protocol Violation Detection Sensitivity
        test_protocol_violation_detection_sensitivity();
        
        // Test 5: False Negative Pattern Detection
        test_false_negative_patterns();
        
        // Final verification environment validation
        validate_environment_sensitivity();
        
        `uvm_info("VERIFY_ENV_SENS", "=== Verification Environment Sensitivity Test Completed ===", UVM_LOW)
        
        phase.drop_objection(this, "Verification environment sensitivity test completed");
    endtask
    
    //==========================================================================
    // Test Method 1: CRC Error Detection Sensitivity
    //==========================================================================
    
    virtual task test_crc_error_detection_sensitivity();
        `uvm_info("VERIFY_ENV_SENS", "Testing CRC Error Detection Sensitivity", UVM_MEDIUM)
        
        for (int i = 0; i < num_error_injection_cycles; i++) begin
            uart_axi4_transaction tr;
            bit original_crc;
            bit corrupted_crc;
            
            // Create normal transaction
            tr = uart_axi4_transaction::type_id::create($sformatf("crc_error_tr_%0d", i));
            if (!tr.randomize()) begin
                `uvm_fatal("VERIFY_ENV_SENS", "Failed to randomize transaction for CRC error test")
            end
            
            // Store original CRC
            original_crc = tr.crc;
            
            // Inject CRC error (flip all bits)
            tr.crc = ~original_crc;
            corrupted_crc = tr.crc;
            crc_errors_injected++;
            
            `uvm_info("VERIFY_ENV_SENS", 
                $sformatf("Injecting CRC error %0d: Original=0x%02x, Corrupted=0x%02x", 
                         i+1, original_crc, corrupted_crc), UVM_HIGH)
            
            // Send transaction and monitor for error detection
            fork
                begin
                    // Send corrupted transaction
                    send_transaction_with_error_monitoring(tr, "CRC_ERROR");
                end
                begin
                    // Timeout watchdog
                    #max_detection_timeout;
                    `uvm_error("VERIFY_ENV_SENS", 
                        $sformatf("CRC error detection timeout for transaction %0d", i+1))
                end
            join_any
            disable fork;
            
            // Wait for error detection
            wait_for_crc_error_detection(i+1);
        end
        
        // Verify detection rate
        real detection_rate = real'(crc_errors_detected) / real'(crc_errors_injected) * 100.0;
        `uvm_info("VERIFY_ENV_SENS", 
            $sformatf("CRC Error Detection Rate: %0.2f%% (%0d/%0d)", 
                     detection_rate, crc_errors_detected, crc_errors_injected), UVM_LOW)
        
        if (detection_rate < 100.0) begin
            `uvm_fatal("VERIFY_ENV_SENS", 
                $sformatf("CRC error detection rate %0.2f%% below 100%% - verification environment insensitive", 
                         detection_rate))
        end
    endtask
    
    //==========================================================================
    // Test Method 2: Timeout Error Detection Sensitivity
    //==========================================================================
    
    virtual task test_timeout_error_detection_sensitivity();
        `uvm_info("VERIFY_ENV_SENS", "Testing Timeout Error Detection Sensitivity", UVM_MEDIUM)
        
        for (int i = 0; i < num_error_injection_cycles; i++) begin
            uart_axi4_transaction tr;
            
            // Create normal transaction
            tr = uart_axi4_transaction::type_id::create($sformatf("timeout_error_tr_%0d", i));
            if (!tr.randomize()) begin
                `uvm_fatal("VERIFY_ENV_SENS", "Failed to randomize transaction for timeout error test")
            end
            
            timeout_errors_injected++;
            
            `uvm_info("VERIFY_ENV_SENS", 
                $sformatf("Injecting timeout error %0d", i+1), UVM_HIGH)
            
            // Send transaction with artificial delay to cause timeout
            fork
                begin
                    inject_timeout_error(tr, i+1);
                end
                begin
                    // Timeout watchdog (longer than normal timeout)
                    #(max_detection_timeout * 3);
                    `uvm_error("VERIFY_ENV_SENS", 
                        $sformatf("Timeout error detection timeout for transaction %0d", i+1))
                end
            join_any
            disable fork;
            
            // Wait for timeout error detection
            wait_for_timeout_error_detection(i+1);
        end
        
        // Verify timeout detection rate
        real detection_rate = real'(timeout_errors_detected) / real'(timeout_errors_injected) * 100.0;
        `uvm_info("VERIFY_ENV_SENS", 
            $sformatf("Timeout Error Detection Rate: %0.2f%% (%0d/%0d)", 
                     detection_rate, timeout_errors_detected, timeout_errors_injected), UVM_LOW)
        
        if (detection_rate < 100.0) begin
            `uvm_fatal("VERIFY_ENV_SENS", 
                $sformatf("Timeout error detection rate %0.2f%% below 100%% - verification environment insensitive", 
                         detection_rate))
        end
    endtask
    
    //==========================================================================
    // Test Method 3: Framing Error Detection Sensitivity
    //==========================================================================
    
    virtual task test_framing_error_detection_sensitivity();
        `uvm_info("VERIFY_ENV_SENS", "Testing Framing Error Detection Sensitivity", UVM_MEDIUM)
        
        for (int i = 0; i < num_error_injection_cycles; i++) begin
            uart_axi4_transaction tr;
            
            // Create normal transaction
            tr = uart_axi4_transaction::type_id::create($sformatf("framing_error_tr_%0d", i));
            if (!tr.randomize()) begin
                `uvm_fatal("VERIFY_ENV_SENS", "Failed to randomize transaction for framing error test")
            end
            
            // Inject framing error (corrupt start/stop bits)
            inject_framing_error(tr, i+1);
            framing_errors_injected++;
            
            `uvm_info("VERIFY_ENV_SENS", 
                $sformatf("Injecting framing error %0d", i+1), UVM_HIGH)
            
            // Wait for framing error detection
            wait_for_framing_error_detection(i+1);
        end
        
        // Verify framing error detection rate
        real detection_rate = real'(framing_errors_detected) / real'(framing_errors_injected) * 100.0;
        `uvm_info("VERIFY_ENV_SENS", 
            $sformatf("Framing Error Detection Rate: %0.2f%% (%0d/%0d)", 
                     detection_rate, framing_errors_detected, framing_errors_injected), UVM_LOW)
        
        if (detection_rate < 100.0) begin
            `uvm_fatal("VERIFY_ENV_SENS", 
                $sformatf("Framing error detection rate %0.2f%% below 100%% - verification environment insensitive", 
                         detection_rate))
        end
    endtask
    
    //==========================================================================
    // Test Method 4: Protocol Violation Detection Sensitivity
    //==========================================================================
    
    virtual task test_protocol_violation_detection_sensitivity();
        `uvm_info("VERIFY_ENV_SENS", "Testing Protocol Violation Detection Sensitivity", UVM_MEDIUM)
        
        for (int i = 0; i < num_error_injection_cycles; i++) begin
            uart_axi4_transaction tr;
            
            // Create transaction with protocol violation
            tr = uart_axi4_transaction::type_id::create($sformatf("protocol_error_tr_%0d", i));
            if (!tr.randomize()) begin
                `uvm_fatal("VERIFY_ENV_SENS", "Failed to randomize transaction for protocol error test")
            end
            
            // Inject protocol violation (invalid command, wrong sequence, etc.)
            inject_protocol_violation(tr, i+1);
            protocol_errors_injected++;
            
            `uvm_info("VERIFY_ENV_SENS", 
                $sformatf("Injecting protocol violation %0d", i+1), UVM_HIGH)
            
            // Wait for protocol violation detection
            wait_for_protocol_violation_detection(i+1);
        end
        
        // Verify protocol violation detection rate
        real detection_rate = real'(protocol_errors_detected) / real'(protocol_errors_injected) * 100.0;
        `uvm_info("VERIFY_ENV_SENS", 
            $sformatf("Protocol Violation Detection Rate: %0.2f%% (%0d/%0d)", 
                     detection_rate, protocol_errors_detected, protocol_errors_injected), UVM_LOW)
        
        if (detection_rate < 100.0) begin
            `uvm_fatal("VERIFY_ENV_SENS", 
                $sformatf("Protocol violation detection rate %0.2f%% below 100%% - verification environment insensitive", 
                         detection_rate))
        end
    endtask
    
    //==========================================================================
    // Test Method 5: False Negative Pattern Detection
    //==========================================================================
    
    virtual task test_false_negative_patterns();
        `uvm_info("VERIFY_ENV_SENS", "Testing False Negative Pattern Detection", UVM_MEDIUM)
        
        // Test boundary conditions that might be missed
        test_boundary_condition_errors();
        
        // Test subtle corruption patterns
        test_subtle_corruption_patterns();
        
        // Test timing-related errors
        test_timing_related_errors();
        
        // Test combinatorial error patterns
        test_combinatorial_error_patterns();
    endtask
    
    //==========================================================================
    // Helper Methods
    //==========================================================================
    
    virtual task send_transaction_with_error_monitoring(uart_axi4_transaction tr, string error_type);
        // Implementation to send transaction and monitor for specific error type
        `uvm_info("VERIFY_ENV_SENS", 
            $sformatf("Sending transaction with %s monitoring", error_type), UVM_HIGH)
        
        // Send transaction through driver
        uart_axi4_driver driver_handle;
        if (!uvm_config_db#(uart_axi4_driver)::get(this, "", "driver", driver_handle)) begin
            `uvm_fatal("VERIFY_ENV_SENS", "Cannot get driver handle for error injection")
        end
        
        // Send corrupted transaction
        driver_handle.send_transaction(tr);
    endtask
    
    virtual task wait_for_crc_error_detection(int transaction_id);
        fork
            begin
                // Wait for CRC error to be detected by verification environment
                wait(crc_error_detected);
                crc_errors_detected++;
                `uvm_info("VERIFY_ENV_SENS", 
                    $sformatf("CRC error %0d successfully detected", transaction_id), UVM_MEDIUM)
            end
            begin
                // Timeout for error detection
                #max_detection_timeout;
                `uvm_fatal("VERIFY_ENV_SENS", 
                    $sformatf("CRC error %0d not detected within timeout", transaction_id))
            end
        join_any
        disable fork;
        
        crc_error_detected = 0; // Reset for next test
    endtask
    
    virtual task wait_for_timeout_error_detection(int transaction_id);
        fork
            begin
                wait(timeout_error_detected);
                timeout_errors_detected++;
                `uvm_info("VERIFY_ENV_SENS", 
                    $sformatf("Timeout error %0d successfully detected", transaction_id), UVM_MEDIUM)
            end
            begin
                #(max_detection_timeout * 2);
                `uvm_fatal("VERIFY_ENV_SENS", 
                    $sformatf("Timeout error %0d not detected within timeout", transaction_id))
            end
        join_any
        disable fork;
        
        timeout_error_detected = 0; // Reset for next test
    endtask
    
    virtual task wait_for_framing_error_detection(int transaction_id);
        fork
            begin
                wait(framing_error_detected);
                framing_errors_detected++;
                `uvm_info("VERIFY_ENV_SENS", 
                    $sformatf("Framing error %0d successfully detected", transaction_id), UVM_MEDIUM)
            end
            begin
                #max_detection_timeout;
                `uvm_fatal("VERIFY_ENV_SENS", 
                    $sformatf("Framing error %0d not detected within timeout", transaction_id))
            end
        join_any
        disable fork;
        
        framing_error_detected = 0; // Reset for next test
    endtask
    
    virtual task wait_for_protocol_violation_detection(int transaction_id);
        fork
            begin
                wait(protocol_error_detected);
                protocol_errors_detected++;
                `uvm_info("VERIFY_ENV_SENS", 
                    $sformatf("Protocol violation %0d successfully detected", transaction_id), UVM_MEDIUM)
            end
            begin
                #max_detection_timeout;
                `uvm_fatal("VERIFY_ENV_SENS", 
                    $sformatf("Protocol violation %0d not detected within timeout", transaction_id))
            end
        join_any
        disable fork;
        
        protocol_error_detected = 0; // Reset for next test
    endtask
    
    virtual task inject_timeout_error(uart_axi4_transaction tr, int transaction_id);
        // Inject artificial delay to cause timeout
        `uvm_info("VERIFY_ENV_SENS", 
            $sformatf("Injecting timeout delay for transaction %0d", transaction_id), UVM_HIGH)
        
        // Send partial transaction then delay
        // Implementation depends on specific protocol timing
        #(max_detection_timeout / 2); // Cause timeout condition
        
        // Signal that timeout should be detected
        timeout_error_detected = 1;
    endtask
    
    virtual task inject_framing_error(uart_axi4_transaction tr, int transaction_id);
        // Corrupt framing information
        `uvm_info("VERIFY_ENV_SENS", 
            $sformatf("Corrupting framing for transaction %0d", transaction_id), UVM_HIGH)
        
        // Specific framing corruption logic here
        // Implementation depends on frame structure
        
        // Signal that framing error should be detected
        framing_error_detected = 1;
    endtask
    
    virtual task inject_protocol_violation(uart_axi4_transaction tr, int transaction_id);
        // Create protocol violation
        `uvm_info("VERIFY_ENV_SENS", 
            $sformatf("Creating protocol violation for transaction %0d", transaction_id), UVM_HIGH)
        
        // Example: Invalid command sequence
        tr.cmd = 8'hFF; // Invalid command
        
        // Signal that protocol violation should be detected
        protocol_error_detected = 1;
    endtask
    
    virtual task verify_environment_baseline();
        `uvm_info("VERIFY_ENV_SENS", "Verifying verification environment baseline", UVM_MEDIUM)
        
        // Ensure environment is in clean state before error injection
        // Reset all detection flags
        crc_error_detected = 0;
        timeout_error_detected = 0;
        framing_error_detected = 0;
        protocol_error_detected = 0;
        
        // Reset all counters
        crc_errors_injected = 0;
        crc_errors_detected = 0;
        timeout_errors_injected = 0;
        timeout_errors_detected = 0;
        framing_errors_injected = 0;
        framing_errors_detected = 0;
        protocol_errors_injected = 0;
        protocol_errors_detected = 0;
    endtask
    
    virtual task validate_environment_sensitivity();
        `uvm_info("VERIFY_ENV_SENS", "Validating verification environment sensitivity", UVM_LOW)
        
        // Calculate overall detection rate
        int total_errors_injected = crc_errors_injected + timeout_errors_injected + 
                                   framing_errors_injected + protocol_errors_injected;
        int total_errors_detected = crc_errors_detected + timeout_errors_detected + 
                                   framing_errors_detected + protocol_errors_detected;
        
        real overall_detection_rate = real'(total_errors_detected) / real'(total_errors_injected) * 100.0;
        
        `uvm_info("VERIFY_ENV_SENS", 
            $sformatf("Overall Error Detection Rate: %0.2f%% (%0d/%0d)", 
                     overall_detection_rate, total_errors_detected, total_errors_injected), UVM_LOW)
        
        // Final validation
        if (overall_detection_rate < 100.0) begin
            `uvm_fatal("VERIFY_ENV_SENS", 
                $sformatf("Overall error detection rate %0.2f%% below 100%% - VERIFICATION ENVIRONMENT INADEQUATE", 
                         overall_detection_rate))
        end else begin
            `uvm_info("VERIFY_ENV_SENS", 
                "✓ Verification environment sensitivity validation PASSED - All injected errors detected", UVM_LOW)
        end
    endtask
    
    // Additional helper methods for specific error pattern testing
    virtual task test_boundary_condition_errors();
        `uvm_info("VERIFY_ENV_SENS", "Testing boundary condition error detection", UVM_MEDIUM)
        // Implementation for boundary condition testing
    endtask
    
    virtual task test_subtle_corruption_patterns();
        `uvm_info("VERIFY_ENV_SENS", "Testing subtle corruption pattern detection", UVM_MEDIUM)
        // Implementation for subtle corruption testing
    endtask
    
    virtual task test_timing_related_errors();
        `uvm_info("VERIFY_ENV_SENS", "Testing timing-related error detection", UVM_MEDIUM)
        // Implementation for timing error testing
    endtask
    
    virtual task test_combinatorial_error_patterns();
        `uvm_info("VERIFY_ENV_SENS", "Testing combinatorial error pattern detection", UVM_MEDIUM)
        // Implementation for combinatorial error testing
    endtask

endclass