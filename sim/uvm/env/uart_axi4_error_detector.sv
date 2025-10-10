`timescale 1ns / 1ps

// Phase 3 Advanced Error Detection System
// Created: October 11, 2025
// Purpose: Predictive error analysis and anomaly detection

class uart_axi4_error_detector extends uvm_object;
    
    `uvm_object_utils(uart_axi4_error_detector)
    
    // Error detection configuration
    typedef struct {
        int max_latency_threshold;      // Maximum acceptable latency (ns)
        int error_burst_threshold;      // Max consecutive errors before alarm
        real efficiency_threshold;      // Minimum efficiency percentage
        int timeout_threshold;          // Transaction timeout (ns)
        int pipeline_depth_limit;       // Maximum pipeline depth
    } error_thresholds_t;
    
    error_thresholds_t thresholds;
    
    // Error tracking structures
    typedef struct {
        time timestamp;
        string error_type;
        string description;
        uart_frame_transaction transaction;
        int severity; // 1=Info, 2=Warning, 3=Error, 4=Fatal
    } error_event_t;
    
    error_event_t error_history[$];
    
    // Pattern analysis
    typedef struct {
        string pattern_name;
        int occurrence_count;
        time last_occurrence;
        real frequency; // errors per second
    } error_pattern_t;
    
    error_pattern_t error_patterns[string];
    
    // Predictive analysis state
    typedef struct {
        real error_rate_trend;          // Increasing/decreasing error rate
        int predicted_errors_next_1ms;  // Predicted errors in next 1ms
        string risk_level;              // LOW, MEDIUM, HIGH, CRITICAL
        string[] recommended_actions;    // Suggested mitigation actions
    } prediction_result_t;
    
    // Statistics tracking
    int total_transactions;
    int total_errors;
    time analysis_start_time;
    time last_analysis_time;
    
    // Constructor
    function new(string name = "uart_axi4_error_detector");
        super.new(name);
        
        // Set default thresholds
        thresholds.max_latency_threshold = 1000000; // 1ms
        thresholds.error_burst_threshold = 5;
        thresholds.efficiency_threshold = 70.0;
        thresholds.timeout_threshold = 2000000; // 2ms
        thresholds.pipeline_depth_limit = 16;
        
        analysis_start_time = $time;
        
        `uvm_info("ERROR_DETECTOR", "Advanced error detection system initialized", UVM_LOW)
    endfunction
    
    // Configure thresholds
    function void configure_thresholds(error_thresholds_t new_thresholds);
        thresholds = new_thresholds;
        `uvm_info("ERROR_DETECTOR", "Error detection thresholds updated", UVM_LOW)
    endfunction
    
    // Main error analysis function
    function prediction_result_t analyze_transaction(uart_frame_transaction tr, 
                                                   correlation_record_t corr_record);
        prediction_result_t result;
        error_event_t error_event;
        string detected_errors[$];
        
        total_transactions++;
        
        // 1. Latency Analysis
        if (corr_record.valid && corr_record.correlation_latency > thresholds.max_latency_threshold) begin
            error_event = create_error_event("LATENCY_VIOLATION", 
                                            $sformatf("Correlation latency %0d ns exceeds threshold %0d ns",
                                                    corr_record.correlation_latency, 
                                                    thresholds.max_latency_threshold),
                                            tr, 2);
            log_error(error_event);
            detected_errors.push_back("LATENCY_VIOLATION");
        end
        
        // 2. Response Status Analysis
        if (tr.response_status != STATUS_OK) begin
            string error_desc = get_status_description(tr.response_status);
            error_event = create_error_event("RESPONSE_ERROR", error_desc, tr, 3);
            log_error(error_event);
            detected_errors.push_back("RESPONSE_ERROR");
            total_errors++;
        end
        
        // 3. Efficiency Analysis
        real efficiency = calculate_efficiency(tr);
        if (efficiency < thresholds.efficiency_threshold) begin
            error_event = create_error_event("LOW_EFFICIENCY", 
                                            $sformatf("Data efficiency %.1f%% below threshold %.1f%%",
                                                    efficiency, thresholds.efficiency_threshold),
                                            tr, 2);
            log_error(error_event);
            detected_errors.push_back("LOW_EFFICIENCY");
        end
        
        // 4. Correlation Success Analysis
        if (corr_record.valid && !corr_record.correlation_success) begin
            error_event = create_error_event("CORRELATION_FAILURE", 
                                            "Failed to correlate UART transaction with AXI response",
                                            tr, 3);
            log_error(error_event);
            detected_errors.push_back("CORRELATION_FAILURE");
        end
        
        // 5. Burst Pattern Analysis
        if (tr.cmd[6] && (tr.cmd[3:0] == 0)) begin // Increment mode but no burst
            error_event = create_error_event("SUBOPTIMAL_BURST", 
                                            "Using increment mode without burst benefit",
                                            tr, 1);
            log_error(error_event);
            detected_errors.push_back("SUBOPTIMAL_BURST");
        end
        
        // Update pattern analysis
        update_error_patterns(detected_errors);
        
        // Generate prediction
        result = generate_prediction();
        
        last_analysis_time = $time;
        
        return result;
    endfunction
    
    // Create error event structure
    function error_event_t create_error_event(string error_type, string description, 
                                            uart_frame_transaction tr, int severity);
        error_event_t event;
        event.timestamp = $time;
        event.error_type = error_type;
        event.description = description;
        event.transaction = tr;
        event.severity = severity;
        return event;
    endfunction
    
    // Log error to history
    function void log_error(error_event_t error_event);
        error_history.push_back(error_event);
        
        // Limit history size
        if (error_history.size() > 1000) begin
            error_history.pop_front();
        end
        
        // Report based on severity
        case (error_event.severity)
            1: `uvm_info("ERROR_DETECTOR", 
                        $sformatf("[%s] %s", error_event.error_type, error_event.description), UVM_HIGH)
            2: `uvm_warning("ERROR_DETECTOR", 
                          $sformatf("[%s] %s", error_event.error_type, error_event.description))
            3: `uvm_error("ERROR_DETECTOR", 
                         $sformatf("[%s] %s", error_event.error_type, error_event.description))
            4: `uvm_fatal("ERROR_DETECTOR", 
                         $sformatf("[%s] %s", error_event.error_type, error_event.description))
        endcase
    endfunction
    
    // Update error pattern tracking
    function void update_error_patterns(string detected_errors[$]);
        foreach (detected_errors[i]) begin
            string error_type = detected_errors[i];
            
            if (error_patterns.exists(error_type)) begin
                error_patterns[error_type].occurrence_count++;
                error_patterns[error_type].last_occurrence = $time;
            end else begin
                error_pattern_t new_pattern;
                new_pattern.pattern_name = error_type;
                new_pattern.occurrence_count = 1;
                new_pattern.last_occurrence = $time;
                new_pattern.frequency = 0.0;
                error_patterns[error_type] = new_pattern;
            end
            
            // Calculate frequency (errors per second)
            if ($time > analysis_start_time) begin
                real time_elapsed_sec = ($time - analysis_start_time) / 1e9;
                error_patterns[error_type].frequency = 
                    error_patterns[error_type].occurrence_count / time_elapsed_sec;
            end
        end
    endfunction
    
    // Generate predictive analysis
    function prediction_result_t generate_prediction();
        prediction_result_t result;
        real current_error_rate;
        real recent_error_rate;
        int high_severity_errors = 0;
        
        // Calculate current error rate
        if (total_transactions > 0) begin
            current_error_rate = (real'(total_errors) / real'(total_transactions)) * 100.0;
        end else begin
            current_error_rate = 0.0;
        end
        
        // Calculate recent error rate (last 100 transactions)
        int recent_window = (total_transactions < 100) ? total_transactions : 100;
        int recent_errors = 0;
        
        for (int i = error_history.size() - recent_window; i < error_history.size(); i++) begin
            if (i >= 0 && error_history[i].severity >= 3) begin
                recent_errors++;
                if (error_history[i].severity >= 3) high_severity_errors++;
            end
        end
        
        if (recent_window > 0) begin
            recent_error_rate = (real'(recent_errors) / real'(recent_window)) * 100.0;
        end else begin
            recent_error_rate = 0.0;
        end
        
        // Calculate trend
        result.error_rate_trend = recent_error_rate - current_error_rate;
        
        // Predict errors in next 1ms
        if (error_patterns.size() > 0) begin
            real avg_frequency = 0.0;
            foreach (error_patterns[pattern]) begin
                avg_frequency += error_patterns[pattern].frequency;
            end
            avg_frequency /= error_patterns.size();
            result.predicted_errors_next_1ms = int'(avg_frequency * 0.001); // 1ms = 0.001s
        end else begin
            result.predicted_errors_next_1ms = 0;
        end
        
        // Determine risk level
        if (high_severity_errors > 5 || recent_error_rate > 20.0) begin
            result.risk_level = "CRITICAL";
            result.recommended_actions = {
                "IMMEDIATE: Stop test execution and investigate",
                "Check DUT configuration and reset state",
                "Analyze error patterns for systematic issues"
            };
        end else if (recent_error_rate > 10.0 || result.error_rate_trend > 5.0) begin
            result.risk_level = "HIGH";
            result.recommended_actions = {
                "Reduce test intensity",
                "Monitor error patterns closely",
                "Consider DUT parameter adjustments"
            };
        end else if (recent_error_rate > 5.0 || result.error_rate_trend > 2.0) begin
            result.risk_level = "MEDIUM";
            result.recommended_actions = {
                "Continue monitoring",
                "Review recent error patterns",
                "Prepare contingency actions"
            };
        end else begin
            result.risk_level = "LOW";
            result.recommended_actions = {
                "Continue normal operation",
                "Maintain current monitoring level"
            };
        end
        
        return result;
    endfunction
    
    // Calculate transaction efficiency
    function real calculate_efficiency(uart_frame_transaction tr);
        int useful_bytes = (tr.cmd[3:0] + 1) * (1 << tr.cmd[5:4]);
        int total_bytes = 8 + useful_bytes; // 8 bytes overhead
        return (real'(useful_bytes) / real'(total_bytes)) * 100.0;
    endfunction
    
    // Get human-readable status description
    function string get_status_description(status_t status);
        case (status)
            STATUS_OK: return "No error";
            STATUS_CRC_ERR: return "CRC checksum error";
            STATUS_CMD_INV: return "Invalid command";
            STATUS_ADDR_ALIGN: return "Address alignment error";
            STATUS_LEN_RANGE: return "Length out of range";
            STATUS_TIMEOUT: return "Transaction timeout";
            STATUS_AXI_SLVERR: return "AXI slave error";
            STATUS_BUSY: return "System busy";
            default: return "Unknown error";
        endcase
    endfunction
    
    // Burst error detection analysis
    function void analyze_error_burst();
        int consecutive_errors = 0;
        int max_consecutive = 0;
        
        // Count consecutive errors
        for (int i = error_history.size()-1; i >= 0; i--) begin
            if (error_history[i].severity >= 3) begin
                consecutive_errors++;
            end else begin
                if (consecutive_errors > max_consecutive) begin
                    max_consecutive = consecutive_errors;
                end
                consecutive_errors = 0;
            end
        end
        
        if (consecutive_errors > thresholds.error_burst_threshold) begin
            `uvm_error("ERROR_DETECTOR", 
                      $sformatf("Error burst detected: %0d consecutive errors exceeds threshold %0d",
                              consecutive_errors, thresholds.error_burst_threshold))
        end
    endfunction
    
    // Generate comprehensive error report
    function void generate_error_report();
        `uvm_info("ERROR_DETECTOR", "=== ADVANCED ERROR DETECTION REPORT ===", UVM_LOW)
        `uvm_info("ERROR_DETECTOR", $sformatf("Total Transactions: %0d", total_transactions), UVM_LOW)
        `uvm_info("ERROR_DETECTOR", $sformatf("Total Errors: %0d", total_errors), UVM_LOW)
        
        if (total_transactions > 0) begin
            real error_rate = (real'(total_errors) / real'(total_transactions)) * 100.0;
            `uvm_info("ERROR_DETECTOR", $sformatf("Overall Error Rate: %.2f%%", error_rate), UVM_LOW)
        end
        
        `uvm_info("ERROR_DETECTOR", "Error Pattern Analysis:", UVM_LOW)
        foreach (error_patterns[pattern]) begin
            `uvm_info("ERROR_DETECTOR", 
                     $sformatf("  %s: %0d occurrences, %.3f errors/sec", 
                             pattern, 
                             error_patterns[pattern].occurrence_count,
                             error_patterns[pattern].frequency), UVM_LOW)
        end
        
        prediction_result_t prediction = generate_prediction();
        `uvm_info("ERROR_DETECTOR", $sformatf("Current Risk Level: %s", prediction.risk_level), UVM_LOW)
        `uvm_info("ERROR_DETECTOR", $sformatf("Predicted Errors (next 1ms): %0d", 
                 prediction.predicted_errors_next_1ms), UVM_LOW)
        
        foreach (prediction.recommended_actions[i]) begin
            `uvm_info("ERROR_DETECTOR", $sformatf("Recommendation: %s", 
                     prediction.recommended_actions[i]), UVM_LOW)
        end
    endfunction
    
endclass : uart_axi4_error_detector