`timescale 1ns / 1ps

// Advanced Transaction Correlation Engine for UART-AXI4 Bridge
// Created: October 11, 2025
// Purpose: Sophisticated correlation algorithms with timing analysis

// Correlation record for tracking transaction relationships
class uart_axi4_correlation_record extends uvm_object;
    
    `uvm_object_utils(uart_axi4_correlation_record)
    
    // Transaction references
    uart_frame_transaction uart_tr;
    axi4_lite_transaction axi_tr;
    
    // Correlation metadata
    string correlation_id;          // Unique identifier for correlation
    time uart_timestamp;            // When UART transaction was received
    time axi_timestamp;             // When AXI transaction was observed
    time correlation_latency;       // Time between UART and AXI
    
    // Correlation quality metrics
    real correlation_confidence;    // 0.0 to 1.0 confidence level
    string correlation_basis;       // Reason for correlation (addr_match, timing, etc)
    
    // Transaction state tracking
    typedef enum {
        PENDING_CORRELATION,        // UART received, waiting for AXI
        CORRELATED,                // Successfully correlated
        TIMEOUT_EXPIRED,           // Correlation timeout exceeded
        MISMATCH_DETECTED,         // Correlation attempted but failed
        ORPHANED                   // No matching transaction found
    } correlation_state_t;
    
    correlation_state_t state;
    
    // Error analysis
    bit has_protocol_error;
    bit has_timing_violation;
    bit has_data_mismatch;
    string error_description;
    
    function new(string name = "uart_axi4_correlation_record");
        super.new(name);
        correlation_confidence = 0.0;
        state = PENDING_CORRELATION;
        has_protocol_error = 1'b0;
        has_timing_violation = 1'b0;
        has_data_mismatch = 1'b0;
        uart_timestamp = 0;
        axi_timestamp = 0;
        correlation_latency = 0;
    endfunction
    
    // Calculate correlation confidence based on multiple factors
    function real calculate_confidence();
        real addr_match_score = 0.0;
        real timing_score = 0.0;
        real cmd_consistency_score = 0.0;
        real data_consistency_score = 0.0;
        
        if (uart_tr != null && axi_tr != null) begin
            // Address matching (40% weight)
            if (uart_tr.addr == axi_tr.addr) begin
                addr_match_score = 0.4;
            end else if ((uart_tr.addr & 32'hFFFFFFFC) == (axi_tr.addr & 32'hFFFFFFFC)) begin
                // Word-aligned addresses
                addr_match_score = 0.3;
            end
            
            // Timing correlation (30% weight)
            if (correlation_latency < 1000000) begin // < 1ms
                timing_score = 0.3;
            end else if (correlation_latency < 10000000) begin // < 10ms
                timing_score = 0.2;
            end else begin
                timing_score = 0.1;
            end
            
            // Command consistency (20% weight)
            if ((uart_tr.cmd[0] == 1'b0 && axi_tr.trans_type == AXI_READ) ||
                (uart_tr.cmd[0] == 1'b1 && axi_tr.trans_type == AXI_WRITE)) begin
                cmd_consistency_score = 0.2;
            end
            
            // Data consistency for writes (10% weight)
            if (axi_tr.trans_type == AXI_WRITE && uart_tr.data.size() > 0) begin
                // Check if data patterns match
                logic [31:0] uart_data_word = 0;
                for (int i = 0; i < uart_tr.data.size() && i < 4; i++) begin
                    uart_data_word[i*8 +: 8] = uart_tr.data[i];
                end
                if (uart_data_word == axi_tr.wdata) begin
                    data_consistency_score = 0.1;
                end else begin
                    data_consistency_score = 0.05;
                end
            end else if (axi_tr.trans_type == AXI_READ) begin
                data_consistency_score = 0.1; // No data to check for reads
            end
        end
        
        correlation_confidence = addr_match_score + timing_score + cmd_consistency_score + data_consistency_score;
        return correlation_confidence;
    endfunction
    
    // Generate detailed correlation report
    function string get_correlation_report();
        string report;
        report = $sformatf("Correlation Record: %s\n", correlation_id);
        report = {report, $sformatf("  State: %s\n", state.name())};
        report = {report, $sformatf("  Confidence: %.2f\n", correlation_confidence)};
        report = {report, $sformatf("  Basis: %s\n", correlation_basis)};
        report = {report, $sformatf("  Latency: %0t ns\n", correlation_latency)};
        
        if (uart_tr != null) begin
            report = {report, $sformatf("  UART: CMD=0x%02X ADDR=0x%08X @%0t\n", 
                     uart_tr.cmd, uart_tr.addr, uart_timestamp)};
        end
        
        if (axi_tr != null) begin
            report = {report, $sformatf("  AXI: %s ADDR=0x%08X @%0t\n", 
                     (axi_tr.trans_type == AXI_WRITE) ? "WRITE" : "READ", 
                     axi_tr.addr, axi_timestamp)};
        end
        
        if (has_protocol_error || has_timing_violation || has_data_mismatch) begin
            report = {report, $sformatf("  ERRORS: %s\n", error_description)};
        end
        
        return report;
    endfunction
    
endclass : uart_axi4_correlation_record

// Advanced Correlation Engine with sophisticated algorithms
class uart_axi4_correlation_engine extends uvm_object;
    
    `uvm_object_utils(uart_axi4_correlation_engine)
    
    // Configuration parameters
    time correlation_timeout;          // Maximum time to wait for correlation
    real minimum_confidence_threshold; // Minimum confidence to accept correlation
    int max_pending_transactions;      // Maximum pending correlations
    
    // Active correlation tracking
    uart_axi4_correlation_record pending_correlations[$];
    uart_axi4_correlation_record completed_correlations[$];
    
    // Performance metrics
    int total_correlations_attempted;
    int successful_correlations;
    int timeout_correlations;
    int failed_correlations;
    
    // Timing analysis
    time min_latency;
    time max_latency;
    time total_latency;
    
    function new(string name = "uart_axi4_correlation_engine");
        super.new(name);
        correlation_timeout = 100000000; // 100ms default
        minimum_confidence_threshold = 0.7;
        max_pending_transactions = 50;
        
        // Initialize metrics
        total_correlations_attempted = 0;
        successful_correlations = 0;
        timeout_correlations = 0;
        failed_correlations = 0;
        min_latency = 1000000000; // 1 second (will be reduced)
        max_latency = 0;
        total_latency = 0;
    endfunction
    
    // Add UART transaction for correlation
    function uart_axi4_correlation_record start_correlation(uart_frame_transaction uart_tr);
        uart_axi4_correlation_record record;
        string correlation_id;
        
        // Generate unique correlation ID
        correlation_id = $sformatf("CORR_%0t_%02X_%08X", $time, uart_tr.cmd, uart_tr.addr);
        
        record = uart_axi4_correlation_record::type_id::create(correlation_id);
        record.correlation_id = correlation_id;
        record.uart_tr = uart_tr;
        record.uart_timestamp = $time;
        record.state = uart_axi4_correlation_record::PENDING_CORRELATION;
        
        pending_correlations.push_back(record);
        total_correlations_attempted++;
        
        `uvm_info("CORRELATION_ENGINE", 
                 $sformatf("Started correlation %s for UART CMD=0x%02X ADDR=0x%08X", 
                          correlation_id, uart_tr.cmd, uart_tr.addr), UVM_HIGH)
        
        return record;
    endfunction
    
    // Attempt to correlate AXI transaction with pending UART transactions
    function uart_axi4_correlation_record correlate_axi_transaction(axi4_lite_transaction axi_tr);
        uart_axi4_correlation_record best_match;
        real best_confidence = 0.0;
        int best_index = -1;
        
        // Search through pending correlations for best match
        for (int i = 0; i < pending_correlations.size(); i++) begin
            uart_axi4_correlation_record candidate = pending_correlations[i];
            
            if (candidate.state != uart_axi4_correlation_record::PENDING_CORRELATION) continue;
            
            // Set AXI transaction and calculate confidence
            candidate.axi_tr = axi_tr;
            candidate.axi_timestamp = $time;
            candidate.correlation_latency = $time - candidate.uart_timestamp;
            
            real confidence = candidate.calculate_confidence();
            
            // Check if this is the best match so far
            if (confidence > best_confidence && confidence >= minimum_confidence_threshold) begin
                best_confidence = confidence;
                best_match = candidate;
                best_index = i;
            end
        end
        
        // If we found a good match, complete the correlation
        if (best_match != null) begin
            best_match.state = uart_axi4_correlation_record::CORRELATED;
            best_match.correlation_basis = $sformatf("addr_timing_match_%.2f", best_confidence);
            
            // Update timing statistics
            update_timing_statistics(best_match.correlation_latency);
            
            // Move to completed correlations
            pending_correlations.delete(best_index);
            completed_correlations.push_back(best_match);
            successful_correlations++;
            
            `uvm_info("CORRELATION_ENGINE", 
                     $sformatf("Completed correlation %s with confidence %.2f", 
                              best_match.correlation_id, best_confidence), UVM_MEDIUM)
        end else begin
            `uvm_info("CORRELATION_ENGINE", 
                     $sformatf("No correlation found for AXI %s ADDR=0x%08X (searched %0d pending)", 
                              (axi_tr.trans_type == AXI_WRITE) ? "WRITE" : "READ", 
                              axi_tr.addr, pending_correlations.size()), UVM_HIGH)
        end
        
        return best_match;
    endfunction
    
    // Check for timeout correlations and clean up
    function void check_timeouts();
        time current_time = $time;
        
        for (int i = pending_correlations.size() - 1; i >= 0; i--) begin
            uart_axi4_correlation_record record = pending_correlations[i];
            
            if ((current_time - record.uart_timestamp) > correlation_timeout) begin
                record.state = uart_axi4_correlation_record::TIMEOUT_EXPIRED;
                record.error_description = "Correlation timeout exceeded";
                
                pending_correlations.delete(i);
                completed_correlations.push_back(record);
                timeout_correlations++;
                
                `uvm_warning("CORRELATION_ENGINE", 
                           $sformatf("Correlation %s timed out after %0t ns", 
                                    record.correlation_id, current_time - record.uart_timestamp))
            end
        end
    endfunction
    
    // Update timing statistics
    function void update_timing_statistics(time latency);
        if (latency < min_latency) min_latency = latency;
        if (latency > max_latency) max_latency = latency;
        total_latency += latency;
    endfunction
    
    // Generate comprehensive correlation report
    function string get_correlation_statistics();
        string report;
        real success_rate = 0.0;
        time avg_latency = 0;
        
        if (total_correlations_attempted > 0) begin
            success_rate = real'(successful_correlations) / real'(total_correlations_attempted) * 100.0;
        end
        
        if (successful_correlations > 0) begin
            avg_latency = total_latency / successful_correlations;
        end
        
        report = "=== CORRELATION ENGINE STATISTICS ===\n";
        report = {report, $sformatf("Total Attempted: %0d\n", total_correlations_attempted)};
        report = {report, $sformatf("Successful: %0d (%.1f%%)\n", successful_correlations, success_rate)};
        report = {report, $sformatf("Timeouts: %0d\n", timeout_correlations)};
        report = {report, $sformatf("Failed: %0d\n", failed_correlations)};
        report = {report, $sformatf("Pending: %0d\n", pending_correlations.size())};
        report = {report, $sformatf("Latency - Min: %0t ns, Max: %0t ns, Avg: %0t ns\n", 
                 min_latency, max_latency, avg_latency)};
        
        return report;
    endfunction
    
    // Advanced diagnostic capabilities
    function void diagnose_correlation_issues();
        `uvm_info("CORRELATION_DIAGNOSTICS", get_correlation_statistics(), UVM_LOW)
        
        // Analyze pending transactions for patterns
        if (pending_correlations.size() > max_pending_transactions / 2) begin
            `uvm_warning("CORRELATION_ENGINE", 
                        $sformatf("High number of pending correlations: %0d", 
                                 pending_correlations.size()))
        end
        
        // Check for address patterns in failures
        analyze_failure_patterns();
    endfunction
    
    // Analyze failure patterns for debugging
    function void analyze_failure_patterns();
        logic [31:0] failed_addresses[$];
        
        foreach (completed_correlations[i]) begin
            if (completed_correlations[i].state == uart_axi4_correlation_record::TIMEOUT_EXPIRED) begin
                failed_addresses.push_back(completed_correlations[i].uart_tr.addr);
            end
        end
        
        if (failed_addresses.size() > 3) begin
            `uvm_info("CORRELATION_DIAGNOSTICS", 
                     $sformatf("Found %0d failed correlations, investigating patterns...", 
                              failed_addresses.size()), UVM_MEDIUM)
        end
    endfunction
    
endclass : uart_axi4_correlation_engine