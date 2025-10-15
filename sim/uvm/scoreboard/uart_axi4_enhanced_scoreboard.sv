// Enhanced UVM Scoreboard with DUT Internal State Monitoring
// Implements QA-2.1: Advanced transaction tracking and DUT response monitoring
// Author: QA Framework - FastMCP v2.0
// Date: 2025-10-14

`timescale 1ns / 1ps

import uvm_pkg::*;
import uart_axi4_test_pkg::*;
`include "uvm_macros.svh"

class uart_axi4_enhanced_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(uart_axi4_enhanced_scoreboard)

    // Transaction Analysis Ports
    uvm_analysis_imp_uart #(uart_frame_transaction, uart_axi4_enhanced_scoreboard) uart_ap;
    uvm_analysis_imp_axi #(axi4_lite_transaction, uart_axi4_enhanced_scoreboard) axi_ap;
    uvm_analysis_imp_dut #(dut_internal_transaction, uart_axi4_enhanced_scoreboard) dut_ap;

    // Enhanced Statistics for QA-2.1
    int unsigned uart_transactions_received;
    int unsigned axi_transactions_received;
    int unsigned dut_state_changes_received;
    int unsigned successful_matches;
    int unsigned timeout_errors;
    int unsigned protocol_violations;
    int unsigned zero_activity_errors;
    
    // Transaction Queues with Enhanced Tracking
    uart_frame_transaction uart_queue[$];
    axi4_lite_transaction axi_queue[$];
    dut_internal_transaction dut_queue[$];
    
    // Quality Metrics - Enhanced for QA-2.1
    time first_activity_time = 0;
    time last_uart_activity = 0;
    time last_axi_activity = 0;
    time last_dut_activity = 0;
    time longest_response_time = 0;
    bit activity_timeout_enabled = 1;
    time activity_timeout_threshold = 1000000ns;  // 1ms timeout for QA-2.1
    bit zero_activity_detected = 0;
    
    // Enhanced DUT Response Tracking
    typedef struct {
        time uart_frame_time;
        time axi_request_time;
        time axi_response_time;
        time uart_response_time;
        bit processing_complete;
        string frame_id;
    } response_tracking_entry;
    
    response_tracking_entry active_responses[string];  // Keyed by transaction ID
    
    // DUT State Tracking
    typedef enum {IDLE, RECEIVING, PROCESSING, RESPONDING, ERROR_STATE} dut_state_t;
    dut_state_t current_dut_state;
    dut_state_t previous_dut_state;
    
    // Constructor
    function new(string name = "uart_axi4_enhanced_scoreboard", uvm_component parent);
        super.new(name, parent);
        uart_ap = new("uart_ap", this);
        axi_ap = new("axi_ap", this);
        dut_ap = new("dut_ap", this);
    endfunction

    // Build Phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info(get_type_name(), "Enhanced Scoreboard Build Phase", UVM_LOW)
        
        // Initialize tracking variables - Enhanced for QA-2.1
        uart_transactions_received = 0;
        axi_transactions_received = 0;
        dut_state_changes_received = 0;
        successful_matches = 0;
        timeout_errors = 0;
        protocol_violations = 0;
        zero_activity_errors = 0;
        
        current_dut_state = IDLE;
        previous_dut_state = IDLE;
        
        first_activity_time = 0;
        last_uart_activity = 0;
        last_axi_activity = 0;
        last_dut_activity = 0;
        longest_response_time = 0;
        zero_activity_detected = 0;
    endfunction

    // UART Transaction Analysis - Enhanced for QA-2.1
    virtual function void write_uart(uart_frame_transaction t);
        string trans_id;
        
        uart_transactions_received++;
        uart_queue.push_back(t);
        last_uart_activity = $time;
        
        // Update global activity tracking
        update_activity_tracking();
        
        // Generate unique transaction ID for response tracking
        trans_id = $sformatf("UART_%08x_%02x_%0t", t.addr, t.cmd, $time);
        
        // Create response tracking entry
        active_responses[trans_id] = '{
            uart_frame_time: $time,
            axi_request_time: 0,
            axi_response_time: 0,
            uart_response_time: 0,
            processing_complete: 0,
            frame_id: trans_id
        };
        
        `uvm_info("ENHANCED_SB_UART", 
                  $sformatf("UART Transaction #%0d [%s]: cmd=0x%02x, addr=0x%08x, time=%0t", 
                           uart_transactions_received, trans_id, t.cmd, t.addr, $time), UVM_MEDIUM)
        
        // Enhanced Transaction Analysis
        analyze_uart_transaction(t);
        
        // Attempt matching with pending AXI transactions
        match_transactions();
    endfunction

    // AXI Transaction Analysis
    virtual function void write_axi(axi4_lite_transaction t);
        axi_transactions_received++;
        axi_queue.push_back(t);
        last_axi_activity = $time;
        
        `uvm_info("ENHANCED_SB_AXI", 
                  $sformatf("AXI Transaction #%0d: addr=0x%08x, wdata=0x%08x, time=%0t", 
                           axi_transactions_received, t.addr, t.wdata, $time), UVM_MEDIUM)
        
        // Enhanced Transaction Analysis
        analyze_axi_transaction(t);
        
        // Attempt matching with pending UART transactions
        match_transactions();
    endfunction

    function automatic bit string_contains(input string haystack, input string needle);
        int h_len;
        int n_len;

        n_len = needle.len();
        if (n_len == 0) begin
            return 1;
        end

        h_len = haystack.len();
        if (h_len < n_len) begin
            return 0;
        end

        for (int idx = 0; idx <= h_len - n_len; idx++) begin
            if (haystack.substr(idx, idx + n_len - 1) == needle) begin
                return 1;
            end
        end

        return 0;
    endfunction

    function automatic dut_state_t decode_dut_state(const ref dut_internal_transaction t);
        string info_lower;

        info_lower = t.state_info.tolower();
        if ((info_lower.len() > 0) && string_contains(info_lower, "error")) begin
            return ERROR_STATE;
        end

        unique case (t.transaction_type)
            UART_RX_DATA,
            FRAME_START_DETECTED: return RECEIVING;

            AXI_WRITE_ADDR,
            AXI_WRITE_DATA,
            AXI_READ_ADDR,
            AXI_READ_DATA,
            INTERNAL_STATE_CHANGE: return PROCESSING;

            AXI_WRITE_RESP,
            FRAME_COMPLETE: return RESPONDING;

            FIFO_STATUS_CHANGE: return current_dut_state;

            default: return IDLE;
        endcase
    endfunction

    // DUT Internal State Analysis (NEW in QA-2.1)
    virtual function void write_dut(dut_internal_transaction t);
        dut_state_changes_received++;
        dut_queue.push_back(t);
        last_dut_activity = $time;
        
        previous_dut_state = current_dut_state;
        current_dut_state = decode_dut_state(t);
        
        `uvm_info("ENHANCED_SB_DUT", 
                  $sformatf("DUT State Change #%0d: %s -> %s, fifo_count=%0d, time=%0t", 
                           dut_state_changes_received, 
                           previous_dut_state.name(), current_dut_state.name(), 
                           t.fifo_level, $time), UVM_MEDIUM)
        
        // Protocol compliance checking
        check_dut_state_transition();
        
        // Activity timeout detection
        check_activity_timeout();
    endfunction

    // QA-2.1 Enhanced Activity Tracking
    function void update_activity_tracking();
        if (first_activity_time == 0) first_activity_time = $time;
        // Reset zero activity detection on any activity
        zero_activity_detected = 0;
    endfunction

    // QA-2.1 Response Tracking for AXI Transactions
    function void update_response_tracking_axi(axi4_lite_transaction t);
        // Find matching UART transaction based on address correlation
        foreach (active_responses[trans_id]) begin
            response_tracking_entry entry = active_responses[trans_id];
            if (!entry.processing_complete && entry.axi_request_time == 0) begin
                // Update AXI timing for this response chain
                if (t.trans_kind == AXI_WRITE || t.trans_kind == AXI_READ) begin
                    entry.axi_request_time = $time;
                    active_responses[trans_id] = entry;
                    
                    `uvm_info("ENHANCED_SB_TRACK", 
                              $sformatf("AXI Request tracked for [%s]: addr=0x%08x at %0t", 
                                       trans_id, t.addr, $time), UVM_HIGH)
                end
                break;
            end
        end
    endfunction

    // QA-2.1 Zero Activity Detection
    function void check_zero_activity();
        int total_activity = uart_transactions_received + axi_transactions_received + dut_state_changes_received;
        
        if (total_activity == 0) begin
            zero_activity_detected = 1;
            zero_activity_errors++;
            `uvm_error("ENHANCED_SB_QA", "ZERO ACTIVITY DETECTED: No transactions processed - verification invalid")
        end
    endfunction

    // QA-2.1 Response Time Analysis
    function void analyze_response_times();
        time response_time;
        
        foreach (active_responses[trans_id]) begin
            response_tracking_entry entry = active_responses[trans_id];
            if (entry.processing_complete && entry.uart_response_time > 0) begin
                response_time = entry.uart_response_time - entry.uart_frame_time;
                if (response_time > longest_response_time) begin
                    longest_response_time = response_time;
                end
                
                // Check for timeout violations
                if (response_time > activity_timeout_threshold) begin
                    timeout_errors++;
                    `uvm_warning("ENHANCED_SB_TIMEOUT", 
                                $sformatf("Response timeout for [%s]: %0t ns > %0t ns threshold", 
                                         trans_id, response_time, activity_timeout_threshold))
                end
            end
        end
    endfunction

    // Enhanced Transaction Matching Algorithm
    virtual function void match_transactions();
        if (uart_queue.size() > 0 && axi_queue.size() > 0) begin
            uart_frame_transaction uart_trans = uart_queue.pop_front();
            axi4_lite_transaction axi_trans = axi_queue.pop_front();
            
            // Enhanced matching with protocol validation
            if (validate_transaction_match(uart_trans, axi_trans)) begin
                successful_matches++;
                `uvm_info("ENHANCED_SB_MATCH", 
                          $sformatf("✅ Transaction Match #%0d: UART[cmd=0x%02x] <-> AXI[addr=0x%08x]", 
                                   successful_matches, uart_trans.cmd, axi_trans.addr), UVM_LOW)
            end else begin
                protocol_violations++;
                `uvm_error("ENHANCED_SB_MISMATCH", 
                           $sformatf("❌ Protocol Violation #%0d: UART[cmd=0x%02x] ≠ AXI[addr=0x%08x]", 
                                    protocol_violations, uart_trans.cmd, axi_trans.addr))
            end
        end
    endfunction

    // UART Transaction Analysis
    virtual function void analyze_uart_transaction(uart_frame_transaction t);
        // Validate UART frame structure
        if (t.start_delimiter != 8'hA5) begin
            protocol_violations++;
            `uvm_error("UART_FRAME_ERROR", 
                       $sformatf("Invalid UART start delimiter: expected 0xA5, got 0x%02x", 
                                t.start_delimiter))
        end
        
        // Check CRC if available
        if (t.crc_received != t.crc_calculated) begin
            protocol_violations++;
            `uvm_error("UART_CRC_ERROR", 
                       $sformatf("UART CRC mismatch: received=0x%02x, calculated=0x%02x", 
                                t.crc_received, t.crc_calculated))
        end
    endfunction

    // AXI Transaction Analysis
    virtual function void analyze_axi_transaction(axi4_lite_transaction t);
        logic [1:0] response;
        
        // Validate AXI4-Lite address alignment
        if (t.addr % 4 != 0) begin
            protocol_violations++;
            `uvm_error("AXI_ALIGNMENT_ERROR", 
                       $sformatf("AXI address not 32-bit aligned: 0x%08x", t.addr))
        end
        
        // Check response codes (use bresp for write, rresp for read)
        response = t.is_write ? t.bresp : t.rresp;
        if (response != 2'b00) begin // AXI_OKAY = 2'b00
            `uvm_warning("AXI_RESPONSE_WARNING", 
                         $sformatf("AXI response not OKAY: response=0x%0x", response))
        end
    endfunction

    // DUT State Transition Validation
    virtual function void check_dut_state_transition();
        bit valid_transition = 0;
        
        case ({previous_dut_state, current_dut_state})
            {IDLE, RECEIVING},
            {RECEIVING, PROCESSING},
            {PROCESSING, RESPONDING},
            {RESPONDING, IDLE},
            {IDLE, IDLE}: valid_transition = 1;
            
            // Error recovery transitions
            {ERROR_STATE, IDLE}: valid_transition = 1;
            
            default: valid_transition = 0;
        endcase
        
        if (!valid_transition) begin
            protocol_violations++;
            `uvm_error("DUT_STATE_ERROR", 
                       $sformatf("Invalid DUT state transition: %s -> %s", 
                                previous_dut_state.name(), current_dut_state.name()))
        end
    endfunction

    // Activity Timeout Detection
    virtual function void check_activity_timeout();
        time current_time = $time;
        
        if (activity_timeout_enabled) begin
            // Check for UART activity timeout
            if ((current_time - last_uart_activity) > activity_timeout_threshold && 
                uart_transactions_received > 0) begin
                timeout_errors++;
                `uvm_error("UART_TIMEOUT", 
                           $sformatf("UART activity timeout: no activity for %0t", 
                                    current_time - last_uart_activity))
            end
            
            // Check for AXI activity timeout
            if ((current_time - last_axi_activity) > activity_timeout_threshold && 
                axi_transactions_received > 0) begin
                timeout_errors++;
                `uvm_error("AXI_TIMEOUT", 
                           $sformatf("AXI activity timeout: no activity for %0t", 
                                    current_time - last_axi_activity))
            end
        end
    endfunction

    // Enhanced Transaction Validation
    virtual function bit validate_transaction_match(uart_frame_transaction uart_trans, 
                                                    axi4_lite_transaction axi_trans);
        // Command-to-address mapping validation
        case (uart_trans.cmd)
            8'h01: begin // READ command
                if (axi_trans.trans_kind != AXI_READ) return 0;
                return 1;
            end
            8'h02: begin // WRITE command
                if (axi_trans.trans_kind != AXI_WRITE) return 0;
                return (uart_trans.data[0] == axi_trans.wdata[7:0]);
            end
            default: return 0;
        endcase
    endfunction

    // Enhanced Final Report - QA-2.1 Specification
    virtual function void report_phase(uvm_phase phase);
        int total_transactions;
        real quality_score;
        bit qa_pass;
        string fail_reasons[$];
        response_tracking_entry entry;
        time total_response_time;
        string combined_reasons;
        
        super.report_phase(phase);
        
        // QA-2.1: Check for zero activity
        check_zero_activity();
        
        // QA-2.1: Analyze response times
        analyze_response_times();
        
        total_transactions = uart_transactions_received + axi_transactions_received + dut_state_changes_received;
        
        `uvm_info("ENHANCED_SB_REPORT", 
                  "================== QA-2.1 ENHANCED SCOREBOARD REPORT ==================", UVM_NONE)
        
        // Transaction Statistics
        `uvm_info("ENHANCED_SB_REPORT", 
                  $sformatf("UART Transactions: %0d", uart_transactions_received), UVM_NONE)
        `uvm_info("ENHANCED_SB_REPORT", 
                  $sformatf("AXI Transactions: %0d", axi_transactions_received), UVM_NONE)
        `uvm_info("ENHANCED_SB_REPORT", 
                  $sformatf("DUT State Changes: %0d", dut_state_changes_received), UVM_NONE)
        `uvm_info("ENHANCED_SB_REPORT", 
                  $sformatf("Total Transactions: %0d", total_transactions), UVM_NONE)
        
        // QA-2.1 Enhanced Quality Metrics
        `uvm_info("ENHANCED_SB_REPORT", 
                  $sformatf("Successful Matches: %0d", successful_matches), UVM_NONE)
        `uvm_info("ENHANCED_SB_REPORT", 
                  $sformatf("Protocol Violations: %0d", protocol_violations), UVM_NONE)
        `uvm_info("ENHANCED_SB_REPORT", 
                  $sformatf("Timeout Errors: %0d", timeout_errors), UVM_NONE)
        `uvm_info("ENHANCED_SB_REPORT", 
                  $sformatf("Zero Activity Errors: %0d", zero_activity_errors), UVM_NONE)
        
        // QA-2.1 Activity Analysis
        `uvm_info("ENHANCED_SB_REPORT", 
                  $sformatf("First Activity Time: %0t ns", first_activity_time), UVM_NONE)
        `uvm_info("ENHANCED_SB_REPORT", 
                  $sformatf("Last UART Activity: %0t ns", last_uart_activity), UVM_NONE)
        `uvm_info("ENHANCED_SB_REPORT", 
                  $sformatf("Last AXI Activity: %0t ns", last_axi_activity), UVM_NONE)
        `uvm_info("ENHANCED_SB_REPORT", 
                  $sformatf("Last DUT Activity: %0t ns", last_dut_activity), UVM_NONE)
        `uvm_info("ENHANCED_SB_REPORT", 
                  $sformatf("Longest Response Time: %0t ns", longest_response_time), UVM_NONE)
        `uvm_info("ENHANCED_SB_REPORT", 
                  $sformatf("Zero Activity Detected: %s", zero_activity_detected ? "YES" : "NO"), UVM_NONE)
        
        // QA-2.1 Response Tracking Summary
        `uvm_info("ENHANCED_SB_REPORT", "--- RESPONSE TRACKING SUMMARY ---", UVM_NONE)
        foreach (active_responses[trans_id]) begin
            entry = active_responses[trans_id];
            total_response_time = entry.processing_complete ? 
                (entry.uart_response_time - entry.uart_frame_time) : 0;
            
            `uvm_info("ENHANCED_SB_REPORT", 
                      $sformatf("[%s]: Complete=%s, Total_Time=%0t ns", 
                               trans_id, entry.processing_complete ? "YES" : "NO", total_response_time), UVM_MEDIUM)
        end
        
        // QA-2.1 Quality Assessment
        quality_score = calculate_quality_score();
        `uvm_info("ENHANCED_SB_REPORT", 
                  $sformatf("📊 QA-2.1 Quality Score: %.1f%%", quality_score), UVM_NONE)
        
        // QA-2.1 Final Verdict with Enhanced Criteria
        qa_pass = 1;
        
        if (zero_activity_detected) begin
            qa_pass = 0;
            fail_reasons.push_back("ZERO ACTIVITY: No transactions processed");
        end
        
        if (protocol_violations > 0) begin
            qa_pass = 0;
            fail_reasons.push_back($sformatf("PROTOCOL VIOLATIONS: %0d detected", protocol_violations));
        end
        
        if (timeout_errors > 0) begin
            qa_pass = 0;
            fail_reasons.push_back($sformatf("TIMEOUT ERRORS: %0d detected", timeout_errors));
        end
        
        if (successful_matches == 0 && total_transactions > 0) begin
            qa_pass = 0;
            fail_reasons.push_back("NO SUCCESSFUL MATCHES: DUT not responding");
        end
        
        if (qa_pass) begin
            `uvm_info("ENHANCED_SB_REPORT", "✅ QA-2.1 VERIFICATION: PASSED", UVM_NONE)
        end else begin
            combined_reasons = "";
            foreach (fail_reasons[i]) begin
                combined_reasons = {combined_reasons, fail_reasons[i]};
                if (i < fail_reasons.size()-1) combined_reasons = {combined_reasons, "; "};
            end
            `uvm_error("ENHANCED_SB_REPORT", $sformatf("❌ QA-2.1 VERIFICATION: FAILED - %s", combined_reasons))
        end
        
        `uvm_info("ENHANCED_SB_REPORT", 
                  "========================================================================", UVM_NONE)
    endfunction

    // Quality Score Calculation
    virtual function real calculate_quality_score();
        int total_transactions;
        real success_ratio;
        real violation_penalty;
        real timeout_penalty;
        real quality_score;
        
        total_transactions = uart_transactions_received + axi_transactions_received;
        if (total_transactions == 0) return 0.0;
        
        success_ratio = real'(successful_matches) / real'(total_transactions) * 100.0;
        violation_penalty = real'(protocol_violations) * 10.0;
        timeout_penalty = real'(timeout_errors) * 20.0;
        
        quality_score = success_ratio - violation_penalty - timeout_penalty;
        return (quality_score < 0.0) ? 0.0 : quality_score;
    endfunction

endclass