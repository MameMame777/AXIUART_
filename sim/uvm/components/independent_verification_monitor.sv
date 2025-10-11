`timescale 1ns / 1ps

//==============================================================================
// Independent Verification Monitor
//==============================================================================
// File: independent_verification_monitor.sv
// Purpose: UVMスコアボードとは独立した検証ロジック
// Author: AI Assistant
// Date: 2025-10-11
// Description: Provides independent verification results to cross-check UVM scoreboard
//              Implements triple verification principle
//==============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;
import uart_axi4_pkg::*;

class Independent_Verification_Monitor extends uvm_monitor;
    `uvm_component_utils(Independent_Verification_Monitor)
    
    // Independent transaction storage
    uart_axi4_transaction independent_expected_transactions[$];
    uart_axi4_transaction independent_actual_transactions[$];
    
    // Independent verification results
    int independent_match_count = 0;
    int independent_mismatch_count = 0;
    int independent_total_transactions = 0;
    
    // UVM scoreboard comparison
    int uvm_scoreboard_match_count = 0;
    int uvm_scoreboard_mismatch_count = 0;
    
    // Cross-verification status
    bit cross_verification_enabled = 1;
    bit verification_mismatch_detected = 0;
    string last_mismatch_reason = "";
    
    // Monitoring configuration
    bit detailed_logging = 1;
    int max_transaction_queue_size = 1000;
    
    // Analysis ports for independent verification
    uvm_analysis_port #(uart_axi4_transaction) independent_expected_port;
    uvm_analysis_port #(uart_axi4_transaction) independent_actual_port;
    uvm_analysis_port #(verification_result_t) independent_result_port;
    
    // Cross-verification result structure
    typedef struct {
        bit valid;
        int independent_matches;
        int independent_mismatches;
        int uvm_matches;
        int uvm_mismatches;
        bit results_consistent;
        string inconsistency_reason;
        time timestamp;
    } cross_verification_result_t;
    
    cross_verification_result_t latest_cross_verification;
    
    function new(string name = "independent_verification_monitor", uvm_component parent = null);
        super.new(name, parent);
        independent_expected_port = new("independent_expected_port", this);
        independent_actual_port = new("independent_actual_port", this);
        independent_result_port = new("independent_result_port", this);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        `uvm_info("INDEPENDENT_VERIFY", "Building Independent Verification Monitor", UVM_LOW)
        
        if (!uvm_config_db#(bit)::get(this, "", "cross_verification_enabled", cross_verification_enabled)) begin
            cross_verification_enabled = 1;
        end
        
        if (!uvm_config_db#(bit)::get(this, "", "detailed_logging", detailed_logging)) begin
            detailed_logging = 1;
        end
        
        if (!uvm_config_db#(int)::get(this, "", "max_transaction_queue_size", max_transaction_queue_size)) begin
            max_transaction_queue_size = 1000;
        end
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        `uvm_info("INDEPENDENT_VERIFY", "Connecting Independent Verification Monitor", UVM_MEDIUM)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        `uvm_info("INDEPENDENT_VERIFY", "Starting Independent Verification Monitor", UVM_LOW)
        
        fork
            collect_independent_transactions();
            perform_independent_verification();
            if (cross_verification_enabled) begin
                perform_cross_verification_with_uvm();
            end
            monitor_verification_health();
        join_none
    endtask
    
    //==========================================================================
    // Independent Transaction Collection
    //==========================================================================
    
    virtual task collect_independent_transactions();
        forever begin
            @(posedge vif.clk);
            
            if (!vif.reset) begin
                // Collect expected transactions independently
                collect_expected_transaction();
                
                // Collect actual transactions independently
                collect_actual_transaction();
                
                // Manage queue sizes
                manage_transaction_queues();
            end
        end
    endtask
    
    virtual function void collect_expected_transaction();
        uart_axi4_transaction expected_tr;
        
        // Independent collection logic (not relying on UVM scoreboard)
        if (detect_expected_transaction_conditions()) begin
            expected_tr = create_expected_transaction_independently();
            
            if (expected_tr != null) begin
                independent_expected_transactions.push_back(expected_tr);
                independent_expected_port.write(expected_tr);
                
                if (detailed_logging) begin
                    `uvm_info("INDEPENDENT_VERIFY", 
                        $sformatf("Independent expected transaction collected: %s", 
                                 expected_tr.convert2string()), UVM_HIGH)
                end
            end
        end
    endfunction
    
    virtual function void collect_actual_transaction();
        uart_axi4_transaction actual_tr;
        
        // Independent collection logic (not relying on UVM monitor)
        if (detect_actual_transaction_conditions()) begin
            actual_tr = create_actual_transaction_independently();
            
            if (actual_tr != null) begin
                independent_actual_transactions.push_back(actual_tr);
                independent_actual_port.write(actual_tr);
                
                if (detailed_logging) begin
                    `uvm_info("INDEPENDENT_VERIFY", 
                        $sformatf("Independent actual transaction collected: %s", 
                                 actual_tr.convert2string()), UVM_HIGH)
                end
            end
        end
    endfunction
    
    //==========================================================================
    // Independent Verification Logic
    //==========================================================================
    
    virtual task perform_independent_verification();
        forever begin
            @(posedge vif.clk);
            
            if (!vif.reset && (independent_expected_transactions.size() > 0) && 
                (independent_actual_transactions.size() > 0)) begin
                
                // Perform independent comparison
                compare_transactions_independently();
            end
        end
    endtask
    
    virtual function void compare_transactions_independently();
        uart_axi4_transaction expected_tr, actual_tr;
        bit match_result;
        verification_result_t result;
        
        // Get transactions for comparison
        expected_tr = independent_expected_transactions.pop_front();
        actual_tr = independent_actual_transactions.pop_front();
        
        independent_total_transactions++;
        
        // Independent comparison logic
        match_result = perform_independent_comparison(expected_tr, actual_tr);
        
        if (match_result) begin
            independent_match_count++;
            result.status = VERIFICATION_PASS;
            result.description = "Independent verification MATCH";
            
            if (detailed_logging) begin
                `uvm_info("INDEPENDENT_VERIFY", 
                    $sformatf("Independent verification MATCH %0d: Expected=%s, Actual=%s", 
                             independent_match_count, 
                             expected_tr.convert2string(), 
                             actual_tr.convert2string()), UVM_MEDIUM)
            end
        end else begin
            independent_mismatch_count++;
            result.status = VERIFICATION_FAIL;
            result.description = "Independent verification MISMATCH";
            
            `uvm_error("INDEPENDENT_VERIFY", 
                $sformatf("Independent verification MISMATCH %0d: Expected=%s, Actual=%s", 
                         independent_mismatch_count, 
                         expected_tr.convert2string(), 
                         actual_tr.convert2string()))
        end
        
        // Publish independent result
        result.timestamp = $time;
        result.transaction_id = independent_total_transactions;
        independent_result_port.write(result);
    endfunction
    
    virtual function bit perform_independent_comparison(uart_axi4_transaction expected, uart_axi4_transaction actual);
        // Independent comparison algorithm (different from UVM scoreboard)
        bit comparison_result = 1;
        
        // Command comparison
        if (expected.cmd != actual.cmd) begin
            `uvm_info("INDEPENDENT_VERIFY", 
                $sformatf("Command mismatch: Expected=0x%02x, Actual=0x%02x", 
                         expected.cmd, actual.cmd), UVM_HIGH)
            comparison_result = 0;
        end
        
        // Address comparison
        if (expected.addr != actual.addr) begin
            `uvm_info("INDEPENDENT_VERIFY", 
                $sformatf("Address mismatch: Expected=0x%08x, Actual=0x%08x", 
                         expected.addr, actual.addr), UVM_HIGH)
            comparison_result = 0;
        end
        
        // Data comparison
        if (expected.data != actual.data) begin
            `uvm_info("INDEPENDENT_VERIFY", 
                $sformatf("Data mismatch: Expected=0x%08x, Actual=0x%08x", 
                         expected.data, actual.data), UVM_HIGH)
            comparison_result = 0;
        end
        
        // CRC comparison
        if (expected.crc != actual.crc) begin
            `uvm_info("INDEPENDENT_VERIFY", 
                $sformatf("CRC mismatch: Expected=0x%02x, Actual=0x%02x", 
                         expected.crc, actual.crc), UVM_HIGH)
            comparison_result = 0;
        end
        
        return comparison_result;
    endfunction
    
    //==========================================================================
    // Cross-Verification with UVM Scoreboard
    //==========================================================================
    
    virtual task perform_cross_verification_with_uvm();
        forever begin
            @(posedge vif.clk);
            
            // Wait for UVM scoreboard results to be available
            if (uvm_scoreboard_results_available()) begin
                perform_uvm_comparison();
            end
        end
    endtask
    
    virtual function void perform_uvm_comparison();
        cross_verification_result_t cross_result;
        
        // Get UVM scoreboard results
        get_uvm_scoreboard_results();
        
        // Compare independent results with UVM results
        cross_result.valid = 1;
        cross_result.independent_matches = independent_match_count;
        cross_result.independent_mismatches = independent_mismatch_count;
        cross_result.uvm_matches = uvm_scoreboard_match_count;
        cross_result.uvm_mismatches = uvm_scoreboard_mismatch_count;
        cross_result.timestamp = $time;
        
        // Check consistency
        if ((cross_result.independent_matches == cross_result.uvm_matches) &&
            (cross_result.independent_mismatches == cross_result.uvm_mismatches)) begin
            cross_result.results_consistent = 1;
            cross_result.inconsistency_reason = "CONSISTENT";
            
            `uvm_info("INDEPENDENT_VERIFY", 
                $sformatf("Cross-verification CONSISTENT: Independent(%0d/%0d) == UVM(%0d/%0d)", 
                         cross_result.independent_matches, cross_result.independent_mismatches,
                         cross_result.uvm_matches, cross_result.uvm_mismatches), UVM_MEDIUM)
        end else begin
            cross_result.results_consistent = 0;
            cross_result.inconsistency_reason = $sformatf(
                "MISMATCH: Independent(%0d/%0d) != UVM(%0d/%0d)", 
                cross_result.independent_matches, cross_result.independent_mismatches,
                cross_result.uvm_matches, cross_result.uvm_mismatches);
            
            verification_mismatch_detected = 1;
            last_mismatch_reason = cross_result.inconsistency_reason;
            
            `uvm_fatal("INDEPENDENT_VERIFY", 
                $sformatf("Cross-verification INCONSISTENCY detected: %s", 
                         cross_result.inconsistency_reason))
        end
        
        latest_cross_verification = cross_result;
    endfunction
    
    //==========================================================================
    // Helper Functions
    //==========================================================================
    
    virtual function bit detect_expected_transaction_conditions();
        // Independent detection logic for expected transactions
        // This should NOT rely on UVM infrastructure
        return (vif.frame_valid && vif.frame_start);
    endfunction
    
    virtual function bit detect_actual_transaction_conditions();
        // Independent detection logic for actual transactions
        // This should NOT rely on UVM infrastructure
        return (vif.axi_awvalid && vif.axi_awready) || (vif.axi_arvalid && vif.axi_arready);
    endfunction
    
    virtual function uart_axi4_transaction create_expected_transaction_independently();
        uart_axi4_transaction tr;
        tr = uart_axi4_transaction::type_id::create("independent_expected_tr");
        
        // Build expected transaction from interface signals independently
        tr.cmd = vif.uart_cmd;
        tr.addr = vif.uart_addr;
        tr.data = vif.uart_data;
        tr.crc = calculate_independent_crc(tr);
        
        return tr;
    endfunction
    
    virtual function uart_axi4_transaction create_actual_transaction_independently();
        uart_axi4_transaction tr;
        tr = uart_axi4_transaction::type_id::create("independent_actual_tr");
        
        // Build actual transaction from interface signals independently
        tr.addr = vif.axi_awaddr.size() > 0 ? vif.axi_awaddr : vif.axi_araddr;
        tr.data = vif.axi_wdata;
        tr.cmd = infer_command_from_axi_signals();
        tr.crc = 0; // Will be filled when complete transaction is received
        
        return tr;
    endfunction
    
    virtual function bit [7:0] calculate_independent_crc(uart_axi4_transaction tr);
        // Independent CRC calculation (different algorithm from main implementation)
        bit [7:0] crc = 8'h00;
        bit [31:0] data_for_crc;
        
        data_for_crc = {tr.cmd, tr.addr[23:0]};
        
        // Simple CRC calculation for verification
        for (int i = 0; i < 32; i++) begin
            crc = crc ^ data_for_crc[i];
        end
        
        return crc;
    endfunction
    
    virtual function bit [7:0] infer_command_from_axi_signals();
        // Infer command type from AXI signals
        if (vif.axi_awvalid) begin
            return 8'h01; // Write command
        end else if (vif.axi_arvalid) begin
            return 8'h02; // Read command
        end else begin
            return 8'h00; // Unknown/invalid
        end
    endfunction
    
    virtual function bit uvm_scoreboard_results_available();
        // Check if UVM scoreboard has new results
        // This would interface with the actual UVM scoreboard
        return 1; // Placeholder - needs actual implementation
    endfunction
    
    virtual function void get_uvm_scoreboard_results();
        // Get results from UVM scoreboard for comparison
        // This would interface with the actual UVM scoreboard
        uvm_scoreboard_match_count = 0; // Placeholder - needs actual implementation
        uvm_scoreboard_mismatch_count = 0; // Placeholder - needs actual implementation
    endfunction
    
    virtual function void manage_transaction_queues();
        // Prevent queue overflow
        if (independent_expected_transactions.size() > max_transaction_queue_size) begin
            void'(independent_expected_transactions.pop_front());
            `uvm_warning("INDEPENDENT_VERIFY", "Expected transaction queue overflow - dropping oldest entry")
        end
        
        if (independent_actual_transactions.size() > max_transaction_queue_size) begin
            void'(independent_actual_transactions.pop_front());
            `uvm_warning("INDEPENDENT_VERIFY", "Actual transaction queue overflow - dropping oldest entry")
        end
    endfunction
    
    virtual task monitor_verification_health();
        forever begin
            #1us; // Check every microsecond
            
            // Monitor for stuck conditions
            if (independent_expected_transactions.size() > (max_transaction_queue_size / 2)) begin
                `uvm_warning("INDEPENDENT_VERIFY", 
                    $sformatf("Expected transaction queue growing large: %0d entries", 
                             independent_expected_transactions.size()))
            end
            
            if (independent_actual_transactions.size() > (max_transaction_queue_size / 2)) begin
                `uvm_warning("INDEPENDENT_VERIFY", 
                    $sformatf("Actual transaction queue growing large: %0d entries", 
                             independent_actual_transactions.size()))
            end
            
            // Monitor verification activity
            if ($time > 10us && independent_total_transactions == 0) begin
                `uvm_warning("INDEPENDENT_VERIFY", "No transactions processed - verification may be stalled")
            end
        end
    endtask
    
    //==========================================================================
    // Reporting Functions
    //==========================================================================
    
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        
        `uvm_info("INDEPENDENT_VERIFY", "=== Independent Verification Report ===", UVM_LOW)
        `uvm_info("INDEPENDENT_VERIFY", 
            $sformatf("Total Transactions: %0d", independent_total_transactions), UVM_LOW)
        `uvm_info("INDEPENDENT_VERIFY", 
            $sformatf("Matches: %0d", independent_match_count), UVM_LOW)
        `uvm_info("INDEPENDENT_VERIFY", 
            $sformatf("Mismatches: %0d", independent_mismatch_count), UVM_LOW)
        
        if (independent_total_transactions > 0) begin
            real match_rate = real'(independent_match_count) / real'(independent_total_transactions) * 100.0;
            `uvm_info("INDEPENDENT_VERIFY", 
                $sformatf("Independent Match Rate: %0.2f%%", match_rate), UVM_LOW)
        end
        
        if (cross_verification_enabled) begin
            `uvm_info("INDEPENDENT_VERIFY", "=== Cross-Verification Status ===", UVM_LOW)
            `uvm_info("INDEPENDENT_VERIFY", 
                $sformatf("Results Consistent: %s", 
                         latest_cross_verification.results_consistent ? "YES" : "NO"), UVM_LOW)
            
            if (!latest_cross_verification.results_consistent) begin
                `uvm_error("INDEPENDENT_VERIFY", 
                    $sformatf("Cross-verification failed: %s", last_mismatch_reason))
            end
        end
        
        `uvm_info("INDEPENDENT_VERIFY", "=== End Independent Verification Report ===", UVM_LOW)
    endfunction

endclass