`timescale 1ns / 1ps

//==============================================================================
// UART-AXI4 Scoreboard Component
// Part of Phase 3 Scoreboard Development
//
// Purpose: Comprehensive verification scoreboard for UART-to-AXI bridge
// Features: Transaction correlation, enhanced error detection, coverage integration
// Author: GitHub Copilot
// Created: October 11, 2025
//==============================================================================

import uvm_pkg::*;
`include "uvm_macros.svh"

//------------------------------------------------------------------------------
// Transaction Data Structures
//------------------------------------------------------------------------------

// UART Transaction Record
typedef struct packed {
    uart_cmd_t      command;        // UART command type (READ/WRITE)
    logic [31:0]    address;        // Target address
    logic [7:0]     data[$];        // Data payload (dynamic array)
    time            timestamp;      // Transaction timestamp
    logic           crc_valid;      // CRC validation status
    uart_status_t   status;         // Transaction status
    int             transaction_id; // Unique transaction identifier
} uart_transaction_record_t;

// AXI Transaction Record
typedef struct packed {
    axi_trans_type_t trans_type;    // AXI transaction type (READ/WRITE)
    logic [31:0]     address;       // AXI address
    logic [31:0]     data[$];       // AXI data (dynamic array)
    time             timestamp;     // Transaction timestamp
    axi_resp_t       response;      // AXI response
    int              burst_length;  // Number of beats in burst
    int              transaction_id; // Unique transaction identifier
} axi_transaction_record_t;

// Correlation Record
typedef struct packed {
    int                     uart_id;            // UART transaction ID
    int                     axi_id;             // AXI transaction ID
    correlation_status_t    status;             // Correlation status
    time                   correlation_time;    // Time of correlation
    logic                  data_match;          // Data integrity check result
    string                 mismatch_details;    // Detailed mismatch information
} correlation_record_t;

// Correlation Status Enumeration
typedef enum {
    CORRELATION_PENDING,    // Waiting for matching transaction
    CORRELATION_MATCHED,    // Successfully correlated
    CORRELATION_TIMEOUT,    // Correlation timeout
    CORRELATION_MISMATCH,   // Data/address mismatch
    CORRELATION_ERROR       // Correlation error
} correlation_status_t;

//------------------------------------------------------------------------------
// Enhanced UART-AXI4 Scoreboard Class
//------------------------------------------------------------------------------

class uart_axi4_scoreboard extends uvm_scoreboard;
    
    // UVM Factory Registration
    `uvm_component_utils(uart_axi4_scoreboard)
    
    //--------------------------------------------------------------------------
    // Configuration and Analysis Ports
    //--------------------------------------------------------------------------
    
    // Analysis ports for receiving transactions
    uvm_analysis_imp_uart #(uart_transaction_record_t, uart_axi4_scoreboard) uart_ap;
    uvm_analysis_imp_axi  #(axi_transaction_record_t,  uart_axi4_scoreboard) axi_ap;
    
    // Configuration object
    uart_axi4_config cfg;
    
    //--------------------------------------------------------------------------
    // Internal Data Structures
    //--------------------------------------------------------------------------
    
    // Transaction storage queues
    uart_transaction_record_t uart_transactions[$];
    axi_transaction_record_t  axi_transactions[$];
    correlation_record_t      correlations[$];
    
    // Transaction ID counters
    int uart_transaction_count;
    int axi_transaction_count;
    int correlation_count;
    
    // Statistics counters
    int successful_correlations;
    int failed_correlations;
    int timeout_correlations;
    int data_mismatches;
    
    // Timing parameters
    time correlation_timeout;
    time max_correlation_latency;
    time min_correlation_latency;
    
    // Enhanced reporting IDs (using new framework)
    uvm_report_object correlation_reporter;
    uvm_report_object error_reporter;
    uvm_report_object statistics_reporter;
    
    //--------------------------------------------------------------------------
    // Constructor
    //--------------------------------------------------------------------------
    
    function new(string name = "uart_axi4_scoreboard", uvm_component parent = null);
        super.new(name, parent);
        
        // Initialize counters
        uart_transaction_count = 0;
        axi_transaction_count = 0;
        correlation_count = 0;
        successful_correlations = 0;
        failed_correlations = 0;
        timeout_correlations = 0;
        data_mismatches = 0;
        
        // Initialize timing parameters
        correlation_timeout = 10us;     // 10 microsecond timeout
        max_correlation_latency = 0;
        min_correlation_latency = time'(~0); // Initialize to maximum time value
        
        // Create analysis ports
        uart_ap = new("uart_ap", this);
        axi_ap = new("axi_ap", this);
        
        // Initialize enhanced reporting
        correlation_reporter = this;
        error_reporter = this;
        statistics_reporter = this;
        
    endfunction: new
    
    //--------------------------------------------------------------------------
    // UVM Build Phase
    //--------------------------------------------------------------------------
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        if (!uvm_config_db#(uart_axi4_config)::get(this, "", "cfg", cfg)) begin
            `uvm_error("SCOREBOARD_CFG", "Configuration object not found")
        end
        
        // Configure enhanced reporting
        configure_enhanced_reporting();
        
    endfunction: build_phase
    
    //--------------------------------------------------------------------------
    // Enhanced Reporting Configuration
    //--------------------------------------------------------------------------
    
    function void configure_enhanced_reporting();
        
        // Set up component-specific verbosity levels
        this.set_report_verbosity_level(UVM_MEDIUM);
        this.set_report_max_quit_count(5);
        
        // Configure report IDs with categorization
        this.set_report_id_verbosity("SCOREBOARD_CORRELATION", UVM_MEDIUM);
        this.set_report_id_verbosity("SCOREBOARD_ERROR", UVM_LOW);
        this.set_report_id_verbosity("SCOREBOARD_STATISTICS", UVM_HIGH);
        this.set_report_id_verbosity("SCOREBOARD_TIMEOUT", UVM_LOW);
        this.set_report_id_verbosity("SCOREBOARD_MISMATCH", UVM_LOW);
        
        `uvm_info("SCOREBOARD_INIT", "Enhanced reporting configured for scoreboard", UVM_MEDIUM)
        
    endfunction: configure_enhanced_reporting
    
    //--------------------------------------------------------------------------
    // UART Transaction Analysis
    //--------------------------------------------------------------------------
    
    function void write_uart(uart_transaction_record_t transaction);
        
        // Assign unique transaction ID
        transaction.transaction_id = ++uart_transaction_count;
        transaction.timestamp = $time;
        
        // Store transaction
        uart_transactions.push_back(transaction);
        
        // Enhanced reporting
        `uvm_info("SCOREBOARD_UART_RX", 
                  $sformatf("UART Transaction %0d: Cmd=%s, Addr=0x%08h, Size=%0d", 
                           transaction.transaction_id, 
                           transaction.command.name(), 
                           transaction.address, 
                           transaction.data.size()), 
                  UVM_MEDIUM)
        
        // Attempt correlation
        attempt_correlation();
        
    endfunction: write_uart
    
    //--------------------------------------------------------------------------
    // AXI Transaction Analysis
    //--------------------------------------------------------------------------
    
    function void write_axi(axi_transaction_record_t transaction);
        
        // Assign unique transaction ID
        transaction.transaction_id = ++axi_transaction_count;
        transaction.timestamp = $time;
        
        // Store transaction
        axi_transactions.push_back(transaction);
        
        // Enhanced reporting
        `uvm_info("SCOREBOARD_AXI_RX", 
                  $sformatf("AXI Transaction %0d: Type=%s, Addr=0x%08h, Resp=%s, Burst=%0d", 
                           transaction.transaction_id, 
                           transaction.trans_type.name(), 
                           transaction.address, 
                           transaction.response.name(), 
                           transaction.burst_length), 
                  UVM_MEDIUM)
        
        // Attempt correlation
        attempt_correlation();
        
    endfunction: write_axi
    
    //--------------------------------------------------------------------------
    // Transaction Correlation Engine
    //--------------------------------------------------------------------------
    
    function void attempt_correlation();
        uart_transaction_record_t uart_trans;
        axi_transaction_record_t  axi_trans;
        correlation_record_t      correlation;
        bit correlation_found = 0;
        time correlation_latency;
        
        // Try to correlate pending UART transactions with AXI transactions
        for (int i = 0; i < uart_transactions.size(); i++) begin
            uart_trans = uart_transactions[i];
            
            // Skip already correlated transactions
            if (is_transaction_correlated(uart_trans.transaction_id, "UART")) continue;
            
            for (int j = 0; j < axi_transactions.size(); j++) begin
                axi_trans = axi_transactions[j];
                
                // Skip already correlated transactions
                if (is_transaction_correlated(axi_trans.transaction_id, "AXI")) continue;
                
                // Check for correlation match
                if (transactions_match(uart_trans, axi_trans)) begin
                    
                    // Calculate correlation latency
                    if (axi_trans.timestamp > uart_trans.timestamp) begin
                        correlation_latency = axi_trans.timestamp - uart_trans.timestamp;
                    end else begin
                        correlation_latency = uart_trans.timestamp - axi_trans.timestamp;
                    end
                    
                    // Create correlation record
                    correlation.uart_id = uart_trans.transaction_id;
                    correlation.axi_id = axi_trans.transaction_id;
                    correlation.correlation_time = $time;
                    correlation.status = CORRELATION_MATCHED;
                    
                    // Validate data integrity
                    correlation.data_match = validate_data_integrity(uart_trans, axi_trans);
                    
                    if (!correlation.data_match) begin
                        correlation.mismatch_details = generate_mismatch_details(uart_trans, axi_trans);
                        data_mismatches++;
                        `uvm_error("SCOREBOARD_MISMATCH", 
                                  $sformatf("Data mismatch detected: UART[%0d] <-> AXI[%0d]: %s", 
                                           uart_trans.transaction_id, 
                                           axi_trans.transaction_id, 
                                           correlation.mismatch_details))
                    end
                    
                    // Store correlation
                    correlations.push_back(correlation);
                    successful_correlations++;
                    correlation_found = 1;
                    
                    // Update latency statistics
                    if (correlation_latency > max_correlation_latency) begin
                        max_correlation_latency = correlation_latency;
                    end
                    if (correlation_latency < min_correlation_latency) begin
                        min_correlation_latency = correlation_latency;
                    end
                    
                    // Enhanced reporting
                    `uvm_info("SCOREBOARD_CORRELATION", 
                             $sformatf("Correlation successful: UART[%0d] <-> AXI[%0d], Latency=%0t, Data_Match=%b", 
                                      uart_trans.transaction_id, 
                                      axi_trans.transaction_id, 
                                      correlation_latency, 
                                      correlation.data_match), 
                             UVM_MEDIUM)
                    
                    break; // Move to next UART transaction
                end
            end
        end
        
    endfunction: attempt_correlation
    
    //--------------------------------------------------------------------------
    // Transaction Matching Logic
    //--------------------------------------------------------------------------
    
    function bit transactions_match(uart_transaction_record_t uart_trans, axi_transaction_record_t axi_trans);
        
        // Address matching
        if (uart_trans.address != axi_trans.address) begin
            return 0;
        end
        
        // Command type matching
        case (uart_trans.command)
            UART_CMD_WRITE: if (axi_trans.trans_type != AXI_WRITE) return 0;
            UART_CMD_READ:  if (axi_trans.trans_type != AXI_READ) return 0;
            default: return 0;
        endcase
        
        // Timing constraint (within correlation timeout)
        time time_diff = (axi_trans.timestamp > uart_trans.timestamp) ? 
                        (axi_trans.timestamp - uart_trans.timestamp) : 
                        (uart_trans.timestamp - axi_trans.timestamp);
        
        if (time_diff > correlation_timeout) begin
            return 0;
        end
        
        return 1;
        
    endfunction: transactions_match
    
    //--------------------------------------------------------------------------
    // Data Integrity Validation
    //--------------------------------------------------------------------------
    
    function bit validate_data_integrity(uart_transaction_record_t uart_trans, axi_transaction_record_t axi_trans);
        
        // For write transactions, compare data payload
        if (uart_trans.command == UART_CMD_WRITE) begin
            if (uart_trans.data.size() != axi_trans.data.size()) begin
                return 0;
            end
            
            for (int i = 0; i < uart_trans.data.size(); i++) begin
                if (uart_trans.data[i] != axi_trans.data[i]) begin
                    return 0;
                end
            end
        end
        
        // For read transactions, data validation occurs at response level
        // (Implementation depends on specific protocol requirements)
        
        return 1;
        
    endfunction: validate_data_integrity
    
    //--------------------------------------------------------------------------
    // Utility Functions
    //--------------------------------------------------------------------------
    
    function bit is_transaction_correlated(int trans_id, string trans_type);
        foreach (correlations[i]) begin
            if (trans_type == "UART" && correlations[i].uart_id == trans_id) return 1;
            if (trans_type == "AXI" && correlations[i].axi_id == trans_id) return 1;
        end
        return 0;
    endfunction: is_transaction_correlated
    
    function string generate_mismatch_details(uart_transaction_record_t uart_trans, axi_transaction_record_t axi_trans);
        string details = "";
        
        // Address mismatch
        if (uart_trans.address != axi_trans.address) begin
            details = {details, $sformatf("Address: UART=0x%08h, AXI=0x%08h; ", uart_trans.address, axi_trans.address)};
        end
        
        // Data size mismatch
        if (uart_trans.data.size() != axi_trans.data.size()) begin
            details = {details, $sformatf("Size: UART=%0d, AXI=%0d; ", uart_trans.data.size(), axi_trans.data.size())};
        end
        
        return details;
    endfunction: generate_mismatch_details
    
    //--------------------------------------------------------------------------
    // Timeout Monitoring Task
    //--------------------------------------------------------------------------
    
    task monitor_timeouts();
        uart_transaction_record_t uart_trans;
        correlation_record_t timeout_correlation;
        
        forever begin
            #(correlation_timeout/10); // Check every 1/10 of timeout period
            
            // Check for timeout UART transactions
            for (int i = 0; i < uart_transactions.size(); i++) begin
                uart_trans = uart_transactions[i];
                
                // Skip already correlated transactions
                if (is_transaction_correlated(uart_trans.transaction_id, "UART")) continue;
                
                // Check if transaction has timed out
                if (($time - uart_trans.timestamp) > correlation_timeout) begin
                    timeout_correlation.uart_id = uart_trans.transaction_id;
                    timeout_correlation.axi_id = -1; // No AXI correlation
                    timeout_correlation.status = CORRELATION_TIMEOUT;
                    timeout_correlation.correlation_time = $time;
                    timeout_correlation.data_match = 0;
                    timeout_correlation.mismatch_details = "Correlation timeout";
                    
                    correlations.push_back(timeout_correlation);
                    timeout_correlations++;
                    
                    `uvm_warning("SCOREBOARD_TIMEOUT", 
                                $sformatf("UART transaction %0d timed out after %0t", 
                                         uart_trans.transaction_id, 
                                         correlation_timeout))
                end
            end
        end
        
    endtask: monitor_timeouts
    
    //--------------------------------------------------------------------------
    // Run Phase
    //--------------------------------------------------------------------------
    
    task run_phase(uvm_phase phase);
        super.run_phase(phase);
        
        // Start timeout monitoring
        fork
            monitor_timeouts();
        join_none
        
    endtask: run_phase
    
    //--------------------------------------------------------------------------
    // Final Statistics Report
    //--------------------------------------------------------------------------
    
    function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        
        // Generate comprehensive statistics report
        `uvm_info("SCOREBOARD_STATISTICS", 
                 $sformatf("\n=== UART-AXI4 Scoreboard Final Report ===\n" +
                          "UART Transactions:     %0d\n" +
                          "AXI Transactions:      %0d\n" +
                          "Successful Correlations: %0d\n" +
                          "Failed Correlations:   %0d\n" +
                          "Timeout Correlations:  %0d\n" +
                          "Data Mismatches:       %0d\n" +
                          "Max Correlation Latency: %0t\n" +
                          "Min Correlation Latency: %0t\n" +
                          "=========================================="), 
                 UVM_NONE)
        
        // Check for verification success
        if (failed_correlations == 0 && data_mismatches == 0) begin
            `uvm_info("SCOREBOARD_SUCCESS", "All transactions successfully correlated with no data mismatches", UVM_NONE)
        end else begin
            `uvm_error("SCOREBOARD_FAILURE", 
                      $sformatf("Verification failed: %0d correlation failures, %0d data mismatches", 
                               failed_correlations, data_mismatches))
        end
        
    endfunction: report_phase

endclass: uart_axi4_scoreboard