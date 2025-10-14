`timescale 1ns/1ps

// QA-2.2 Enhanced Scoreboard with Quality Metrics Integration
// Simplified version with quality analysis focus
// Author: QA Framework - FastMCP v2.0
// Date: 2025-10-14

class uart_axi4_qa22_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(uart_axi4_qa22_scoreboard)
    
    // Analysis ports
    uvm_analysis_imp_uart #(uart_axi4_transaction, uart_axi4_qa22_scoreboard) uart_imp;
    uvm_analysis_imp_axi #(uart_axi4_transaction, uart_axi4_qa22_scoreboard) axi_imp;
    
    // Quality metrics components
    uart_axi4_quality_collector quality_collector;
    uart_axi4_quality_metrics quality_metrics;
    
    // Transaction tracking
    uart_axi4_transaction uart_transactions[$];
    uart_axi4_transaction axi_transactions[$];
    uart_axi4_transaction matched_transactions[$];
    
    // Quality counters
    int total_transactions = 0;
    int matched_transactions_count = 0;
    int failed_matches = 0;
    int zero_activity_count = 0;
    
    // Timing tracking
    time last_activity_time = 0;
    time zero_activity_threshold = 1000000; // 1ms
    
    function new(string name = "uart_axi4_qa22_scoreboard", uvm_component parent = null);
        super.new(name, parent);
        
        // Create analysis ports
        uart_imp = new("uart_imp", this);
        axi_imp = new("axi_imp", this);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Create quality components
        quality_collector = uart_axi4_quality_collector::type_id::create("quality_collector", this);
        quality_metrics = uart_axi4_quality_metrics::type_id::create("quality_metrics");
        
        `uvm_info(get_type_name(), "QA-2.2 Enhanced Scoreboard initialized", UVM_MEDIUM)
    endfunction
    
    // UART transaction analysis
    function void write_uart(uart_axi4_transaction t);
        uart_transactions.push_back(t);
        total_transactions++;
        last_activity_time = $time;
        
        // Forward to quality collector
        quality_collector.write(t);
        
        // Check for matches
        check_transaction_matches();
        
        `uvm_info(get_type_name(), 
                 $sformatf("UART transaction received: %s", t.convert2string()), 
                 UVM_HIGH)
    endfunction
    
    // AXI transaction analysis
    function void write_axi(uart_axi4_transaction t);
        axi_transactions.push_back(t);
        total_transactions++;
        last_activity_time = $time;
        
        // Forward to quality collector
        quality_collector.write(t);
        
        // Check for matches
        check_transaction_matches();
        
        `uvm_info(get_type_name(), 
                 $sformatf("AXI transaction received: %s", t.convert2string()), 
                 UVM_HIGH)
    endfunction
    
    // Check for transaction matches
    function void check_transaction_matches();
        uart_axi4_transaction uart_txn, axi_txn;
        bit match_found = 0;
        
        // Simple matching algorithm
        if (uart_transactions.size() > 0 && axi_transactions.size() > 0) begin
            uart_txn = uart_transactions[0];
            axi_txn = axi_transactions[0];
            
            // Check if transactions match
            if (transaction_matches(uart_txn, axi_txn)) begin
                matched_transactions.push_back(uart_txn);
                matched_transactions_count++;
                match_found = 1;
                
                // Remove matched transactions
                uart_transactions.pop_front();
                axi_transactions.pop_front();
                
                `uvm_info(get_type_name(), "Transaction match found", UVM_MEDIUM)
            end
        end
        
        if (!match_found && (uart_transactions.size() > 10 || axi_transactions.size() > 10)) begin
            failed_matches++;
            `uvm_warning(get_type_name(), "Potential transaction mismatch detected")
        end
    endfunction
    
    // Transaction matching logic
    function bit transaction_matches(uart_axi4_transaction uart_txn, uart_axi4_transaction axi_txn);
        // Simplified matching - check data content
        if (uart_txn.data.size() == axi_txn.data.size()) begin
            foreach (uart_txn.data[i]) begin
                if (uart_txn.data[i] != axi_txn.data[i]) begin
                    return 0;
                end
            end
            return 1;
        end
        return 0;
    endfunction
    
    // Monitor for zero activity
    task monitor_activity();
        time current_time;
        
        forever begin
            #(zero_activity_threshold);
            current_time = $time;
            
            if ((current_time - last_activity_time) > zero_activity_threshold) begin
                zero_activity_count++;
                `uvm_warning(get_type_name(), 
                           $sformatf("Zero activity detected for %0t ns", 
                                   current_time - last_activity_time))
            end
        end
    endtask
    
    // Start monitoring
    task run_phase(uvm_phase phase);
        super.run_phase(phase);
        
        // Start activity monitoring
        fork
            monitor_activity();
        join_none
    endtask
    
    // Calculate quality score
    function real calculate_qa22_quality_score();
        real match_ratio, activity_score, overall_score;
        
        // Calculate match ratio
        if (total_transactions > 0) begin
            match_ratio = real'(matched_transactions_count) / real'(total_transactions);
        end else begin
            match_ratio = 0.0;
        end
        
        // Calculate activity score (penalize zero activity)
        activity_score = 1.0 - (real'(zero_activity_count) * 0.1);
        if (activity_score < 0.0) activity_score = 0.0;
        
        // Overall quality score
        overall_score = (match_ratio * 0.7 + activity_score * 0.3) * 100.0;
        
        return overall_score;
    endfunction
    
    // Generate QA-2.2 report
    function string generate_qa22_report();
        string report;
        real quality_score;
        
        quality_score = calculate_qa22_quality_score();
        
        report = "\n";
        report = {report, "================ QA-2.2 SCOREBOARD REPORT ================\n"};
        report = {report, $sformatf("Total Transactions: %0d\n", total_transactions)};
        report = {report, $sformatf("Matched Transactions: %0d\n", matched_transactions_count)};
        report = {report, $sformatf("Failed Matches: %0d\n", failed_matches)};
        report = {report, $sformatf("Zero Activity Events: %0d\n", zero_activity_count)};
        
        if (total_transactions > 0) begin
            report = {report, $sformatf("Match Ratio: %.1f%%\n", 
                     (real'(matched_transactions_count) / real'(total_transactions)) * 100.0)};
        end
        
        report = {report, $sformatf("QA-2.2 Quality Score: %.1f/100\n", quality_score)};
        
        if (quality_score >= 80.0) begin
            report = {report, "QA-2.2 Status: PASS\n"};
        end else begin
            report = {report, "QA-2.2 Status: FAIL\n"};
        end
        
        report = {report, "=======================================================\n"};
        
        return report;
    endfunction
    
    // End of test processing
    function void extract_phase(uvm_phase phase);
        string report;
        
        super.extract_phase(phase);
        
        // Generate and display report
        report = generate_qa22_report();
        `uvm_info(get_type_name(), report, UVM_LOW)
        
        // Check quality thresholds
        if (calculate_qa22_quality_score() < 70.0) begin
            `uvm_error(get_type_name(), "QA-2.2 quality score below threshold (70.0)")
        end
    endfunction
    
    // Final report generation
    function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        
        // Export quality metrics if available
        if (quality_collector != null) begin
            quality_collector.export_metrics_json();
        end
    endfunction
    
endclass