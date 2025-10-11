`timescale 1ns / 1ps

//===============================================================================
// Independent Verification Monitor
// 
// Purpose: Provide independent verification logic separate from UVM scoreboard
// Author: SystemVerilog Expert (Phase 4.1 Implementation)
// Date: October 11, 2025
//
// This monitor implements verification logic completely independent from the
// UVM scoreboard to cross-validate results and prevent false positives/negatives.
//===============================================================================

class independent_verification_monitor extends uvm_monitor;
    `uvm_component_utils(independent_verification_monitor)
    
    // Analysis port for independent results
    uvm_analysis_port #(uart_transaction) independent_results_port;
    
    // Independent transaction storage
    uart_transaction independent_expected_queue[$];
    uart_transaction independent_actual_queue[$];
    
    // Independent verification statistics
    int independent_match_count = 0;
    int independent_mismatch_count = 0;
    int independent_timeout_count = 0;
    int independent_crc_error_count = 0;
    
    // Cross-validation with UVM scoreboard
    int uvm_match_count = 0;
    int uvm_mismatch_count = 0;
    bit cross_validation_enabled = 1;
    
    // Independent CRC calculator
    bit [31:0] independent_crc_calculator;
    
    // Timing validation
    time last_transaction_time = 0;
    time transaction_timeout_threshold = 5000ns;
    
    virtual uart_axi4_bridge_interface vif;
    
    function new(string name = "independent_verification_monitor", uvm_component parent = null);
        super.new(name, parent);
        independent_results_port = new("independent_results_port", this);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if (!uvm_config_db#(virtual uart_axi4_bridge_interface)::get(this, "", "vif", vif)) begin
            `uvm_fatal("INDEPENDENT_MONITOR", "Virtual interface not found in config_db");
        end
        
        `uvm_info("INDEPENDENT_MONITOR_BUILD", "Independent Verification Monitor built", UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        `uvm_info("INDEPENDENT_MONITOR_RUN", "Starting Independent Verification Monitor", UVM_LOW)
        
        fork
            collect_independent_transactions();
            perform_independent_verification();
            monitor_timing_violations();
            cross_validate_with_uvm();
        join_none
    endtask
    
    //===========================================================================
    // Independent Transaction Collection
    //===========================================================================
    
    virtual task collect_independent_transactions();
        uart_transaction tr;
        
        forever begin
            // Wait for transaction start
            @(posedge vif.clk);
            
            if (vif.frame_start) begin
                tr = uart_transaction::type_id::create("independent_tr");
                
                // Collect transaction data independently
                collect_transaction_data(tr);
                
                // Store in independent queue
                independent_actual_queue.push_back(tr);
                
                `uvm_info("INDEPENDENT_COLLECT", 
                         $sformatf("Collected independent transaction: SOF=%h, CMD=%h, ADDR=%h, DATA=%h", 
                                  tr.sof, tr.cmd, tr.addr, tr.data), UVM_HIGH)
                
                last_transaction_time = $time;
            end
        end
    endtask
    
    virtual task collect_transaction_data(uart_transaction tr);
        // Independent data collection from interface signals
        
        // Collect SOF
        tr.sof = vif.uart_rx_data; // Assuming this carries SOF
        @(posedge vif.clk);
        
        // Collect Command
        tr.cmd = vif.uart_rx_data;
        @(posedge vif.clk);
        
        // Collect Address (4 bytes)
        for (int i = 0; i < 4; i++) begin
            tr.addr = (tr.addr << 8) | vif.uart_rx_data;
            @(posedge vif.clk);
        end
        
        // Collect Data (4 bytes)
        for (int i = 0; i < 4; i++) begin
            tr.data = (tr.data << 8) | vif.uart_rx_data;
            @(posedge vif.clk);
        end
        
        // Collect CRC (4 bytes)
        for (int i = 0; i < 4; i++) begin
            tr.crc = (tr.crc << 8) | vif.uart_rx_data;
            @(posedge vif.clk);
        end
        
        // Calculate independent CRC
        tr.calculated_crc = calculate_independent_crc(tr);
        
        // Collect timestamp
        tr.timestamp = $time;
    endtask
    
    //===========================================================================
    // Independent CRC Calculation
    //===========================================================================
    
    virtual function bit [31:0] calculate_independent_crc(uart_transaction tr);
        bit [31:0] crc;
        bit [7:0] data_bytes[];
        
        // Pack transaction data for CRC calculation
        data_bytes = new[9]; // SOF + CMD + ADDR(4) + DATA(4)
        data_bytes[0] = tr.sof;
        data_bytes[1] = tr.cmd;
        data_bytes[2] = tr.addr[31:24];
        data_bytes[3] = tr.addr[23:16];
        data_bytes[4] = tr.addr[15:8];
        data_bytes[5] = tr.addr[7:0];
        data_bytes[6] = tr.data[31:24];
        data_bytes[7] = tr.data[23:16];
        data_bytes[8] = tr.data[15:8];
        
        // Independent CRC-32 implementation
        crc = 32'hFFFFFFFF;
        
        for (int i = 0; i < data_bytes.size(); i++) begin
            crc = crc ^ data_bytes[i];
            for (int j = 0; j < 8; j++) begin
                if (crc[0] == 1) begin
                    crc = (crc >> 1) ^ 32'hEDB88320; // CRC-32 polynomial
                end else begin
                    crc = crc >> 1;
                end
            end
        end
        
        return ~crc; // Final inversion
    endfunction
    
    //===========================================================================
    // Independent Verification Logic
    //===========================================================================
    
    virtual task perform_independent_verification();
        uart_transaction actual_tr, expected_tr;
        
        forever begin
            // Wait for transactions to verify
            wait(independent_actual_queue.size() > 0);
            
            actual_tr = independent_actual_queue.pop_front();
            
            // Independent verification logic
            if (verify_transaction_independently(actual_tr)) begin
                independent_match_count++;
                `uvm_info("INDEPENDENT_VERIFY", 
                         $sformatf("✓ Independent verification PASS for transaction at %0t", actual_tr.timestamp), 
                         UVM_MEDIUM)
            end else begin
                independent_mismatch_count++;
                `uvm_error("INDEPENDENT_VERIFY", 
                          $sformatf("✗ Independent verification FAIL for transaction at %0t", actual_tr.timestamp))
            end
            
            // Send result to analysis port
            independent_results_port.write(actual_tr);
        end
    endtask
    
    virtual function bit verify_transaction_independently(uart_transaction tr);
        bit verification_result = 1;
        
        // Independent verification checks
        
        // Check 1: SOF validation
        if (tr.sof != 8'hA5) begin
            `uvm_error("INDEPENDENT_VERIFY", $sformatf("Invalid SOF: %h (expected A5)", tr.sof));
            verification_result = 0;
        end
        
        // Check 2: Command validation
        if (!(tr.cmd inside {8'h01, 8'h02, 8'h03, 8'h04})) begin
            `uvm_error("INDEPENDENT_VERIFY", $sformatf("Invalid command: %h", tr.cmd));
            verification_result = 0;
        end
        
        // Check 3: Address alignment (for applicable commands)
        if ((tr.cmd == 8'h01 || tr.cmd == 8'h02) && (tr.addr[1:0] != 2'b00)) begin
            `uvm_warning("INDEPENDENT_VERIFY", $sformatf("Unaligned address: %h", tr.addr));
            // Not necessarily an error, depending on design
        end
        
        // Check 4: CRC validation
        if (tr.crc != tr.calculated_crc) begin
            `uvm_error("INDEPENDENT_VERIFY", 
                      $sformatf("CRC mismatch: received=%h, calculated=%h", tr.crc, tr.calculated_crc));
            verification_result = 0;
            independent_crc_error_count++;
        end
        
        // Check 5: Timing validation
        if (($time - last_transaction_time) > transaction_timeout_threshold) begin
            `uvm_warning("INDEPENDENT_VERIFY", 
                        $sformatf("Transaction timeout: %0t ns since last transaction", $time - last_transaction_time));
            independent_timeout_count++;
        end
        
        return verification_result;
    endfunction
    
    //===========================================================================
    // Timing Violation Monitoring
    //===========================================================================
    
    virtual task monitor_timing_violations();
        time start_time, end_time, duration;
        
        forever begin
            @(posedge vif.frame_start);
            start_time = $time;
            
            @(posedge vif.frame_end);
            end_time = $time;
            
            duration = end_time - start_time;
            
            // Check for timing violations
            if (duration > 10000ns) begin // Example threshold
                `uvm_warning("INDEPENDENT_TIMING", 
                            $sformatf("Long transaction duration: %0t ns", duration));
            end
            
            if (duration < 100ns) begin // Example minimum
                `uvm_warning("INDEPENDENT_TIMING", 
                            $sformatf("Suspiciously short transaction: %0t ns", duration));
            end
        end
    endtask
    
    //===========================================================================
    // Cross-Validation with UVM Scoreboard
    //===========================================================================
    
    virtual task cross_validate_with_uvm();
        forever begin
            // Wait for both independent and UVM results to be available
            #1000ns; // Periodic check
            
            if (cross_validation_enabled) begin
                perform_cross_validation_check();
            end
        end
    endtask
    
    virtual function void perform_cross_validation_check();
        // This would be called when UVM scoreboard results are available
        // For now, we'll implement a placeholder
        
        if (independent_match_count != uvm_match_count) begin
            `uvm_fatal("CROSS_VALIDATION", 
                      $sformatf("Match count mismatch: Independent=%0d, UVM=%0d", 
                               independent_match_count, uvm_match_count));
        end
        
        if (independent_mismatch_count != uvm_mismatch_count) begin
            `uvm_fatal("CROSS_VALIDATION", 
                      $sformatf("Mismatch count mismatch: Independent=%0d, UVM=%0d", 
                               independent_mismatch_count, uvm_mismatch_count));
        end
        
        `uvm_info("CROSS_VALIDATION", 
                 $sformatf("Cross-validation PASS: Independent and UVM results consistent"), UVM_MEDIUM)
    endfunction
    
    //===========================================================================
    // UVM Scoreboard Interface
    //===========================================================================
    
    virtual function void update_uvm_statistics(int uvm_matches, int uvm_mismatches);
        uvm_match_count = uvm_matches;
        uvm_mismatch_count = uvm_mismatches;
        
        // Trigger cross-validation check
        if (cross_validation_enabled) begin
            perform_cross_validation_check();
        end
    endfunction
    
    //===========================================================================
    // Report Generation
    //===========================================================================
    
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        
        `uvm_info("INDEPENDENT_REPORT", "=== Independent Verification Monitor Report ===", UVM_LOW)
        `uvm_info("INDEPENDENT_REPORT", $sformatf("Independent Matches: %0d", independent_match_count), UVM_LOW)
        `uvm_info("INDEPENDENT_REPORT", $sformatf("Independent Mismatches: %0d", independent_mismatch_count), UVM_LOW)
        `uvm_info("INDEPENDENT_REPORT", $sformatf("Independent CRC Errors: %0d", independent_crc_error_count), UVM_LOW)
        `uvm_info("INDEPENDENT_REPORT", $sformatf("Independent Timeouts: %0d", independent_timeout_count), UVM_LOW)
        
        if (cross_validation_enabled) begin
            `uvm_info("INDEPENDENT_REPORT", $sformatf("UVM Matches: %0d", uvm_match_count), UVM_LOW)
            `uvm_info("INDEPENDENT_REPORT", $sformatf("UVM Mismatches: %0d", uvm_mismatch_count), UVM_LOW)
            
            if (independent_match_count == uvm_match_count && independent_mismatch_count == uvm_mismatch_count) begin
                `uvm_info("INDEPENDENT_REPORT", "✓ Cross-validation SUCCESSFUL - Results consistent", UVM_LOW)
            end else begin
                `uvm_fatal("INDEPENDENT_REPORT", "✗ Cross-validation FAILED - Results inconsistent");
            end
        end
        
        `uvm_info("INDEPENDENT_REPORT", "=== End Independent Verification Report ===", UVM_LOW)
    endfunction
    
    //===========================================================================
    // Utility Functions
    //===========================================================================
    
    virtual function void reset_statistics();
        independent_match_count = 0;
        independent_mismatch_count = 0;
        independent_timeout_count = 0;
        independent_crc_error_count = 0;
        uvm_match_count = 0;
        uvm_mismatch_count = 0;
        
        // Clear queues
        independent_expected_queue.delete();
        independent_actual_queue.delete();
        
        `uvm_info("INDEPENDENT_MONITOR", "Statistics reset", UVM_MEDIUM)
    endfunction
    
    virtual function void enable_cross_validation(bit enable = 1);
        cross_validation_enabled = enable;
        `uvm_info("INDEPENDENT_MONITOR", 
                 $sformatf("Cross-validation %s", enable ? "enabled" : "disabled"), UVM_MEDIUM)
    endfunction
    
    virtual function void set_timeout_threshold(time threshold);
        transaction_timeout_threshold = threshold;
        `uvm_info("INDEPENDENT_MONITOR", 
                 $sformatf("Timeout threshold set to %0t ns", threshold), UVM_MEDIUM)
    endfunction

endclass : independent_verification_monitor