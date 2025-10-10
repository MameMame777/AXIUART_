`timescale 1ns / 1ps

// Phase 3 Enhanced Coverage Model with Correlation Analysis
// Created: October 11, 2025
// Purpose: Advanced coverage integration with transaction correlation

class uart_axi4_phase3_coverage extends uvm_subscriber #(uart_frame_transaction);
    
    `uvm_component_utils(uart_axi4_phase3_coverage)
    
    // Configuration and correlation engine reference
    uart_axi4_env_config cfg;
    uart_axi4_correlation_engine correlation_engine;
    
    // Enhanced transaction storage for temporal analysis
    uart_frame_transaction recent_transactions[$];
    time transaction_timestamps[$];
    
    // Phase 3 Advanced Coverage Groups
    
    // 1. Transaction Correlation Coverage
    covergroup correlation_coverage with function sample(correlation_record_t record);
        
        // Correlation timing analysis
        correlation_latency: coverpoint record.correlation_latency {
            bins immediate = {[0:1000]};           // < 1us
            bins fast = {[1001:10000]};            // 1-10us
            bins normal = {[10001:100000]};        // 10-100us
            bins slow = {[100001:1000000]};        // 100us-1ms
            illegal_bins timeout = {[1000001:$]};  // > 1ms
        }
        
        // UART to AXI transaction mapping
        uart_axi_mapping: coverpoint record.mapping_type {
            bins single_write = {MAPPING_SINGLE_WRITE};
            bins single_read = {MAPPING_SINGLE_READ};
            bins burst_write = {MAPPING_BURST_WRITE};
            bins burst_read = {MAPPING_BURST_READ};
            bins complex_mapping = {MAPPING_COMPLEX};
        }
        
        // Success rate tracking
        correlation_success: coverpoint record.correlation_success {
            bins matched = {1'b1};
            bins unmatched = {1'b0};
        }
        
        // Cross coverage: mapping type vs latency
        mapping_latency: cross uart_axi_mapping, correlation_latency {
            ignore_bins no_timeout = binsof(correlation_latency.timeout);
        }
        
        // Cross coverage: success vs timing
        success_timing: cross correlation_success, correlation_latency;
        
    endgroup
    
    // 2. Protocol Efficiency Coverage
    covergroup efficiency_coverage with function sample(uart_frame_transaction tr);
        
        // Throughput analysis
        data_efficiency: coverpoint calculate_data_efficiency(tr) {
            bins excellent = {[90:100]};    // 90-100% efficiency
            bins good = {[70:89]};          // 70-89% efficiency
            bins fair = {[50:69]};          // 50-69% efficiency
            bins poor = {[0:49]};           // < 50% efficiency
        }
        
        // Pipeline utilization
        pipeline_depth: coverpoint get_pipeline_depth() {
            bins empty = {0};
            bins light = {[1:2]};
            bins moderate = {[3:5]};
            bins heavy = {[6:10]};
            bins saturated = {[11:$]};
        }
        
        // Burst optimization
        burst_efficiency: coverpoint tr.cmd[3:0] iff (tr.cmd[6]) { // Only for increment mode
            bins optimal_8 = {[7:15]};       // Good burst length
            bins suboptimal = {[1:6]};       // Short bursts
            bins single = {0};               // No burst benefit
        }
        
    endgroup
    
    // 3. Error Pattern Coverage
    covergroup error_pattern_coverage with function sample(uart_frame_transaction tr);
        
        // Error type distribution
        error_types: coverpoint tr.response_status {
            bins no_error = {STATUS_OK};
            bins crc_errors = {STATUS_CRC_ERR};
            bins protocol_errors = {STATUS_CMD_INV, STATUS_ADDR_ALIGN};
            bins system_errors = {STATUS_TIMEOUT, STATUS_AXI_SLVERR};
            bins resource_errors = {STATUS_BUSY, STATUS_LEN_RANGE};
        }
        
        // Error recovery patterns
        error_sequence: coverpoint get_error_sequence_pattern() {
            bins isolated_error = {ERROR_ISOLATED};
            bins error_burst = {ERROR_BURST};
            bins error_recovery = {ERROR_RECOVERY};
            bins error_cascade = {ERROR_CASCADE};
        }
        
        // Cross coverage: command type vs error type
        cmd_error: cross tr.cmd[7], error_types;
        
    endgroup
    
    // 4. Advanced Protocol Interaction Coverage
    covergroup protocol_interaction_coverage;
        
        // Back-to-back transaction timing
        transaction_spacing: coverpoint get_transaction_spacing() {
            bins immediate = {[0:10]};          // Immediate follow-up
            bins close = {[11:100]};            // Close timing
            bins normal = {[101:1000]};         // Normal spacing
            bins spaced = {[1001:10000]};       // Well spaced
            bins isolated = {[10001:$]};        // Isolated transactions
        }
        
        // Command sequence patterns
        command_sequences: coverpoint get_command_sequence() {
            bins write_read_same = {SEQ_WR_SAME};
            bins write_read_diff = {SEQ_WR_DIFF};
            bins read_sequence = {SEQ_RD_SEQ};
            bins write_sequence = {SEQ_WR_SEQ};
            bins mixed_sequence = {SEQ_MIXED};
        }
        
        // Address pattern coverage
        address_patterns: coverpoint get_address_pattern() {
            bins sequential = {ADDR_SEQUENTIAL};
            bins random = {ADDR_RANDOM};
            bins stride_2 = {ADDR_STRIDE_2};
            bins stride_4 = {ADDR_STRIDE_4};
            bins fixed = {ADDR_FIXED};
        }
        
    endgroup
    
    // Constructor
    function new(string name = "uart_axi4_phase3_coverage", uvm_component parent = null);
        super.new(name, parent);
        
        // Initialize coverage groups
        correlation_coverage = new();
        efficiency_coverage = new();
        error_pattern_coverage = new();
        protocol_interaction_coverage = new();
        
    endfunction
    
    // Build phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        if (!uvm_config_db#(uart_axi4_env_config)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("PHASE3_COV", "Could not get env_config from config_db")
        end
        
        `uvm_info("PHASE3_COV", "Phase 3 enhanced coverage model initialized", UVM_LOW)
    endfunction
    
    // Connect phase - get correlation engine reference
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Get correlation engine from parent scoreboard
        if ($cast(correlation_engine, uvm_top.find("*.scoreboard.correlation_engine"))) begin
            `uvm_info("PHASE3_COV", "Connected to correlation engine", UVM_LOW)
        end else begin
            `uvm_warning("PHASE3_COV", "Could not connect to correlation engine")
        end
    endfunction
    
    // Main write function - enhanced with Phase 3 analysis
    virtual function void write(uart_frame_transaction t);
        uart_frame_transaction tr;
        
        // Clone transaction
        $cast(tr, t.clone());
        
        // Store for temporal analysis
        recent_transactions.push_back(tr);
        transaction_timestamps.push_back($time);
        
        // Limit history size
        if (recent_transactions.size() > 100) begin
            recent_transactions.pop_front();
            transaction_timestamps.pop_front();
        end
        
        // Sample all coverage groups
        efficiency_coverage.sample(tr);
        error_pattern_coverage.sample(tr);
        protocol_interaction_coverage.sample();
        
        // Sample correlation coverage if correlation engine is available
        if (correlation_engine != null) begin
            correlation_record_t record = correlation_engine.get_latest_correlation();
            if (record.valid) begin
                correlation_coverage.sample(record);
            end
        end
        
        `uvm_info("PHASE3_COV", $sformatf("Sampled coverage for CMD=0x%02x, ADDR=0x%08x", 
                 tr.cmd, tr.addr), UVM_HIGH)
    endfunction
    
    // Enhanced analysis functions
    
    // Calculate data transfer efficiency
    virtual function int calculate_data_efficiency(uart_frame_transaction tr);
        int useful_bytes, total_bytes;
        int frame_overhead = 8; // SOF + CMD + ADDR(4) + CRC
        
        useful_bytes = (tr.cmd[3:0] + 1) * (1 << tr.cmd[5:4]);
        total_bytes = frame_overhead + useful_bytes;
        
        return (useful_bytes * 100) / total_bytes;
    endfunction
    
    // Get current pipeline depth
    virtual function int get_pipeline_depth();
        // This would interface with the DUT to get actual pipeline status
        // For now, return based on recent transaction count
        return recent_transactions.size();
    endfunction
    
    // Analyze error sequence patterns
    virtual function error_sequence_t get_error_sequence_pattern();
        int error_count = 0;
        int recent_window = 5;
        
        // Count errors in recent window
        for (int i = recent_transactions.size()-recent_window; i < recent_transactions.size(); i++) begin
            if (i >= 0 && recent_transactions[i].response_status != STATUS_OK) begin
                error_count++;
            end
        end
        
        case (error_count)
            0: return ERROR_ISOLATED;
            1: return ERROR_ISOLATED;
            2,3: return ERROR_RECOVERY;
            default: return ERROR_BURST;
        endcase
    endfunction
    
    // Calculate transaction spacing
    virtual function int get_transaction_spacing();
        if (transaction_timestamps.size() < 2) return 0;
        
        time last_spacing = transaction_timestamps[$] - transaction_timestamps[$-1];
        return last_spacing / 1ns; // Convert to ns
    endfunction
    
    // Analyze command sequences
    virtual function command_sequence_t get_command_sequence();
        if (recent_transactions.size() < 2) return SEQ_MIXED;
        
        uart_frame_transaction last_tr = recent_transactions[$-1];
        uart_frame_transaction curr_tr = recent_transactions[$];
        
        // Simplified sequence analysis
        if (last_tr.cmd[7] == 0 && curr_tr.cmd[7] == 1 && last_tr.addr == curr_tr.addr) begin
            return SEQ_WR_SAME; // Write followed by read to same address
        end else if (last_tr.cmd[7] == curr_tr.cmd[7]) begin
            return last_tr.cmd[7] ? SEQ_RD_SEQ : SEQ_WR_SEQ;
        end else begin
            return SEQ_MIXED;
        end
    endfunction
    
    // Analyze address patterns
    virtual function address_pattern_t get_address_pattern();
        if (recent_transactions.size() < 3) return ADDR_RANDOM;
        
        int addr_diff1 = recent_transactions[$-1].addr - recent_transactions[$-2].addr;
        int addr_diff2 = recent_transactions[$].addr - recent_transactions[$-1].addr;
        
        if (addr_diff1 == addr_diff2) begin
            case (addr_diff1)
                1: return ADDR_SEQUENTIAL;
                2: return ADDR_STRIDE_2;
                4: return ADDR_STRIDE_4;
                0: return ADDR_FIXED;
                default: return ADDR_RANDOM;
            endcase
        end else begin
            return ADDR_RANDOM;
        end
    endfunction
    
    // Report phase with enhanced metrics
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        
        `uvm_info("PHASE3_COV", "=== PHASE 3 ENHANCED COVERAGE REPORT ===", UVM_LOW)
        `uvm_info("PHASE3_COV", $sformatf("Correlation Coverage: %.2f%%", 
                 correlation_coverage.get_coverage()), UVM_LOW)
        `uvm_info("PHASE3_COV", $sformatf("Efficiency Coverage: %.2f%%", 
                 efficiency_coverage.get_coverage()), UVM_LOW)
        `uvm_info("PHASE3_COV", $sformatf("Error Pattern Coverage: %.2f%%", 
                 error_pattern_coverage.get_coverage()), UVM_LOW)
        `uvm_info("PHASE3_COV", $sformatf("Protocol Interaction Coverage: %.2f%%", 
                 protocol_interaction_coverage.get_coverage()), UVM_LOW)
        
        real total_coverage = (correlation_coverage.get_coverage() + 
                              efficiency_coverage.get_coverage() + 
                              error_pattern_coverage.get_coverage() + 
                              protocol_interaction_coverage.get_coverage()) / 4.0;
        
        `uvm_info("PHASE3_COV", $sformatf("Total Phase 3 Coverage: %.2f%%", total_coverage), UVM_LOW)
        
        if (total_coverage < 80.0) begin
            `uvm_warning("PHASE3_COV", "Phase 3 coverage below 80% - consider additional testing")
        end
    endfunction
    
endclass : uart_axi4_phase3_coverage