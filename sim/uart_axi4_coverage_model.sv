`timescale 1ns / 1ps

//==============================================================================
// UART-AXI4 Coverage Model for Scoreboard Integration
// Part of Phase 3 Scoreboard Development
//
// Purpose: Comprehensive functional coverage for UART-to-AXI verification
// Features: Transaction coverage, cross-coverage, protocol coverage
// Author: GitHub Copilot
// Created: October 11, 2025
//==============================================================================

import uvm_pkg::*;
`include "uvm_macros.svh"

//------------------------------------------------------------------------------
// Coverage Model Class
//------------------------------------------------------------------------------

class uart_axi4_coverage_model extends uvm_subscriber #(uart_transaction_record_t);
    
    // UVM Factory Registration
    `uvm_component_utils(uart_axi4_coverage_model)
    
    //--------------------------------------------------------------------------
    // Coverage Groups
    //--------------------------------------------------------------------------
    
    // UART Command Coverage
    covergroup uart_command_cg;
        option.per_instance = 1;
        option.comment = "UART Command Coverage";
        
        command_cp: coverpoint sample_trans.command {
            bins write_cmd = {UART_CMD_WRITE};
            bins read_cmd  = {UART_CMD_READ};
            bins other_cmd = default;
        }
        
        address_cp: coverpoint sample_trans.address {
            bins low_addr    = {[32'h0000_0000:32'h0FFF_FFFF]};
            bins mid_addr    = {[32'h1000_0000:32'h7FFF_FFFF]};
            bins high_addr   = {[32'h8000_0000:32'hEFFF_FFFF]};
            bins boundary_addr = {32'hFFFF_FFFC, 32'hFFFF_FFF8, 32'hFFFF_FFF4, 32'hFFFF_FFF0};
            bins zero_addr   = {32'h0000_0000};
            bins max_addr    = {32'hFFFF_FFFC};
        }
        
        data_size_cp: coverpoint sample_trans.data.size() {
            bins single_byte = {1};
            bins small_data  = {[2:4]};
            bins medium_data = {[5:16]};
            bins large_data  = {[17:64]};
            bins max_data    = {[65:256]};
        }
        
        crc_status_cp: coverpoint sample_trans.crc_valid {
            bins crc_valid   = {1};
            bins crc_invalid = {0};
        }
        
        // Cross-coverage: Command vs Address range
        cmd_addr_cross: cross command_cp, address_cp {
            option.comment = "Command and Address Cross Coverage";
        }
        
        // Cross-coverage: Command vs Data size
        cmd_size_cross: cross command_cp, data_size_cp {
            option.comment = "Command and Data Size Cross Coverage";
        }
        
        // Cross-coverage: CRC status vs Command
        crc_cmd_cross: cross crc_status_cp, command_cp {
            option.comment = "CRC Status and Command Cross Coverage";
            ignore_bins invalid_read_crc = binsof(crc_status_cp.crc_invalid) && binsof(command_cp.read_cmd);
        }
        
    endgroup: uart_command_cg
    
    // AXI Transaction Coverage (connected via scoreboard)
    covergroup axi_transaction_cg;
        option.per_instance = 1;
        option.comment = "AXI Transaction Coverage";
        
        trans_type_cp: coverpoint sample_axi_trans.trans_type {
            bins axi_write = {AXI_WRITE};
            bins axi_read  = {AXI_READ};
        }
        
        burst_length_cp: coverpoint sample_axi_trans.burst_length {
            bins single_beat = {1};
            bins short_burst = {[2:4]};
            bins medium_burst = {[5:8]};
            bins long_burst = {[9:16]};
        }
        
        response_cp: coverpoint sample_axi_trans.response {
            bins okay     = {AXI_OKAY};
            bins exokay   = {AXI_EXOKAY};
            bins slverr   = {AXI_SLVERR};
            bins decerr   = {AXI_DECERR};
        }
        
        // Cross-coverage: Transaction type vs Response
        type_resp_cross: cross trans_type_cp, response_cp {
            option.comment = "Transaction Type and Response Cross Coverage";
        }
        
        // Cross-coverage: Burst length vs Response
        burst_resp_cross: cross burst_length_cp, response_cp {
            option.comment = "Burst Length and Response Cross Coverage";
        }
        
    endgroup: axi_transaction_cg
    
    // Protocol Timing Coverage
    covergroup timing_coverage_cg;
        option.per_instance = 1;
        option.comment = "Protocol Timing Coverage";
        
        correlation_latency_cp: coverpoint correlation_latency_ns {
            bins fast_corr     = {[0:100]};
            bins normal_corr   = {[101:1000]};
            bins slow_corr     = {[1001:10000]};
            bins timeout_corr  = {[10001:100000]};
        }
        
        inter_trans_gap_cp: coverpoint inter_transaction_gap_ns {
            bins no_gap        = {[0:10]};
            bins short_gap     = {[11:100]};
            bins medium_gap    = {[101:1000]};
            bins long_gap      = {[1001:10000]};
        }
        
        // Cross-coverage: Correlation latency vs Command type
        latency_cmd_cross: cross correlation_latency_cp, sample_trans.command {
            option.comment = "Correlation Latency and Command Cross Coverage";
        }
        
    endgroup: timing_coverage_cg
    
    // Error Scenario Coverage
    covergroup error_scenario_cg;
        option.per_instance = 1;
        option.comment = "Error Scenario Coverage";
        
        error_type_cp: coverpoint current_error_type {
            bins no_error         = {NO_ERROR};
            bins crc_error        = {CRC_ERROR};
            bins timeout_error    = {TIMEOUT_ERROR};
            bins protocol_error   = {PROTOCOL_ERROR};
            bins data_mismatch    = {DATA_MISMATCH_ERROR};
            bins address_error    = {ADDRESS_ERROR};
        }
        
        recovery_type_cp: coverpoint error_recovery_type {
            bins auto_recovery    = {AUTO_RECOVERY};
            bins manual_recovery  = {MANUAL_RECOVERY};
            bins no_recovery      = {NO_RECOVERY};
        }
        
        // Cross-coverage: Error type vs Recovery
        error_recovery_cross: cross error_type_cp, recovery_type_cp {
            option.comment = "Error Type and Recovery Cross Coverage";
        }
        
    endgroup: error_scenario_cg
    
    //--------------------------------------------------------------------------
    // Coverage Data Members
    //--------------------------------------------------------------------------
    
    // Sample transaction data
    uart_transaction_record_t sample_trans;
    axi_transaction_record_t  sample_axi_trans;
    
    // Timing measurements
    int correlation_latency_ns;
    int inter_transaction_gap_ns;
    time last_transaction_time;
    
    // Error tracking
    error_type_t current_error_type;
    recovery_type_t error_recovery_type;
    
    // Statistics
    int total_transactions;
    int successful_correlations;
    int failed_correlations;
    real coverage_percentage;
    
    //--------------------------------------------------------------------------
    // Coverage Types
    //--------------------------------------------------------------------------
    
    typedef enum {
        NO_ERROR,
        CRC_ERROR,
        TIMEOUT_ERROR,
        PROTOCOL_ERROR,
        DATA_MISMATCH_ERROR,
        ADDRESS_ERROR
    } error_type_t;
    
    typedef enum {
        AUTO_RECOVERY,
        MANUAL_RECOVERY,
        NO_RECOVERY
    } recovery_type_t;
    
    //--------------------------------------------------------------------------
    // Constructor
    //--------------------------------------------------------------------------
    
    function new(string name = "uart_axi4_coverage_model", uvm_component parent = null);
        super.new(name, parent);
        
        // Initialize coverage groups
        uart_command_cg = new();
        axi_transaction_cg = new();
        timing_coverage_cg = new();
        error_scenario_cg = new();
        
        // Initialize variables
        total_transactions = 0;
        successful_correlations = 0;
        failed_correlations = 0;
        last_transaction_time = 0;
        current_error_type = NO_ERROR;
        error_recovery_type = NO_RECOVERY;
        
        `uvm_info("COVERAGE_MODEL_INIT", "Coverage model initialized", UVM_MEDIUM)
        
    endfunction: new
    
    //--------------------------------------------------------------------------
    // Write Method - Sample Coverage
    //--------------------------------------------------------------------------
    
    function void write(uart_transaction_record_t t);
        
        // Update sample data
        sample_trans = t;
        total_transactions++;
        
        // Calculate timing metrics
        if (last_transaction_time != 0) begin
            inter_transaction_gap_ns = int'(($time - last_transaction_time) / 1ns);
        end
        last_transaction_time = $time;
        
        // Sample UART coverage
        uart_command_cg.sample();
        
        // Sample timing coverage
        timing_coverage_cg.sample();
        
        // Sample error coverage if applicable
        if (current_error_type != NO_ERROR) begin
            error_scenario_cg.sample();
        end
        
        // Enhanced reporting
        `uvm_info("COVERAGE_SAMPLE", 
                 $sformatf("Sampled transaction %0d: Cmd=%s, Addr=0x%08h, Coverage=%.2f%%", 
                          total_transactions, 
                          sample_trans.command.name(), 
                          sample_trans.address, 
                          get_coverage_percentage()), 
                 UVM_HIGH)
        
    endfunction: write
    
    //--------------------------------------------------------------------------
    // AXI Transaction Sampling
    //--------------------------------------------------------------------------
    
    function void sample_axi_transaction(axi_transaction_record_t axi_trans, int correlation_latency);
        
        // Update sample data
        sample_axi_trans = axi_trans;
        correlation_latency_ns = correlation_latency;
        
        // Sample AXI coverage
        axi_transaction_cg.sample();
        
        // Update correlation statistics
        successful_correlations++;
        
        `uvm_info("COVERAGE_AXI_SAMPLE", 
                 $sformatf("Sampled AXI correlation: Type=%s, Resp=%s, Latency=%0dns", 
                          axi_trans.trans_type.name(), 
                          axi_trans.response.name(), 
                          correlation_latency), 
                 UVM_HIGH)
        
    endfunction: sample_axi_transaction
    
    //--------------------------------------------------------------------------
    // Error Scenario Sampling
    //--------------------------------------------------------------------------
    
    function void sample_error_scenario(error_type_t error_type, recovery_type_t recovery_type);
        
        current_error_type = error_type;
        error_recovery_type = recovery_type;
        
        // Sample error coverage
        error_scenario_cg.sample();
        
        // Update statistics
        if (error_type != NO_ERROR) begin
            failed_correlations++;
        end
        
        `uvm_info("COVERAGE_ERROR_SAMPLE", 
                 $sformatf("Sampled error scenario: Error=%s, Recovery=%s", 
                          error_type.name(), 
                          recovery_type.name()), 
                 UVM_MEDIUM)
        
    endfunction: sample_error_scenario
    
    //--------------------------------------------------------------------------
    // Coverage Analysis Functions
    //--------------------------------------------------------------------------
    
    function real get_coverage_percentage();
        real uart_cov = uart_command_cg.get_coverage();
        real axi_cov = axi_transaction_cg.get_coverage();
        real timing_cov = timing_coverage_cg.get_coverage();
        real error_cov = error_scenario_cg.get_coverage();
        
        // Weighted average
        coverage_percentage = (uart_cov * 0.4) + (axi_cov * 0.3) + (timing_cov * 0.2) + (error_cov * 0.1);
        return coverage_percentage;
    endfunction: get_coverage_percentage
    
    function void print_coverage_summary();
        real uart_cov = uart_command_cg.get_coverage();
        real axi_cov = axi_transaction_cg.get_coverage();
        real timing_cov = timing_coverage_cg.get_coverage();
        real error_cov = error_scenario_cg.get_coverage();
        real total_cov = get_coverage_percentage();
        
        `uvm_info("COVERAGE_SUMMARY", 
                 $sformatf("\n=== Coverage Summary ===\n" +
                          "UART Command Coverage:    %.2f%%\n" +
                          "AXI Transaction Coverage: %.2f%%\n" +
                          "Timing Coverage:          %.2f%%\n" +
                          "Error Scenario Coverage:  %.2f%%\n" +
                          "Total Weighted Coverage:  %.2f%%\n" +
                          "Total Transactions:       %0d\n" +
                          "Successful Correlations:  %0d\n" +
                          "Failed Correlations:      %0d\n" +
                          "======================="), 
                 UVM_NONE)
        
    endfunction: print_coverage_summary
    
    //--------------------------------------------------------------------------
    // Report Phase - Coverage Reporting
    //--------------------------------------------------------------------------
    
    function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        
        // Print comprehensive coverage summary
        print_coverage_summary();
        
        // Check coverage goals
        if (get_coverage_percentage() < 90.0) begin
            `uvm_warning("COVERAGE_GOAL", 
                        $sformatf("Coverage goal not met: %.2f%% < 90.0%%", get_coverage_percentage()))
        end else begin
            `uvm_info("COVERAGE_GOAL", 
                     $sformatf("Coverage goal achieved: %.2f%% >= 90.0%%", get_coverage_percentage()), 
                     UVM_NONE)
        end
        
    endfunction: report_phase

endclass: uart_axi4_coverage_model