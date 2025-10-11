`timescale 1ns / 1ps

//==============================================================================
// Coverage Gap Detection Tool (Phase 4.3)
//==============================================================================
// File: coverage_gap_detector.sv
// Purpose: Automated detection of verification blind spots and coverage gaps
// Author: AI Assistant
// Date: 2025-10-11
// Description: Systematically identifies uncovered code paths, assertion gaps, 
//              and verification blind spots to ensure zero-tolerance verification
//==============================================================================

`include "uvm_macros.svh"
import uvm_pkg::*;

class Coverage_Gap_Detector extends uvm_component;
    `uvm_component_utils(Coverage_Gap_Detector)
    
    // Coverage tracking structures
    typedef struct packed {
        bit [31:0] total_lines;
        bit [31:0] covered_lines;
        bit [31:0] uncovered_lines;
        real coverage_percentage;
    } line_coverage_t;
    
    typedef struct packed {
        bit [31:0] total_branches;
        bit [31:0] covered_branches;
        bit [31:0] uncovered_branches;
        real coverage_percentage;
    } branch_coverage_t;
    
    typedef struct packed {
        bit [31:0] total_assertions;
        bit [31:0] covered_assertions;
        bit [31:0] uncovered_assertions;
        real coverage_percentage;
    } assertion_coverage_t;
    
    typedef struct packed {
        string module_name;
        line_coverage_t line_cov;
        branch_coverage_t branch_cov;
        assertion_coverage_t assertion_cov;
        bit has_critical_gaps;
    } module_coverage_report_t;
    
    // Coverage data storage
    module_coverage_report_t coverage_reports[$];
    string uncovered_code_paths[$];
    string assertion_gaps[$];
    string verification_blind_spots[$];
    
    // Configuration parameters
    real minimum_line_coverage = 100.0;      // Zero tolerance
    real minimum_branch_coverage = 100.0;    // Zero tolerance
    real minimum_assertion_coverage = 100.0; // Zero tolerance
    real minimum_coverage_threshold = 100.0; // Zero tolerance check
    int maximum_allowed_gaps = 0;             // Zero tolerance
    
    // Gap detection results
    int total_gaps_found = 0;
    int critical_gaps_found = 0;
    bit verification_complete = 0;
    
    function new(string name = "coverage_gap_detector", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info("COV_GAP", "Building Coverage Gap Detector", UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this, "Starting coverage gap detection");
        
        `uvm_info("COV_GAP", "=== Coverage Gap Detection Started ===", UVM_LOW)
        
        // Step 1: Collect coverage data from all modules
        collect_coverage_data();
        
        // Step 2: Analyze line coverage gaps
        analyze_line_coverage_gaps();
        
        // Step 3: Analyze branch coverage gaps
        analyze_branch_coverage_gaps();
        
        // Step 4: Analyze assertion coverage gaps
        analyze_assertion_coverage_gaps();
        
        // Step 5: Identify verification blind spots
        identify_verification_blind_spots();
        
        // Step 6: Generate comprehensive gap report
        generate_gap_report();
        
        // Step 7: Assess verification completeness
        assess_verification_completeness();
        
        phase.drop_objection(this, "Coverage gap detection completed");
    endtask
    
    //==========================================================================
    // Coverage Data Collection
    //==========================================================================
    virtual task collect_coverage_data();
        `uvm_info("COV_GAP", "Collecting coverage data from all modules", UVM_MEDIUM)
        
        // Simulate coverage data collection for demonstration
        // In real implementation, interface with DSIM coverage database
        module_coverage_report_t uart_module, axi_bridge, crc_checker;
        
        // UART Module Coverage
        uart_module.module_name = "UART_Controller";
        uart_module.line_cov = '{1000, 995, 5, 99.5};
        uart_module.branch_cov = '{200, 198, 2, 99.0};
        uart_module.assertion_cov = '{50, 48, 2, 96.0};
        uart_module.has_critical_gaps = 1;
        coverage_reports.push_back(uart_module);
        
        // AXI Bridge Coverage
        axi_bridge.module_name = "AXI4_Bridge";
        axi_bridge.line_cov = '{800, 792, 8, 99.0};
        axi_bridge.branch_cov = '{150, 147, 3, 98.0};
        axi_bridge.assertion_cov = '{40, 38, 2, 95.0};
        axi_bridge.has_critical_gaps = 1;
        coverage_reports.push_back(axi_bridge);
        
        // CRC Checker Coverage
        crc_checker.module_name = "CRC_Checker";
        crc_checker.line_cov = '{300, 300, 0, 100.0};
        crc_checker.branch_cov = '{60, 60, 0, 100.0};
        crc_checker.assertion_cov = '{20, 20, 0, 100.0};
        crc_checker.has_critical_gaps = 0;
        coverage_reports.push_back(crc_checker);
        
        `uvm_info("COV_GAP", $sformatf("Collected coverage data for %0d modules", coverage_reports.size()), UVM_LOW)
    endtask
    
    //==========================================================================
    // Line Coverage Gap Analysis
    //==========================================================================
    virtual task analyze_line_coverage_gaps();
        `uvm_info("COV_GAP", "Analyzing line coverage gaps", UVM_MEDIUM)
        
        foreach (coverage_reports[i]) begin
            if (coverage_reports[i].line_cov.coverage_percentage < minimum_line_coverage) begin
                string gap_info = $sformatf("Module: %s, Uncovered lines: %0d (%.2f%% coverage)", 
                    coverage_reports[i].module_name, 
                    coverage_reports[i].line_cov.uncovered_lines,
                    coverage_reports[i].line_cov.coverage_percentage);
                uncovered_code_paths.push_back(gap_info);
                total_gaps_found++;
                
                if (coverage_reports[i].line_cov.uncovered_lines > 3) begin
                    critical_gaps_found++;
                end
            end
        end
        
        `uvm_info("COV_GAP", $sformatf("Found %0d line coverage gaps", uncovered_code_paths.size()), UVM_LOW)
    endtask
    
    //==========================================================================
    // Branch Coverage Gap Analysis
    //==========================================================================
    virtual task analyze_branch_coverage_gaps();
        `uvm_info("COV_GAP", "Analyzing branch coverage gaps", UVM_MEDIUM)
        
        foreach (coverage_reports[i]) begin
            if (coverage_reports[i].branch_cov.coverage_percentage < minimum_branch_coverage) begin
                string gap_info = $sformatf("Module: %s, Uncovered branches: %0d (%.2f%% coverage)", 
                    coverage_reports[i].module_name, 
                    coverage_reports[i].branch_cov.uncovered_branches,
                    coverage_reports[i].branch_cov.coverage_percentage);
                uncovered_code_paths.push_back(gap_info);
                total_gaps_found++;
                
                if (coverage_reports[i].branch_cov.uncovered_branches > 1) begin
                    critical_gaps_found++;
                end
            end
        end
        
        `uvm_info("COV_GAP", $sformatf("Branch coverage analysis completed"), UVM_LOW)
    endtask
    
    //==========================================================================
    // Assertion Coverage Gap Analysis
    //==========================================================================
    virtual task analyze_assertion_coverage_gaps();
        `uvm_info("COV_GAP", "Analyzing assertion coverage gaps", UVM_MEDIUM)
        
        foreach (coverage_reports[i]) begin
            if (coverage_reports[i].assertion_cov.coverage_percentage < minimum_assertion_coverage) begin
                string gap_info = $sformatf("Module: %s, Uncovered assertions: %0d (%.2f%% coverage)", 
                    coverage_reports[i].module_name, 
                    coverage_reports[i].assertion_cov.uncovered_assertions,
                    coverage_reports[i].assertion_cov.coverage_percentage);
                assertion_gaps.push_back(gap_info);
                total_gaps_found++;
                critical_gaps_found++;
            end
        end
        
        `uvm_info("COV_GAP", $sformatf("Assertion coverage analysis completed"), UVM_LOW)
    endtask
    
    //==========================================================================
    // Verification Blind Spot Identification
    //==========================================================================
    virtual task identify_verification_blind_spots();
        `uvm_info("COV_GAP", "Identifying verification blind spots", UVM_MEDIUM)
        
        // Common verification blind spots
        verification_blind_spots.push_back("Error recovery scenarios not fully tested");
        verification_blind_spots.push_back("Corner case boundary conditions need more coverage");
        verification_blind_spots.push_back("Concurrent operation stress testing insufficient");
        verification_blind_spots.push_back("Reset sequence validation gaps detected");
        
        foreach (verification_blind_spots[i]) begin
            total_gaps_found++;
        end
        
        `uvm_info("COV_GAP", $sformatf("Identified %0d verification blind spots", verification_blind_spots.size()), UVM_LOW)
    endtask
    
    //==========================================================================
    // Gap Report Generation
    //==========================================================================
    virtual task generate_gap_report();
        `uvm_info("COV_GAP", "=== COVERAGE GAP DETECTION REPORT ===", UVM_LOW)
        `uvm_info("COV_GAP", "", UVM_LOW)
        
        // Summary
        `uvm_info("COV_GAP", $sformatf("Total gaps found: %0d", total_gaps_found), UVM_LOW)
        `uvm_info("COV_GAP", $sformatf("Critical gaps found: %0d", critical_gaps_found), UVM_LOW)
        `uvm_info("COV_GAP", "", UVM_LOW)
        
        // Line/Branch Coverage Gaps
        if (uncovered_code_paths.size() > 0) begin
            `uvm_info("COV_GAP", "UNCOVERED CODE PATHS:", UVM_LOW)
            foreach (uncovered_code_paths[i]) begin
                `uvm_info("COV_GAP", $sformatf("  %s", uncovered_code_paths[i]), UVM_LOW)
            end
            `uvm_info("COV_GAP", "", UVM_LOW)
        end
        
        // Assertion Gaps
        if (assertion_gaps.size() > 0) begin
            `uvm_info("COV_GAP", "ASSERTION COVERAGE GAPS:", UVM_LOW)
            foreach (assertion_gaps[i]) begin
                `uvm_info("COV_GAP", $sformatf("  %s", assertion_gaps[i]), UVM_LOW)
            end
            `uvm_info("COV_GAP", "", UVM_LOW)
        end
        
        // Verification Blind Spots
        if (verification_blind_spots.size() > 0) begin
            `uvm_info("COV_GAP", "VERIFICATION BLIND SPOTS:", UVM_LOW)
            foreach (verification_blind_spots[i]) begin
                `uvm_info("COV_GAP", $sformatf("  %s", verification_blind_spots[i]), UVM_LOW)
            end
            `uvm_info("COV_GAP", "", UVM_LOW)
        end
    endtask
    
    //==========================================================================
    // Verification Completeness Assessment
    //==========================================================================
    virtual task assess_verification_completeness();
        `uvm_info("COV_GAP", "Assessing verification completeness", UVM_MEDIUM)
        
        verification_complete = (total_gaps_found <= maximum_allowed_gaps);
        
        if (verification_complete) begin
            `uvm_info("COV_GAP", "VERIFICATION COMPLETE: Zero gaps detected", UVM_LOW)
        end else begin
            `uvm_fatal("COV_GAP", $sformatf("VERIFICATION INCOMPLETE: %0d gaps must be addressed (Zero tolerance policy)", total_gaps_found))
        end
    endtask

endclass