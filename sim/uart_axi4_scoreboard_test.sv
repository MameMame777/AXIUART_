`timescale 1ns / 1ps

//==============================================================================
// UART-AXI4 Enhanced Test with Scoreboard Integration
// Part of Phase 3 Scoreboard Development
//
// Purpose: Demonstrate scoreboard integration with enhanced UVM reporting
// Features: Complete verification flow with transaction correlation
// Author: GitHub Copilot
// Created: October 11, 2025
//==============================================================================

import uvm_pkg::*;
`include "uvm_macros.svh"

//------------------------------------------------------------------------------
// Enhanced Test Class with Scoreboard Integration
//------------------------------------------------------------------------------

class uart_axi4_scoreboard_test extends enhanced_uart_axi4_base_test;
    
    // UVM Factory Registration
    `uvm_component_utils(uart_axi4_scoreboard_test)
    
    // Scoreboard component
    uart_axi4_scoreboard scoreboard;
    
    //--------------------------------------------------------------------------
    // Constructor
    //--------------------------------------------------------------------------
    
    function new(string name = "uart_axi4_scoreboard_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction: new
    
    //--------------------------------------------------------------------------
    // Build Phase - Enhanced with Scoreboard
    //--------------------------------------------------------------------------
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Create scoreboard
        scoreboard = uart_axi4_scoreboard::type_id::create("scoreboard", this);
        
        // Configure scoreboard reporting
        `uvm_info("SCOREBOARD_TEST_BUILD", "Scoreboard created and configured", UVM_MEDIUM)
        
    endfunction: build_phase
    
    //--------------------------------------------------------------------------
    // Connect Phase - Wire Scoreboard to Monitors
    //--------------------------------------------------------------------------
    
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect UART monitor to scoreboard
        env.uart_agent.monitor.ap.connect(scoreboard.uart_ap);
        
        // Connect AXI monitor to scoreboard
        env.axi_agent.monitor.ap.connect(scoreboard.axi_ap);
        
        `uvm_info("SCOREBOARD_TEST_CONNECT", "Scoreboard connected to monitors", UVM_MEDIUM)
        
    endfunction: connect_phase
    
    //--------------------------------------------------------------------------
    // Test Execution with Scoreboard Validation
    //--------------------------------------------------------------------------
    
    task run_phase(uvm_phase phase);
        uart_axi4_enhanced_sequence seq;
        
        phase.raise_objection(this);
        
        // Enhanced reporting for test start
        `uvm_info("SCOREBOARD_TEST_START", 
                 "Starting enhanced test with scoreboard verification", UVM_NONE)
        
        // Create and execute enhanced sequence
        seq = uart_axi4_enhanced_sequence::type_id::create("enhanced_seq");
        
        // Configure sequence for comprehensive testing
        seq.num_transactions = 50;           // Increased transaction count
        seq.enable_error_injection = 1;     // Test error scenarios
        seq.enable_burst_transactions = 1;  // Test burst operations
        
        // Execute sequence
        seq.start(env.uart_agent.sequencer);
        
        // Wait for all transactions to complete and correlate
        #10us; // Extended wait for correlation completion
        
        // Final scoreboard validation
        validate_scoreboard_results();
        
        `uvm_info("SCOREBOARD_TEST_COMPLETE", 
                 "Enhanced test with scoreboard verification completed", UVM_NONE)
        
        phase.drop_objection(this);
        
    endtask: run_phase
    
    //--------------------------------------------------------------------------
    // Scoreboard Validation
    //--------------------------------------------------------------------------
    
    function void validate_scoreboard_results();
        int successful_correlations;
        int failed_correlations;
        int data_mismatches;
        
        // Get scoreboard statistics
        successful_correlations = scoreboard.successful_correlations;
        failed_correlations = scoreboard.failed_correlations;
        data_mismatches = scoreboard.data_mismatches;
        
        // Validate results
        if (failed_correlations > 0 || data_mismatches > 0) begin
            `uvm_error("SCOREBOARD_VALIDATION_FAIL", 
                      $sformatf("Scoreboard detected issues: Failed correlations=%0d, Data mismatches=%0d", 
                               failed_correlations, data_mismatches))
        end else begin
            `uvm_info("SCOREBOARD_VALIDATION_PASS", 
                     $sformatf("Scoreboard validation successful: %0d transactions correlated", 
                              successful_correlations), UVM_NONE)
        end
        
    endfunction: validate_scoreboard_results

endclass: uart_axi4_scoreboard_test

//------------------------------------------------------------------------------
// Enhanced Sequence for Scoreboard Testing
//------------------------------------------------------------------------------

class uart_axi4_enhanced_sequence extends uvm_sequence #(uart_transaction);
    
    // UVM Factory Registration
    `uvm_object_utils(uart_axi4_enhanced_sequence)
    
    // Configuration parameters
    int num_transactions = 20;
    bit enable_error_injection = 0;
    bit enable_burst_transactions = 0;
    
    //--------------------------------------------------------------------------
    // Constructor
    //--------------------------------------------------------------------------
    
    function new(string name = "uart_axi4_enhanced_sequence");
        super.new(name);
    endfunction: new
    
    //--------------------------------------------------------------------------
    // Enhanced Sequence Body
    //--------------------------------------------------------------------------
    
    task body();
        uart_transaction req;
        
        `uvm_info("ENHANCED_SEQUENCE_START", 
                 $sformatf("Starting enhanced sequence with %0d transactions", num_transactions), 
                 UVM_MEDIUM)
        
        for (int i = 0; i < num_transactions; i++) begin
            
            // Create transaction
            req = uart_transaction::type_id::create($sformatf("req_%0d", i));
            
            // Randomize transaction
            start_item(req);
            
            if (!req.randomize()) begin
                `uvm_error("SEQUENCE_RANDOMIZE", $sformatf("Failed to randomize transaction %0d", i))
                continue;
            end
            
            // Apply test-specific constraints
            apply_test_constraints(req, i);
            
            // Send transaction
            finish_item(req);
            
            // Enhanced reporting per transaction
            `uvm_info("ENHANCED_SEQUENCE_TX", 
                     $sformatf("Transaction %0d: Cmd=%s, Addr=0x%08h", 
                              i, req.command.name(), req.address), 
                     UVM_HIGH)
            
            // Inter-transaction delay
            #($urandom_range(100, 1000) * 1ns);
        end
        
        `uvm_info("ENHANCED_SEQUENCE_COMPLETE", 
                 $sformatf("Enhanced sequence completed %0d transactions", num_transactions), 
                 UVM_MEDIUM)
        
    endtask: body
    
    //--------------------------------------------------------------------------
    // Test-Specific Constraint Application
    //--------------------------------------------------------------------------
    
    function void apply_test_constraints(uart_transaction req, int trans_num);
        
        // Address pattern for coverage
        case (trans_num % 4)
            0: req.address = 32'h0000_0000;  // Base address
            1: req.address = 32'h1000_0000;  // High address
            2: req.address = 32'hFFFF_FFFC;  // Boundary address
            3: req.address = $urandom();     // Random address
        endcase
        
        // Command pattern for coverage
        if (trans_num % 2 == 0) begin
            req.command = UART_CMD_WRITE;
        end else begin
            req.command = UART_CMD_READ;
        end
        
        // Burst transaction support
        if (enable_burst_transactions && (trans_num % 5 == 0)) begin
            req.burst_length = $urandom_range(2, 8);
        end
        
        // Error injection for negative testing
        if (enable_error_injection && (trans_num % 10 == 9)) begin
            req.inject_crc_error = 1;
        end
        
    endfunction: apply_test_constraints

endclass: uart_axi4_enhanced_sequence