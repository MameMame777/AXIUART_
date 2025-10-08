`timescale 1ns / 1ps

/*
 * AXI4-Lite Basic Operation Test
 * 
 * Purpose: Verify fundamental AXI4-Lite Master and Register_Block functionality
 *          BEFORE attempting full system integration tests
 * 
 * Test Cases:
 * 1. Basic AXI4-Lite write transaction to Register_Block
 * 2. Basic AXI4-Lite read transaction from Register_Block  
 * 3. Verify write data reaches register and can be read back
 * 4. Test REG_TEST registers specifically
 * 
 * This should be the FIRST test to pass before moving to system-level debugging
 */

`include "uvm_macros.svh"
import uvm_pkg::*;
import axi4_lite_pkg::*;

// Test for AXI4-Lite basic read/write operations
class axi_basic_test extends uvm_test;
    `uvm_component_utils(axi_basic_test)
    
    // Test environment
    axi4_lite_env env;
    
    // Test configuration
    axi4_lite_config cfg;
    
    function new(string name = "axi_basic_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Create configuration
        cfg = axi4_lite_config::type_id::create("cfg", this);
        cfg.has_scoreboard = 1;
        cfg.has_coverage = 1;
        
        // Set configuration in UVM database
        uvm_config_db#(axi4_lite_config)::set(this, "*", "cfg", cfg);
        
        // Create environment  
        env = axi4_lite_env::type_id::create("env", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        axi_basic_sequence basic_seq;
        
        phase.raise_objection(this);
        
        `uvm_info("AXI_BASIC_TEST", "Starting AXI4-Lite Basic Operation Test", UVM_LOW)
        
        // Create and run basic AXI sequence
        basic_seq = axi_basic_sequence::type_id::create("basic_seq");
        basic_seq.start(env.agent.sequencer);
        
        #1000; // Allow time for final transactions
        
        `uvm_info("AXI_BASIC_TEST", "AXI4-Lite Basic Operation Test Completed", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass

// Basic AXI4-Lite sequence for fundamental operations
class axi_basic_sequence extends uvm_sequence #(axi4_lite_item);
    `uvm_object_utils(axi_basic_sequence)
    
    function new(string name = "axi_basic_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_lite_item req;
        
        `uvm_info("AXI_BASIC_SEQ", "Starting Basic AXI4-Lite Transactions", UVM_LOW)
        
        // Test 1: Write to REG_TEST_0 (0x00001020)
        `uvm_info("AXI_BASIC_SEQ", "Test 1: Write 0x12345678 to REG_TEST_0 (0x00001020)", UVM_LOW)
        req = axi4_lite_item::type_id::create("req");
        start_item(req);
        req.trans_type = AXI_WRITE;
        req.addr = 32'h00001020;
        req.data = 32'h12345678;
        req.strb = 4'hF;
        req.prot = 3'b000;
        finish_item(req);
        
        #100; // Wait between transactions
        
        // Test 2: Read back from REG_TEST_0
        `uvm_info("AXI_BASIC_SEQ", "Test 2: Read back from REG_TEST_0 (0x00001020)", UVM_LOW)
        req = axi4_lite_item::type_id::create("req");
        start_item(req);
        req.trans_type = AXI_READ;
        req.addr = 32'h00001020;
        req.prot = 3'b000;
        finish_item(req);
        
        #100;
        
        // Test 3: Write to REG_TEST_1 (0x00001024)
        `uvm_info("AXI_BASIC_SEQ", "Test 3: Write 0xDEADBEEF to REG_TEST_1 (0x00001024)", UVM_LOW)
        req = axi4_lite_item::type_id::create("req");
        start_item(req);
        req.trans_type = AXI_WRITE;
        req.addr = 32'h00001024;
        req.data = 32'hDEADBEEF;
        req.strb = 4'hF;
        req.prot = 3'b000;
        finish_item(req);
        
        #100;
        
        // Test 4: Read back from REG_TEST_1
        `uvm_info("AXI_BASIC_SEQ", "Test 4: Read back from REG_TEST_1 (0x00001024)", UVM_LOW)
        req = axi4_lite_item::type_id::create("req");
        start_item(req);
        req.trans_type = AXI_READ;
        req.addr = 32'h00001024;
        req.prot = 3'b000;
        finish_item(req);
        
        #100;
        
        // Test 5: Multiple register access pattern
        `uvm_info("AXI_BASIC_SEQ", "Test 5: Multiple register write/read pattern", UVM_LOW)
        
        // Write different values to all REG_TEST registers
        for (int i = 0; i < 4; i++) begin
            req = axi4_lite_item::type_id::create("req");
            start_item(req);
            req.trans_type = AXI_WRITE;
            req.addr = 32'h00001020 + (i * 4);
            req.data = 32'h11111111 * (i + 1); // 0x11111111, 0x22222222, etc.
            req.strb = 4'hF;
            req.prot = 3'b000;
            finish_item(req);
            #50;
        end
        
        // Read back all values to verify
        for (int i = 0; i < 4; i++) begin
            req = axi4_lite_item::type_id::create("req");
            start_item(req);
            req.trans_type = AXI_READ;
            req.addr = 32'h00001020 + (i * 4);
            req.prot = 3'b000;
            finish_item(req);
            #50;
        end
        
        `uvm_info("AXI_BASIC_SEQ", "Basic AXI4-Lite Sequence Completed", UVM_LOW)
    endtask
    
endclass