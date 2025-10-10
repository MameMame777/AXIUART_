`timescale 1ns / 1ps

// Complete UART-AXI Bridge Register Pattern Test
// Tests complete data flow: UART → Bridge → AXI → Register
// Uses all5, allA, allF patterns for proper bit validation

import uvm_pkg::*;
`include "uvm_macros.svh"

class uart_axi_bridge_pattern_test extends uvm_test;
    `uvm_component_utils(uart_axi_bridge_pattern_test)
    
    // Environment components
    typedef virtual axi4_lite_if vif_t;
    vif_t vif;
    
    function new(string name = "uart_axi_bridge_pattern_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get virtual interface
        if (!uvm_config_db#(vif_t)::get(this, "", "axi_vif", vif)) begin
            `uvm_fatal("CONFIG_ERROR", "Virtual interface not found in config DB")
        end
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        uart_register_pattern_sequence seq;
        
        phase.raise_objection(this);
        
        `uvm_info("TEST", "=== UART-AXI BRIDGE PATTERN TEST START ===", UVM_LOW)
        
        // Wait for reset deassertion
        wait(!vif.rst);
        repeat(10) @(posedge vif.clk);
        
        // Direct AXI register tests first (baseline)
        test_direct_axi_patterns();
        
        // UART-AXI Bridge tests (full data flow)
        seq = uart_register_pattern_sequence::type_id::create("uart_reg_seq");
        seq.start(null); // Note: This needs proper sequencer setup
        
        `uvm_info("TEST", "=== UART-AXI BRIDGE PATTERN TEST COMPLETE ===", UVM_LOW)
        
        repeat(50) @(posedge vif.clk);
        phase.drop_objection(this);
    endtask
    
    // Direct AXI tests as baseline comparison
    virtual task test_direct_axi_patterns();
        logic [31:0] read_data;
        logic [31:0] test_patterns[7] = {
            32'h55555555, // all5 - critical bit validation
            32'hAAAAAAAA, // allA - inverted bit validation  
            32'hFFFFFFFF, // allF - all ones
            32'h12345678, // sequential
            32'hDEADBEEF, // classic pattern
            32'hCAFEBABE, // coffee pattern
            32'hFEEDFACE  // feed face pattern
        };
        logic [31:0] test_addresses[4] = {
            32'h0000_1020, // TEST_0
            32'h0000_1024, // TEST_1
            32'h0000_1028, // TEST_2
            32'h0000_102C  // TEST_3
        };
        
        `uvm_info("TEST", "--- Direct AXI Pattern Tests (Baseline) ---", UVM_LOW)
        
        // Test each register with critical patterns
        foreach (test_addresses[addr_idx]) begin
            foreach (test_patterns[pat_idx]) begin
                // Write pattern
                axi_write(test_addresses[addr_idx], test_patterns[pat_idx], 4'b1111);
                
                // Read back and verify
                axi_read(test_addresses[addr_idx], read_data);
                
                if (read_data === test_patterns[pat_idx]) begin
                    `uvm_info("TEST", 
                             $sformatf("Direct AXI: Addr=0x%08X, Pattern=0x%08X: PASS", 
                                      test_addresses[addr_idx], test_patterns[pat_idx]), UVM_MEDIUM)
                end else begin
                    `uvm_error("TEST", 
                              $sformatf("Direct AXI: Addr=0x%08X, Expected=0x%08X, Got=0x%08X: FAIL", 
                                       test_addresses[addr_idx], test_patterns[pat_idx], read_data))
                end
            end
        end
        
        `uvm_info("TEST", "Direct AXI pattern tests complete", UVM_LOW)
    endtask
    
    // Helper task: AXI Write
    virtual task axi_write(logic [31:0] addr, logic [31:0] data, logic [3:0] strb);
        `uvm_info("TEST", $sformatf("AXI WRITE: addr=0x%08X, data=0x%08X", addr, data), UVM_HIGH)
        
        fork
            // Address channel
            begin
                vif.awvalid <= 1'b1;
                vif.awaddr <= addr;
                vif.awprot <= 3'b000;
                @(posedge vif.clk iff vif.awready);
                vif.awvalid <= 1'b0;
            end
            // Data channel
            begin
                vif.wvalid <= 1'b1;
                vif.wdata <= data;
                vif.wstrb <= strb;
                @(posedge vif.clk iff vif.wready);
                vif.wvalid <= 1'b0;
            end
        join
        
        // Response channel
        vif.bready <= 1'b1;
        @(posedge vif.clk iff vif.bvalid);
        vif.bready <= 1'b0;
    endtask
    
    // Helper task: AXI Read
    virtual task axi_read(logic [31:0] addr, output logic [31:0] data);
        `uvm_info("TEST", $sformatf("AXI READ: addr=0x%08X", addr), UVM_HIGH)
        
        // Address channel
        vif.arvalid <= 1'b1;
        vif.araddr <= addr;
        vif.arprot <= 3'b000;
        @(posedge vif.clk iff vif.arready);
        vif.arvalid <= 1'b0;
        
        // Data channel
        vif.rready <= 1'b1;
        @(posedge vif.clk iff vif.rvalid);
        data = vif.rdata;
        vif.rready <= 1'b0;
        
        `uvm_info("TEST", $sformatf("AXI READ result: data=0x%08X", data), UVM_HIGH)
    endtask
    
endclass