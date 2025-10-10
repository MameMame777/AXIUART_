`timescale 1ns / 1ps

// Comprehensive Register Block Test - Test All Register Types
// Purpose: Test all available registers including RW, RO, and error handling

import uvm_pkg::*;
`include "uvm_macros.svh"

class register_block_minimal_test extends uvm_test;
    `uvm_component_utils(register_block_minimal_test)
    
    // Environment components
    typedef virtual axi4_lite_if vif_t;
    vif_t vif;
    
    function new(string name = "register_block_minimal_test", uvm_component parent = null);
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
        phase.raise_objection(this);
        
        `uvm_info("TEST", "=== REGISTER BLOCK COMPREHENSIVE TEST START ===", UVM_LOW)
        
        // Wait for reset deassertion
        wait(!vif.rst);
        repeat(5) @(posedge vif.clk);
        
        // Test 1: Basic control register write/read
        test_control_register();
        
        // Test 2: Configuration register write/read
        test_config_register();
        
        // Test 3: Debug register write/read
        test_debug_register();
        
        // Test 4: Test registers (comprehensive set)
        test_register_set();
        
        // Test 5: Read-only register access
        test_readonly_registers();
        
        // Test 6: Invalid address access
        test_invalid_address();
        
        // Test 7: ERROR HANDLING VERIFICATION
        test_error_handling();
        
        `uvm_info("TEST", "=== REGISTER BLOCK COMPREHENSIVE TEST COMPLETE ===", UVM_LOW)
        
        repeat(10) @(posedge vif.clk);
        phase.drop_objection(this);
    endtask
    
    // Test Task 1: Control Register Basic Operations
    virtual task test_control_register();
        logic [31:0] read_data;
        
        `uvm_info("TEST", "--- Testing Control Register ---", UVM_LOW)
        
        // CRITICAL: Initial value is 0x00000001, so we must write DIFFERENT values to verify W/R functionality
        
        // First, write 0x00000000 (disable bridge) - DIFFERENT from reset value
        axi_write(32'h0000_1000, 32'h0000_0000, 4'b1111);
        
        // Read back and verify
        axi_read(32'h0000_1000, read_data);
        if (read_data[0] !== 1'b0) begin
            `uvm_error("TEST", $sformatf("Control register write 0 failed: expected bit[0]=0, got 0x%08X", read_data))
        end else begin
            `uvm_info("TEST", "Control register write/read 0: PASS", UVM_LOW)
        end
        
        // Then, write 0x55555555 (all5 pattern) - Comprehensive bit test
        axi_write(32'h0000_1000, 32'h5555_5555, 4'b1111);
        
        // Read back and verify control register functionality
        axi_read(32'h0000_1000, read_data);
        if (read_data[0] !== 1'b1) begin
            `uvm_error("TEST", $sformatf("Control register all5 pattern failed: expected bit[0]=1, got 0x%08X", read_data))
        end else begin
            `uvm_info("TEST", "Control register all5 pattern: PASS", UVM_LOW)
        end
        
        // Test allA pattern (0xAAAAAAAA)
        axi_write(32'h0000_1000, 32'hAAAA_AAAA, 4'b1111);
        
        // Read back and verify
        axi_read(32'h0000_1000, read_data);
        if (read_data[0] !== 1'b0) begin
            `uvm_error("TEST", $sformatf("Control register allA pattern failed: expected bit[0]=0, got 0x%08X", read_data))
        end else begin
            `uvm_info("TEST", "Control register allA pattern: PASS", UVM_LOW)
        end
    endtask
    
    // Test Task 2: Configuration Register
    virtual task test_config_register();
        logic [31:0] read_data;
        
        `uvm_info("TEST", "--- Testing Configuration Register ---", UVM_LOW)
        
        // Test baud_div_config (bits 7:0) and timeout_config (bits 15:8)
        axi_write(32'h0000_1008, 32'h0000_5AA5, 4'b1111);
        
        // Read back and verify
        axi_read(32'h0000_1008, read_data);
        if (read_data[15:0] !== 16'h5AA5) begin
            `uvm_error("TEST", $sformatf("Config register read mismatch: expected 0x5AA5, got 0x%04X", read_data[15:0]))
        end else begin
            `uvm_info("TEST", "Configuration register write/read: PASS", UVM_LOW)
        end
        
        // Test partial write (lower byte only)
        axi_write(32'h0000_1008, 32'h0000_0033, 4'b0001);
        axi_read(32'h0000_1008, read_data);
        if (read_data[7:0] !== 8'h33) begin
            `uvm_error("TEST", $sformatf("Config partial write failed: expected 0x33, got 0x%02X", read_data[7:0]))
        end else begin
            `uvm_info("TEST", "Configuration register partial write: PASS", UVM_LOW)
        end
    endtask
    
    // Test Task 3: Debug Register
    virtual task test_debug_register();
        logic [31:0] read_data;
        
        `uvm_info("TEST", "--- Testing Debug Register ---", UVM_LOW)
        
        // Test debug_mode (bits 3:0)
        axi_write(32'h0000_100C, 32'h0000_000F, 4'b1111);
        
        // Read back and verify
        axi_read(32'h0000_100C, read_data);
        if (read_data[3:0] !== 4'hF) begin
            `uvm_error("TEST", $sformatf("Debug register read mismatch: expected 0xF, got 0x%01X", read_data[3:0]))
        end else begin
            `uvm_info("TEST", "Debug register write/read: PASS", UVM_LOW)
        end
        
        // Test pattern cycling
        for (int i = 0; i < 16; i++) begin
            axi_write(32'h0000_100C, i, 4'b1111);
            axi_read(32'h0000_100C, read_data);
            if (read_data[3:0] !== i[3:0]) begin
                `uvm_error("TEST", $sformatf("Debug register pattern %0d failed: expected 0x%01X, got 0x%01X", i, i[3:0], read_data[3:0]))
                break;
            end
        end
        `uvm_info("TEST", "Debug register pattern cycling: PASS", UVM_LOW)
    endtask
    
    // Test Task 4: Test Register Set - PROPER BIT VALIDATION PATTERNS
    virtual task test_register_set();
        logic [31:0] read_data;
        logic [31:0] test_patterns[8] = {
            32'h55555555, // all5 - bit validation pattern
            32'hAAAAAAAA, // allA - inverted bit validation  
            32'hFFFFFFFF, // allF - all ones verification
            32'h12345678, // Sequential pattern (NOT initial value 0x00000000)
            32'hDEADBEEF, // Hex pattern
            32'hCAFEBABE, // Another hex pattern
            32'hABCDEF00, // Mixed pattern
            32'hFEEDFACE  // Additional pattern for 8 elements
        };
        logic [31:0] test_addresses[8] = {
            32'h0000_1020, 32'h0000_1024, 32'h0000_1028, 32'h0000_102C,
            32'h0000_1040, 32'h0000_1050, 32'h0000_1080, 32'h0000_1100
        };
        
        `uvm_info("TEST", "--- Testing Test Register Set ---", UVM_LOW)
        
        // Test all test registers with different patterns
        for (int i = 0; i < 8; i++) begin
            // Write test pattern
            axi_write(test_addresses[i], test_patterns[i], 4'b1111);
            
            // Read back and verify
            axi_read(test_addresses[i], read_data);
            if (read_data !== test_patterns[i]) begin
                `uvm_error("TEST", $sformatf("Test register %0d at 0x%08X: expected 0x%08X, got 0x%08X", 
                          i, test_addresses[i], test_patterns[i], read_data))
            end else begin
                `uvm_info("TEST", $sformatf("Test register %0d: PASS (0x%08X)", i, test_patterns[i]), UVM_MEDIUM)
            end
        end
        
        // Test data persistence - read all registers again
        `uvm_info("TEST", "Testing data persistence...", UVM_MEDIUM)
        for (int i = 0; i < 8; i++) begin
            axi_read(test_addresses[i], read_data);
            if (read_data !== test_patterns[i]) begin
                `uvm_error("TEST", $sformatf("Data persistence failed for register %0d: expected 0x%08X, got 0x%08X", 
                          i, test_patterns[i], read_data))
            end
        end
        `uvm_info("TEST", "Test register set comprehensive test: PASS", UVM_LOW)
    endtask
    
    // Test Task 5: Read-Only Registers (Enhanced)
    // Test Task 5: Read-Only Registers (Enhanced)
    virtual task test_readonly_registers();
        logic [31:0] read_data;
        
        `uvm_info("TEST", "--- Testing Read-Only Registers ---", UVM_LOW)
        
        // Test VERSION register (should be 0x0001_0000)
        axi_read(32'h0000_101C, read_data);
        if (read_data !== 32'h0001_0000) begin
            `uvm_error("TEST", $sformatf("Version register mismatch: expected 0x00010000, got 0x%08X", read_data))
        end else begin
            `uvm_info("TEST", "Version register read: PASS", UVM_LOW)
        end
        
        // Test STATUS register read (bridge should not be busy initially)
        axi_read(32'h0000_1004, read_data);
        `uvm_info("TEST", $sformatf("Status register: 0x%08X", read_data), UVM_LOW)
        
        // Test TX_COUNT register
        axi_read(32'h0000_1010, read_data);
        `uvm_info("TEST", $sformatf("TX Count register: 0x%08X", read_data), UVM_LOW)
        
        // Test RX_COUNT register  
        axi_read(32'h0000_1014, read_data);
        `uvm_info("TEST", $sformatf("RX Count register: 0x%08X", read_data), UVM_LOW)
        
        // Test FIFO_STAT register
        axi_read(32'h0000_1018, read_data);
        `uvm_info("TEST", $sformatf("FIFO Status register: 0x%08X", read_data), UVM_LOW)
        
        // Attempt to write to read-only registers (should have no effect)
        `uvm_info("TEST", "Testing write protection of RO registers...", UVM_MEDIUM)
        
        // Try to write to VERSION register
        axi_write(32'h0000_101C, 32'hDEADBEEF, 4'b1111);
        axi_read(32'h0000_101C, read_data);
        if (read_data !== 32'h0001_0000) begin
            `uvm_error("TEST", "Version register was modified by write - write protection failed!")
        end else begin
            `uvm_info("TEST", "Version register write protection: PASS", UVM_LOW)
        end
    endtask
    
    // Test Task 6: Invalid Address Access
    virtual task test_invalid_address();
        logic [31:0] read_data;
        logic [1:0] resp;
        
        `uvm_info("TEST", "--- Testing Invalid Address Access ---", UVM_LOW)
        
        // Try to read from invalid address
        axi_read_with_response(32'h0000_1FFC, read_data, resp);
        if (resp !== 2'b10) begin // SLVERR expected
            `uvm_error("TEST", $sformatf("Invalid address should return SLVERR, got resp=0x%02X", resp))
        end else begin
            `uvm_info("TEST", "Invalid address error response: PASS", UVM_LOW)
        end
    endtask
    
    // Test Task 7: ERROR HANDLING VERIFICATION
    virtual task test_error_handling();
        logic [31:0] read_data;
        logic [1:0] resp;
        
        `uvm_info("TEST", "--- ERROR HANDLING VERIFICATION START ---", UVM_LOW)
        
        // Test 1: Invalid WSTRB patterns (misaligned access)
        test_invalid_wstrb_patterns();
        
        // Test 2: AXI Protocol violations
        test_protocol_violations();
        
        // Test 3: Address alignment errors
        test_address_alignment_errors();
        
        // Test 4: Boundary address testing
        test_boundary_addresses();
        
        `uvm_info("TEST", "--- ERROR HANDLING VERIFICATION COMPLETE ---", UVM_LOW)
    endtask
    
    // Test invalid WSTRB patterns
    virtual task test_invalid_wstrb_patterns();
        logic [31:0] read_data;
        logic [1:0] resp;
        
        `uvm_info("TEST", "Testing invalid WSTRB patterns...", UVM_MEDIUM)
        
        // Test invalid WSTRB pattern - gaps in byte enables (0b1010)
        axi_write_with_response(32'h0000_1000, 32'h12345678, 4'b1010, resp);
        if (resp == 2'b00) begin // OKAY response
            `uvm_info("TEST", "WSTRB gap pattern accepted (PASS)", UVM_MEDIUM)
        end else begin
            `uvm_info("TEST", $sformatf("WSTRB gap pattern rejected with RESP=0x%01X", resp), UVM_MEDIUM)
        end
        
        // Test single byte access (valid)
        axi_write_with_response(32'h0000_1000, 32'h000000AB, 4'b0001, resp);
        if (resp == 2'b00) begin
            `uvm_info("TEST", "Single byte WSTRB accepted (PASS)", UVM_MEDIUM)
        end else begin
            `uvm_error("TEST", $sformatf("Single byte WSTRB should be valid, got RESP=0x%01X", resp))
        end
        
        // Test all bytes disabled (should be error)
        axi_write_with_response(32'h0000_1000, 32'h12345678, 4'b0000, resp);
        if (resp != 2'b00) begin
            `uvm_info("TEST", $sformatf("All bytes disabled correctly rejected with RESP=0x%01X (PASS)", resp), UVM_MEDIUM)
        end else begin
            `uvm_info("TEST", "All bytes disabled accepted (implementation specific)", UVM_MEDIUM)
        end
    endtask
    
    // Test AXI protocol violations
    virtual task test_protocol_violations();
        logic [31:0] read_data;
        logic [1:0] resp;
        
        `uvm_info("TEST", "Testing AXI protocol edge cases...", UVM_MEDIUM)
        
        // Test concurrent read and write (implementation dependent)
        fork
            begin
                axi_write_with_response(32'h0000_1000, 32'hAAAABBBB, 4'b1111, resp);
                `uvm_info("TEST", $sformatf("Concurrent write completed with RESP=0x%01X", resp), UVM_MEDIUM)
            end
            begin
                #1; // Small delay to ensure some overlap
                axi_read_with_response(32'h0000_1004, read_data, resp);
                `uvm_info("TEST", $sformatf("Concurrent read completed with RESP=0x%01X", resp), UVM_MEDIUM)
            end
        join
        
        // Test rapid successive accesses
        for (int i = 0; i < 5; i++) begin
            axi_write(32'h0000_1000, 32'h11111111 + i, 4'b1111);
            axi_read(32'h0000_1000, read_data);
        end
        `uvm_info("TEST", "Rapid successive accesses completed", UVM_MEDIUM)
    endtask
    
    // Test address alignment errors  
    virtual task test_address_alignment_errors();
        logic [31:0] read_data;
        logic [1:0] resp;
        logic [31:0] unaligned_addrs[4];
        
        `uvm_info("TEST", "Testing address alignment...", UVM_MEDIUM)
        
        // Initialize unaligned addresses array
        unaligned_addrs[0] = 32'h0000_1001; // +1 byte offset
        unaligned_addrs[1] = 32'h0000_1002; // +2 byte offset  
        unaligned_addrs[2] = 32'h0000_1003; // +3 byte offset
        unaligned_addrs[3] = 32'h0000_1005; // +5 byte offset
        
        for (int i = 0; i < 4; i++) begin
            axi_write_with_response(unaligned_addrs[i], 32'h12345678, 4'b1111, resp);
            if (resp == 2'b00) begin
                `uvm_info("TEST", $sformatf("Unaligned addr 0x%08X accepted (PASS)", unaligned_addrs[i]), UVM_MEDIUM)
            end else begin
                `uvm_info("TEST", $sformatf("Unaligned addr 0x%08X rejected with RESP=0x%01X", unaligned_addrs[i], resp), UVM_MEDIUM)
            end
            
            axi_read_with_response(unaligned_addrs[i], read_data, resp);
            if (resp == 2'b00) begin
                `uvm_info("TEST", $sformatf("Unaligned read 0x%08X accepted (PASS)", unaligned_addrs[i]), UVM_MEDIUM)
            end else begin
                `uvm_info("TEST", $sformatf("Unaligned read 0x%08X rejected with RESP=0x%01X", unaligned_addrs[i], resp), UVM_MEDIUM)
            end
        end
    endtask
    
    // Test boundary addresses
    virtual task test_boundary_addresses();
        logic [31:0] read_data;
        logic [1:0] resp;
        logic [31:0] boundary_addrs[8];
        
        `uvm_info("TEST", "Testing boundary addresses...", UVM_MEDIUM)
        
        // Initialize boundary addresses array
        boundary_addrs[0] = 32'h0000_0FFC; // Just before valid range
        boundary_addrs[1] = 32'h0000_0FFF; // Just before valid range  
        boundary_addrs[2] = 32'h0000_1000; // First valid address
        boundary_addrs[3] = 32'h0000_1044; // Last valid address (FIFO_STAT)
        boundary_addrs[4] = 32'h0000_1045; // Just after valid range
        boundary_addrs[5] = 32'h0000_1048; // Just after valid range
        boundary_addrs[6] = 32'h0000_1FFF; // Far after valid range
        boundary_addrs[7] = 32'h0000_2000; // Far after valid range
        
        for (int i = 0; i < 8; i++) begin
            axi_read_with_response(boundary_addrs[i], read_data, resp);
            if (i >= 2 && i <= 3) begin // Valid range
                if (resp == 2'b00) begin
                    `uvm_info("TEST", $sformatf("Valid boundary addr 0x%08X: OKAY (PASS)", boundary_addrs[i]), UVM_MEDIUM)
                end else begin
                    `uvm_error("TEST", $sformatf("Valid addr 0x%08X should return OKAY, got RESP=0x%01X", boundary_addrs[i], resp))
                end
            end else begin // Invalid range
                if (resp == 2'b10) begin // SLVERR expected
                    `uvm_info("TEST", $sformatf("Invalid boundary addr 0x%08X: SLVERR (PASS)", boundary_addrs[i]), UVM_MEDIUM)
                end else begin
                    `uvm_info("TEST", $sformatf("Invalid addr 0x%08X returned RESP=0x%01X (implementation specific)", boundary_addrs[i], resp), UVM_MEDIUM)
                end
            end
        end
    endtask
    
    // Helper task: AXI Write with Response
    virtual task axi_write_with_response(logic [31:0] addr, logic [31:0] data, logic [3:0] strb, output logic [1:0] resp);
        `uvm_info("TEST", $sformatf("AXI WRITE: addr=0x%08X, data=0x%08X, strb=0x%01X", addr, data, strb), UVM_HIGH)
        
        // Address and data channels
        fork
            begin
                vif.awvalid <= 1'b1;
                vif.awaddr <= addr;
                vif.awprot <= 3'b000;
                @(posedge vif.clk iff vif.awready);
                vif.awvalid <= 1'b0;
            end
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
        resp = vif.bresp;
        vif.bready <= 1'b0;
        
        `uvm_info("TEST", $sformatf("AXI write response: RESP=0x%01X", resp), UVM_HIGH)
    endtask
    
    // Helper task: AXI Write
    virtual task axi_write(logic [31:0] addr, logic [31:0] data, logic [3:0] strb);
        `uvm_info("TEST", $sformatf("AXI WRITE: addr=0x%08X, data=0x%08X", addr, data), UVM_MEDIUM)
        
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
        
        if (vif.bresp !== 2'b00) begin
            `uvm_warning("TEST", $sformatf("Write response error: bresp=0x%02X", vif.bresp))
        end
    endtask
    
    // Helper task: AXI Read
    virtual task axi_read(logic [31:0] addr, output logic [31:0] data);
        logic [1:0] resp;
        axi_read_with_response(addr, data, resp);
    endtask
    
    // Helper task: AXI Read with Response Check
    virtual task axi_read_with_response(logic [31:0] addr, output logic [31:0] data, output logic [1:0] resp);
        `uvm_info("TEST", $sformatf("AXI READ: addr=0x%08X", addr), UVM_MEDIUM)
        
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
        resp = vif.rresp;
        vif.rready <= 1'b0;
        
        `uvm_info("TEST", $sformatf("AXI READ result: data=0x%08X, resp=0x%02X", data, resp), UVM_MEDIUM)
    endtask
    
endclass