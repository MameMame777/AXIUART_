`timescale 1ns / 1ps

// UART Register Pattern Test Sequence
// Tests register access through UART-AXI Bridge with all5, allA, allF patterns
// Purpose: Verify complete UART→Bridge→AXI→Register data flow

import uvm_pkg::*;
`include "uvm_macros.svh"

class uart_register_pattern_sequence extends uvm_sequence;
    `uvm_object_utils(uart_register_pattern_sequence)
    
    // Test patterns for comprehensive bit validation
    typedef struct packed {
        logic [31:0] pattern;
        string       name;
    } test_pattern_t;
    
    test_pattern_t test_patterns[] = {
        '{32'h55555555, "all5_pattern"},   // Critical bit validation
        '{32'hAAAAAAAA, "allA_pattern"},   // Inverted bit validation
        '{32'hFFFFFFFF, "allF_pattern"},   // All ones
        '{32'h12345678, "sequential"},     // Sequential pattern
        '{32'hDEADBEEF, "deadbeef"},      // Classic test pattern
        '{32'hCAFEBABE, "cafebabe"},      // Coffee pattern
        '{32'hFEEDFACE, "feedface"}       // Feed face pattern
    };
    
    // Register addresses for testing
    typedef struct packed {
        logic [31:0] addr;
        string       name;
    } register_info_t;
    
    register_info_t test_registers[] = {
        '{32'h0000_1000, "CONTROL"},      // Control register
        '{32'h0000_1008, "CONFIG"},       // Configuration register  
        '{32'h0000_100C, "DEBUG"},        // Debug register
        '{32'h0000_1020, "TEST_0"},       // Test register 0
        '{32'h0000_1024, "TEST_1"},       // Test register 1
        '{32'h0000_1028, "TEST_2"},       // Test register 2
        '{32'h0000_102C, "TEST_3"}        // Test register 3
    };
    
    function new(string name = "uart_register_pattern_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        `uvm_info("UART_REG_SEQ", "=== UART REGISTER PATTERN TEST START ===", UVM_LOW)
        
        // Test each register with each pattern
        foreach (test_registers[reg_idx]) begin
            foreach (test_patterns[pat_idx]) begin
                test_register_pattern(
                    test_registers[reg_idx].addr,
                    test_registers[reg_idx].name,
                    test_patterns[pat_idx].pattern,
                    test_patterns[pat_idx].name
                );
            end
        end
        
        `uvm_info("UART_REG_SEQ", "=== UART REGISTER PATTERN TEST COMPLETE ===", UVM_LOW)
    endtask
    
    // Test single register with single pattern via UART-AXI Bridge
    virtual task test_register_pattern(
        logic [31:0] addr,
        string reg_name,
        logic [31:0] pattern,
        string pattern_name
    );
        logic [7:0] uart_frame[8];
        logic [31:0] read_data;
        
        `uvm_info("UART_REG_SEQ", 
                 $sformatf("Testing %s register (0x%08X) with %s pattern (0x%08X)", 
                          reg_name, addr, pattern_name, pattern), UVM_MEDIUM)
        
        // Build UART frame for AXI write command
        // Frame format: [SYNC] [CMD] [LEN] [ADDR[3:0]] [DATA[3:0]] [CRC]
        uart_frame[0] = 8'h5A;                    // SYNC byte
        uart_frame[1] = 8'h57;                    // WRITE command (0x57)
        uart_frame[2] = 8'h08;                    // Length = 8 bytes (4 addr + 4 data)
        uart_frame[3] = addr[31:24];              // Address byte 3
        uart_frame[4] = addr[23:16];              // Address byte 2
        uart_frame[5] = addr[15:8];               // Address byte 1
        uart_frame[6] = addr[7:0];                // Address byte 0
        uart_frame[7] = pattern[31:24];           // Data byte 3
        uart_frame[8] = pattern[23:16];           // Data byte 2
        uart_frame[9] = pattern[15:8];            // Data byte 1
        uart_frame[10] = pattern[7:0];            // Data byte 0
        // Note: CRC calculation would be added here in full implementation
        
        // Send UART frame (simplified - actual implementation would use proper UART driver)
        send_uart_frame(uart_frame, 11);
        
        // Wait for AXI transaction completion
        repeat(100) @(posedge p_sequencer.get_sequencer().vif.clk);
        
        // Build UART frame for AXI read command to verify
        uart_frame[0] = 8'h5A;                    // SYNC byte
        uart_frame[1] = 8'h52;                    // READ command (0x52)
        uart_frame[2] = 8'h04;                    // Length = 4 bytes (address only)
        uart_frame[3] = addr[31:24];              // Address byte 3
        uart_frame[4] = addr[23:16];              // Address byte 2
        uart_frame[5] = addr[15:8];               // Address byte 1
        uart_frame[6] = addr[7:0];                // Address byte 0
        
        // Send read frame
        send_uart_frame(uart_frame, 7);
        
        // Wait for read response and verify
        read_data = receive_uart_response();
        
        if (read_data === pattern) begin
            `uvm_info("UART_REG_SEQ", 
                     $sformatf("%s %s test: PASS (0x%08X)", reg_name, pattern_name, read_data), UVM_LOW)
        end else begin
            `uvm_error("UART_REG_SEQ", 
                      $sformatf("%s %s test: FAIL - expected 0x%08X, got 0x%08X", 
                               reg_name, pattern_name, pattern, read_data))
        end
    endtask
    
    // Helper task: Send UART frame
    virtual task send_uart_frame(logic [7:0] frame[], int length);
        // Implementation would depend on the specific UART agent
        // This is a placeholder for the actual UART transmission
        `uvm_info("UART_REG_SEQ", $sformatf("Sending UART frame, length=%0d", length), UVM_HIGH)
        
        // Simulate UART transmission timing
        repeat(length * 100) @(posedge p_sequencer.get_sequencer().vif.clk);
    endtask
    
    // Helper task: Receive UART response
    virtual task receive_uart_response();
        logic [31:0] response_data;
        // Implementation would depend on the specific UART agent
        // This is a placeholder for the actual UART reception
        
        // Simulate UART reception timing
        repeat(500) @(posedge p_sequencer.get_sequencer().vif.clk);
        
        // For now, return dummy data - real implementation would parse UART response
        response_data = 32'h12345678;
        
        `uvm_info("UART_REG_SEQ", $sformatf("Received UART response: 0x%08X", response_data), UVM_HIGH)
        return response_data;
    endtask
    
endclass