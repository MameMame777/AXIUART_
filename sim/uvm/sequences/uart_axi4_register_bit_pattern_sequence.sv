`timescale 1ns / 1ps

// =============================================================================
// uart_axi4_register_bit_pattern_sequence.sv
// Comprehensive Bit Pattern Register Test Sequence
// 
// Purpose: Test AXI4-Lite register write/read with all5, allA, allF patterns
//          to verify actual bit-level read/write functionality
// =============================================================================

class uart_axi4_register_bit_pattern_sequence extends uvm_sequence#(uart_frame_transaction);

    `uvm_object_utils(uart_axi4_register_bit_pattern_sequence)
    
    localparam bit [31:0] REG_BASE_ADDR = 32'h0000_1000;
    localparam bit [31:0] REG_CONTROL   = REG_BASE_ADDR + 32'h000;
    localparam bit [31:0] REG_CONFIG    = REG_BASE_ADDR + 32'h008;
    localparam bit [31:0] REG_DEBUG     = REG_BASE_ADDR + 32'h00C;
    localparam bit [31:0] REG_TEST_0    = REG_BASE_ADDR + 32'h020;
    localparam bit [31:0] REG_TEST_1    = REG_BASE_ADDR + 32'h024;
    localparam bit [31:0] REG_TEST_2    = REG_BASE_ADDR + 32'h028;

    function new(string name = "uart_axi4_register_bit_pattern_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction req;
        
        `uvm_info(get_type_name(), "=== UART-AXI BRIDGE BIT PATTERN REGISTER TEST START ===", UVM_LOW)
        
        // Test Pattern 1: all5 (0x55555555) - Alternating bits 01010101
        test_register_pattern("all5", REG_TEST_0, 32'h55555555);
        
        // Test Pattern 2: allA (0xAAAAAAAA) - Alternating bits 10101010  
        test_register_pattern("allA", REG_TEST_1, 32'hAAAAAAAA);
        
        // Test Pattern 3: allF (0xFFFFFFFF) - All ones
        test_register_pattern("allF", REG_TEST_2, 32'hFFFFFFFF);
        
        // Test Pattern 4: Custom pattern (0xDEADBEEF)
        test_register_pattern("DEADBEEF", REG_CONFIG, 32'hDEADBEEF);
        
        // Test Pattern 5: Sequential pattern (0x12345678)
        test_register_pattern("Sequential", REG_DEBUG, 32'h12345678);
        
        `uvm_info(get_type_name(), "=== UART-AXI BRIDGE BIT PATTERN REGISTER TEST COMPLETE ===", UVM_LOW)
    endtask
    
    // Helper task to test a specific register with a specific pattern
    virtual task test_register_pattern(string pattern_name, bit [31:0] reg_addr, bit [31:0] test_pattern);
        uart_frame_transaction req;
        
        `uvm_info(get_type_name(), $sformatf("=== Testing %s Pattern (0x%08X) at Register 0x%08X ===", 
                  pattern_name, test_pattern, reg_addr), UVM_LOW)
        
        // Step 1: Write the test pattern via UART
        `uvm_info(get_type_name(), $sformatf("Writing %s pattern 0x%08X to register 0x%08X", 
                  pattern_name, test_pattern, reg_addr), UVM_MEDIUM)
        
        req = uart_frame_transaction::type_id::create($sformatf("%s_write_req", pattern_name));
        start_item(req);
        req.is_write = 1'b1;
        req.auto_increment = 1'b0;
        req.addr = reg_addr;
        req.length = 0;            // Single beat
        req.size = 2'b10;          // 32-bit transaction
        req.data = new[4];
        
        // Pack data in little-endian format
        req.data[0] = test_pattern[7:0];    // LSB
        req.data[1] = test_pattern[15:8];
        req.data[2] = test_pattern[23:16];
        req.data[3] = test_pattern[31:24];  // MSB
        
        req.build_cmd();           // Build command field
        req.calculate_crc();       // Calculate CRC
        finish_item(req);
        
        #200000ns;  // Wait for write to complete through entire UART-AXI bridge
        
        // Step 2: Read back the pattern via UART  
        `uvm_info(get_type_name(), $sformatf("Reading back from register 0x%08X to verify %s pattern", 
                  reg_addr, pattern_name), UVM_MEDIUM)
        
        req = uart_frame_transaction::type_id::create($sformatf("%s_read_req", pattern_name));
        start_item(req);
        req.is_write = 1'b0;
        req.auto_increment = 1'b0;
        req.addr = reg_addr;
        req.length = 0;            // Single beat
        req.size = 2'b10;          // 32-bit transaction
        req.data = new[1];         // Minimal data array for read
        req.build_cmd();           // Build command field
        req.calculate_crc();       // Calculate CRC
        finish_item(req);
        
        #200000ns;  // Wait for read to complete through entire UART-AXI bridge
        
        `uvm_info(get_type_name(), $sformatf("%s pattern test completed for register 0x%08X", 
                  pattern_name, reg_addr), UVM_MEDIUM)
        
    endtask

endclass