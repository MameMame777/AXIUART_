`timescale 1ns / 1ps

// =============================================================================
// uart_axi4_register_pattern_sequence.sv
// UART-AXI4-Lite Register Pattern Test Sequence
// 
// Purpose: Test complete UART->AXI4->Register data flow with all5, allA, allF patterns
//          Verify that register writes actually update values (not initial values)
// =============================================================================

class uart_axi4_register_pattern_sequence extends uvm_sequence#(uart_frame_transaction);

    `uvm_object_utils(uart_axi4_register_pattern_sequence)
    
    localparam bit [31:0] REG_BASE_ADDR = 32'h0000_1000;
    localparam bit [31:0] REG_CONTROL   = REG_BASE_ADDR + 32'h000;  // 0x1000
    localparam bit [31:0] REG_CONFIG    = REG_BASE_ADDR + 32'h008;  // 0x1008  
    localparam bit [31:0] REG_DEBUG     = REG_BASE_ADDR + 32'h00C;  // 0x100C
    localparam bit [31:0] REG_TEST_0    = REG_BASE_ADDR + 32'h020;  // 0x1020
    localparam bit [31:0] REG_TEST_1    = REG_BASE_ADDR + 32'h024;  // 0x1024
    localparam bit [31:0] REG_TEST_2    = REG_BASE_ADDR + 32'h028;  // 0x1028

    function new(string name = "uart_axi4_register_pattern_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction req;
        
        `uvm_info(get_type_name(), "=== UART-AXI4-REGISTER PATTERN TEST START ===", UVM_LOW)
        
        // Test 1: Write all5 pattern (0x55555555) to TEST_0 register via UART
        `uvm_info(get_type_name(), "Test 1: Write all5 (0x55555555) to TEST_0 via UART", UVM_LOW)
        write_register_via_uart(REG_TEST_0, 32'h55555555);
        #200000ns;  // Wait for complete processing
        
        // Test 2: Read back TEST_0 register via UART  
        `uvm_info(get_type_name(), "Test 2: Read TEST_0 register via UART", UVM_LOW)
        read_register_via_uart(REG_TEST_0);
        #200000ns;
        
        // Test 3: Write allA pattern (0xAAAAAAAA) to TEST_1 register via UART
        `uvm_info(get_type_name(), "Test 3: Write allA (0xAAAAAAAA) to TEST_1 via UART", UVM_LOW)
        write_register_via_uart(REG_TEST_1, 32'hAAAAAAAA);
        #200000ns;
        
        // Test 4: Read back TEST_1 register via UART
        `uvm_info(get_type_name(), "Test 4: Read TEST_1 register via UART", UVM_LOW)
        read_register_via_uart(REG_TEST_1);
        #200000ns;
        
        // Test 5: Write allF pattern (0xFFFFFFFF) to TEST_2 register via UART
        `uvm_info(get_type_name(), "Test 5: Write allF (0xFFFFFFFF) to TEST_2 via UART", UVM_LOW)
        write_register_via_uart(REG_TEST_2, 32'hFFFFFFFF);
        #200000ns;
        
        // Test 6: Read back TEST_2 register via UART
        `uvm_info(get_type_name(), "Test 6: Read TEST_2 register via UART", UVM_LOW)
        read_register_via_uart(REG_TEST_2);
        #200000ns;
        
        // Test 7: Write custom pattern (0x12345678) to CONFIG register
        `uvm_info(get_type_name(), "Test 7: Write custom (0x12345678) to CONFIG via UART", UVM_LOW)
        write_register_via_uart(REG_CONFIG, 32'h12345678);
        #200000ns;
        
        // Test 8: Read back CONFIG register via UART
        `uvm_info(get_type_name(), "Test 8: Read CONFIG register via UART", UVM_LOW)
        read_register_via_uart(REG_CONFIG);
        #200000ns;
        
        // Test 9: Write DEADBEEF pattern to DEBUG register  
        `uvm_info(get_type_name(), "Test 9: Write DEADBEEF (0xDEADBEEF) to DEBUG via UART", UVM_LOW)
        write_register_via_uart(REG_DEBUG, 32'hDEADBEEF);
        #200000ns;
        
        // Test 10: Read back DEBUG register via UART
        `uvm_info(get_type_name(), "Test 10: Read DEBUG register via UART", UVM_LOW)
        read_register_via_uart(REG_DEBUG);
        #200000ns;
        
        `uvm_info(get_type_name(), "=== UART-AXI4-REGISTER PATTERN TEST COMPLETE ===", UVM_LOW)
    endtask
    
    // Helper task: Write register via UART
    virtual task write_register_via_uart(bit [31:0] addr, bit [31:0] data);
        uart_frame_transaction req;
        
        `uvm_info(get_type_name(), $sformatf("UART WRITE: addr=0x%08X, data=0x%08X", addr, data), UVM_MEDIUM)
        
        req = uart_frame_transaction::type_id::create("write_req");
        start_item(req);
        req.is_write = 1'b1;           // Write operation
        req.auto_increment = 1'b0;     // No auto-increment
        req.addr = addr;               // Target address
        req.length = 0;                // Single beat transfer
        req.size = 2'b10;              // 32-bit transaction
        req.data = new[4];             
        
        // Pack data in little-endian format
        req.data[0] = data[7:0];       // LSB
        req.data[1] = data[15:8];
        req.data[2] = data[23:16];  
        req.data[3] = data[31:24];     // MSB
        
        req.build_cmd();               // Build command field
        req.calculate_crc();           // Calculate CRC
        finish_item(req);
    endtask
    
    // Helper task: Read register via UART
    virtual task read_register_via_uart(bit [31:0] addr);
        uart_frame_transaction req;
        
        `uvm_info(get_type_name(), $sformatf("UART READ: addr=0x%08X", addr), UVM_MEDIUM)
        
        req = uart_frame_transaction::type_id::create("read_req");
        start_item(req);
        req.is_write = 1'b0;           // Read operation
        req.auto_increment = 1'b0;     // No auto-increment
        req.addr = addr;               // Target address
        req.length = 0;                // Single beat transfer
        req.size = 2'b10;              // 32-bit transaction
        req.data = new[1];             // Minimal data array for read
        
        req.build_cmd();               // Build command field
        req.calculate_crc();           // Calculate CRC
        finish_item(req);
    endtask

endclass