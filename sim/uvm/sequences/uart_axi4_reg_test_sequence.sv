`timescale 1ns / 1ps

// =============================================================================
// uart_axi4_reg_test_sequence.sv
// REG_TEST_0-3 Register Verification Sequence
// 
// Purpose: Test REG_TEST_0, REG_TEST_1, REG_TEST_2, REG_TEST_3 registers
// Address Range: 0x1020-0x102C (REG_TEST_0 to REG_TEST_3)
// =============================================================================

class uart_axi4_reg_test_sequence extends uvm_sequence#(uart_frame_transaction);

    `uvm_object_utils(uart_axi4_reg_test_sequence)
    
    localparam bit [31:0] REG_BASE_ADDR = 32'h0000_1000;
    localparam bit [31:0] REG_TEST_0    = REG_BASE_ADDR + 32'h020;  // 0x1020
    localparam bit [31:0] REG_TEST_1    = REG_BASE_ADDR + 32'h024;  // 0x1024
    localparam bit [31:0] REG_TEST_2    = REG_BASE_ADDR + 32'h028;  // 0x1028
    localparam bit [31:0] REG_TEST_3    = REG_BASE_ADDR + 32'h02C;  // 0x102C

    function new(string name = "uart_axi4_reg_test_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction req;
        
        `uvm_info(get_type_name(), "Starting REG_TEST_0-3 Register Verification", UVM_LOW)
        
        // ========================================
        // Test REG_TEST_0 (0x1020)
        // ========================================
        
        // Read initial value of REG_TEST_0 (should be 0xDEADBEEF)
        `uvm_info(get_type_name(), "=== Test 1: Read REG_TEST_0 Initial Value ===", UVM_LOW)
        req = uart_frame_transaction::type_id::create("test0_read_initial");
        start_item(req);
        req.is_write = 1'b0;
        req.auto_increment = 1'b0;
        req.addr = REG_TEST_0;
        req.length = 0;            // Single beat
        req.size = 2'b10;          // 32-bit transaction
        req.data = new[1];         // Minimal data array for read
        req.build_cmd();           // Build command field manually
        req.calculate_crc();       // Calculate CRC manually
        finish_item(req);
        #100000ns;
        
        // Write test pattern to REG_TEST_0
        `uvm_info(get_type_name(), "=== Test 2: Write 0xAAAABBBB to REG_TEST_0 ===", UVM_LOW)
        req = uart_frame_transaction::type_id::create("test0_write");
        start_item(req);
        req.is_write = 1'b1;
        req.auto_increment = 1'b0;
        req.addr = REG_TEST_0;
        req.length = 0;            // Single beat
        req.size = 2'b10;          // 32-bit transaction
        req.data = new[4];
        req.data[0] = 8'hBB;       // 0xAAAABBBB (little endian)
        req.data[1] = 8'hBB;
        req.data[2] = 8'hAA;
        req.data[3] = 8'hAA;
        req.build_cmd();
        req.calculate_crc();
        finish_item(req);
        #100000ns;
        
        // Read back REG_TEST_0
        `uvm_info(get_type_name(), "=== Test 3: Read back REG_TEST_0 ===", UVM_LOW)
        req = uart_frame_transaction::type_id::create("test0_read_back");
        start_item(req);
        req.is_write = 1'b0;
        req.auto_increment = 1'b0;
        req.addr = REG_TEST_0;
        req.length = 0;
        req.size = 2'b10;
        req.data = new[1];
        req.build_cmd();
        req.calculate_crc();
        finish_item(req);
        #100000ns;
        
        // ========================================
        // Test REG_TEST_1 (0x1024)
        // ========================================
        
        // Read initial value of REG_TEST_1 (should be 0x12345678)
        `uvm_info(get_type_name(), "=== Test 4: Read REG_TEST_1 Initial Value ===", UVM_LOW)
        req = uart_frame_transaction::type_id::create("test1_read_initial");
        start_item(req);
        req.is_write = 1'b0;
        req.auto_increment = 1'b0;
        req.addr = REG_TEST_1;
        req.length = 0;
        req.size = 2'b10;
        req.data = new[1];
        req.build_cmd();
        req.calculate_crc();
        finish_item(req);
        #100000ns;
        
        // Write test pattern to REG_TEST_1
        `uvm_info(get_type_name(), "=== Test 5: Write 0x55556666 to REG_TEST_1 ===", UVM_LOW)
        req = uart_frame_transaction::type_id::create("test1_write");
        start_item(req);
        req.is_write = 1'b1;
        req.auto_increment = 1'b0;
        req.addr = REG_TEST_1;
        req.length = 0;
        req.size = 2'b10;
        req.data = new[4];
        req.data[0] = 8'h66;       // 0x55556666 (little endian)
        req.data[1] = 8'h66;
        req.data[2] = 8'h55;
        req.data[3] = 8'h55;
        req.build_cmd();
        req.calculate_crc();
        finish_item(req);
        #100000ns;
        
        // Read back REG_TEST_1
        `uvm_info(get_type_name(), "=== Test 6: Read back REG_TEST_1 ===", UVM_LOW)
        req = uart_frame_transaction::type_id::create("test1_read_back");
        start_item(req);
        req.is_write = 1'b0;
        req.auto_increment = 1'b0;
        req.addr = REG_TEST_1;
        req.length = 0;
        req.size = 2'b10;
        req.data = new[1];
        req.build_cmd();
        req.calculate_crc();
        finish_item(req);
        #100000ns;
        
        // ========================================
        // Test REG_TEST_2 (0x1028)
        // ========================================
        
        // Read initial value of REG_TEST_2 (should be 0xABCDEF00)
        `uvm_info(get_type_name(), "=== Test 7: Read REG_TEST_2 Initial Value ===", UVM_LOW)
        req = uart_frame_transaction::type_id::create("test2_read_initial");
        start_item(req);
        req.is_write = 1'b0;
        req.auto_increment = 1'b0;
        req.addr = REG_TEST_2;
        req.length = 0;
        req.size = 2'b10;
        req.data = new[1];
        req.build_cmd();
        req.calculate_crc();
        finish_item(req);
        #100000ns;
        
        // Write test pattern to REG_TEST_2
        `uvm_info(get_type_name(), "=== Test 8: Write 0x11223344 to REG_TEST_2 ===", UVM_LOW)
        req = uart_frame_transaction::type_id::create("test2_write");
        start_item(req);
        req.is_write = 1'b1;
        req.auto_increment = 1'b0;
        req.addr = REG_TEST_2;
        req.length = 0;
        req.size = 2'b10;
        req.data = new[4];
        req.data[0] = 8'h44;       // 0x11223344 (little endian)
        req.data[1] = 8'h33;
        req.data[2] = 8'h22;
        req.data[3] = 8'h11;
        req.build_cmd();
        req.calculate_crc();
        finish_item(req);
        #100000ns;
        
        // Read back REG_TEST_2
        `uvm_info(get_type_name(), "=== Test 9: Read back REG_TEST_2 ===", UVM_LOW)
        req = uart_frame_transaction::type_id::create("test2_read_back");
        start_item(req);
        req.is_write = 1'b0;
        req.auto_increment = 1'b0;
        req.addr = REG_TEST_2;
        req.length = 0;
        req.size = 2'b10;
        req.data = new[1];
        req.build_cmd();
        req.calculate_crc();
        finish_item(req);
        #100000ns;
        
        // ========================================
        // Test REG_TEST_3 (0x102C)
        // ========================================
        
        // Read initial value of REG_TEST_3 (should be 0x00000000)
        `uvm_info(get_type_name(), "=== Test 10: Read REG_TEST_3 Initial Value ===", UVM_LOW)
        req = uart_frame_transaction::type_id::create("test3_read_initial");
        start_item(req);
        req.is_write = 1'b0;
        req.auto_increment = 1'b0;
        req.addr = REG_TEST_3;
        req.length = 0;
        req.size = 2'b10;
        req.data = new[1];
        req.build_cmd();
        req.calculate_crc();
        finish_item(req);
        #100000ns;
        
        // Write test pattern to REG_TEST_3
        `uvm_info(get_type_name(), "=== Test 11: Write 0xFFFFFFFF to REG_TEST_3 ===", UVM_LOW)
        req = uart_frame_transaction::type_id::create("test3_write");
        start_item(req);
        req.is_write = 1'b1;
        req.auto_increment = 1'b0;
        req.addr = REG_TEST_3;
        req.length = 0;
        req.size = 2'b10;
        req.data = new[4];
        req.data[0] = 8'hFF;       // 0xFFFFFFFF (little endian)
        req.data[1] = 8'hFF;
        req.data[2] = 8'hFF;
        req.data[3] = 8'hFF;
        req.build_cmd();
        req.calculate_crc();
        finish_item(req);
        #100000ns;
        
        // Read back REG_TEST_3
        `uvm_info(get_type_name(), "=== Test 12: Read back REG_TEST_3 ===", UVM_LOW)
        req = uart_frame_transaction::type_id::create("test3_read_back");
        start_item(req);
        req.is_write = 1'b0;
        req.auto_increment = 1'b0;
        req.addr = REG_TEST_3;
        req.length = 0;
        req.size = 2'b10;
        req.data = new[1];
        req.build_cmd();
        req.calculate_crc();
        finish_item(req);
        #100000ns;
        
        // ========================================
        // Walking Bit Pattern Test on REG_TEST_3
        // ========================================
        
        `uvm_info(get_type_name(), "=== Test 13: Walking bit pattern on REG_TEST_3 ===", UVM_LOW)
        
        // Test walking 1s pattern
        for (int i = 0; i < 32; i++) begin
            logic [31:0] walking_pattern = 32'h1 << i;
            
            // Write walking pattern
            req = uart_frame_transaction::type_id::create($sformatf("test3_walk_%0d", i));
            start_item(req);
            req.is_write = 1'b1;
            req.auto_increment = 1'b0;
            req.addr = REG_TEST_3;
            req.length = 0;
            req.size = 2'b10;
            req.data = new[4];
            req.data[0] = walking_pattern[7:0];
            req.data[1] = walking_pattern[15:8];
            req.data[2] = walking_pattern[23:16];
            req.data[3] = walking_pattern[31:24];
            req.build_cmd();
            req.calculate_crc();
            finish_item(req);
            #50000ns;
            
            // Read back and verify (in real test, scoreboard would verify)
            req = uart_frame_transaction::type_id::create($sformatf("test3_walk_read_%0d", i));
            start_item(req);
            req.is_write = 1'b0;
            req.auto_increment = 1'b0;
            req.addr = REG_TEST_3;
            req.length = 0;
            req.size = 2'b10;
            req.data = new[1];
            req.build_cmd();
            req.calculate_crc();
            finish_item(req);
            #50000ns;
        end
        
        `uvm_info(get_type_name(), "REG_TEST_0-3 Register Verification Completed", UVM_LOW)
    endtask

endclass