// =============================================================================
// uart_axi4_register_simple_sequence.sv
// Simple Register Test Sequence with Fixed Values (No Randomization)
// 
// Purpose: Test AXI4-Lite register write/read without randomization issues
// =============================================================================

class uart_axi4_register_simple_sequence extends uvm_sequence#(uart_frame_transaction);

    `uvm_object_utils(uart_axi4_register_simple_sequence)
    
    localparam bit [31:0] REG_BASE_ADDR = 32'h0000_1000;
    localparam bit [31:0] REG_CONTROL   = REG_BASE_ADDR + 32'h000;
    localparam bit [31:0] REG_STATUS    = REG_BASE_ADDR + 32'h004;
    localparam bit [31:0] REG_CONFIG    = REG_BASE_ADDR + 32'h008;
    localparam bit [31:0] REG_DEBUG     = REG_BASE_ADDR + 32'h00C;

    function new(string name = "uart_axi4_register_simple_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction req;
        
        `uvm_info(get_type_name(), "Starting Simple Register Write/Read Test Sequence", UVM_LOW)
        
        // Test 1: Write 0x44444444 to CONFIG register
        `uvm_info(get_type_name(), "=== Test 1: Write CONFIG Register ===", UVM_LOW)
        req = uart_frame_transaction::type_id::create("config_write_req");
        start_item(req);
        req.is_write = 1'b1;
        req.auto_increment = 1'b0;
        req.addr = REG_CONFIG;
        req.length = 0;            // Single beat
        req.size = 2'b10;          // 32-bit transaction
        req.data = new[4];
        req.data[0] = 8'h44;       // 0x44444444
        req.data[1] = 8'h44;
        req.data[2] = 8'h44;
        req.data[3] = 8'h44;
        finish_item(req);
        
        #100000ns;  // Wait for write to complete
        
        // Test 2: Read back from CONFIG register
        `uvm_info(get_type_name(), "=== Test 2: Read CONFIG Register ===", UVM_LOW)
        req = uart_frame_transaction::type_id::create("config_read_req");
        start_item(req);
        req.is_write = 1'b0;
        req.auto_increment = 1'b0;
        req.addr = REG_CONFIG;
        req.length = 0;            // Single beat
        req.size = 2'b10;          // 32-bit transaction
        req.data = new[1];         // Minimal data array for read
        finish_item(req);
        
        #100000ns;  // Wait for read to complete
        
        // Test 3: Write 0x12345678 to DEBUG register
        `uvm_info(get_type_name(), "=== Test 3: Write DEBUG Register ===", UVM_LOW)
        req = uart_frame_transaction::type_id::create("debug_write_req");
        start_item(req);
        req.is_write = 1'b1;
        req.auto_increment = 1'b0;
        req.addr = REG_DEBUG;
        req.length = 0;            // Single beat
        req.size = 2'b10;          // 32-bit transaction
        req.data = new[4];
        req.data[0] = 8'h78;       // 0x12345678 (little endian)
        req.data[1] = 8'h56;
        req.data[2] = 8'h34;
        req.data[3] = 8'h12;
        finish_item(req);
        
        #100000ns;  // Wait for write to complete
        
        // Test 4: Read back from DEBUG register
        `uvm_info(get_type_name(), "=== Test 4: Read DEBUG Register ===", UVM_LOW)
        req = uart_frame_transaction::type_id::create("debug_read_req");
        start_item(req);
        req.is_write = 1'b0;
        req.auto_increment = 1'b0;
        req.addr = REG_DEBUG;
        req.length = 0;            // Single beat
        req.size = 2'b10;          // 32-bit transaction
        req.data = new[1];         // Minimal data array for read
        finish_item(req);
        
        #100000ns;  // Wait for read to complete
        
        `uvm_info(get_type_name(), "Simple Register Write/Read Test Sequence completed", UVM_LOW)
    endtask

endclass