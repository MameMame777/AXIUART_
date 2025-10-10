`timescale 1ns / 1ps

// Simple test register sequence for direct verification
class simple_test_register_sequence extends uvm_sequence#(uart_frame_transaction);
    
    `uvm_object_utils(simple_test_register_sequence)
    
    function new(string name = "simple_test_register_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction req;
        
        `uvm_info("SIMPLE_TEST_REG", "=== Simple Test Register Verification ===", UVM_LOW)
        
        // Test REG_TEST_0 (0x1020) - Write 0x12345678
        `uvm_info("SIMPLE_TEST_REG", "Testing REG_TEST_0 (0x1020) write...", UVM_LOW)
        
        req = uart_frame_transaction::type_id::create("write_req");
        start_item(req);
        
        req.cmd = 8'h20;  // 32-bit write command
        req.addr = 32'h0000_1020;
        req.data = new[4];
        req.data[0] = 8'h78;  // LSB
        req.data[1] = 8'h56;
        req.data[2] = 8'h34;
        req.data[3] = 8'h12;  // MSB
        
        finish_item(req);
        
        `uvm_info("SIMPLE_TEST_REG", "✓ REG_TEST_0 write request sent", UVM_LOW)
        
        // Wait a bit
        #5000;
        
        // Test REG_TEST_0 (0x1020) - Read back
        `uvm_info("SIMPLE_TEST_REG", "Testing REG_TEST_0 (0x1020) read...", UVM_LOW)
        
        req = uart_frame_transaction::type_id::create("read_req");
        start_item(req);
        
        req.cmd = 8'hA0;  // 32-bit read command
        req.addr = 32'h0000_1020;
        req.data = new[0]; // No data for read operation
        
        finish_item(req);
        
        `uvm_info("SIMPLE_TEST_REG", "✓ REG_TEST_0 read request sent", UVM_LOW)
        
        #5000;
        
        // Test REG_TEST_1 (0x1024) - Write 0xDEADBEEF
        `uvm_info("SIMPLE_TEST_REG", "Testing REG_TEST_1 (0x1024) write...", UVM_LOW)
        
        req = uart_frame_transaction::type_id::create("write_req2");
        start_item(req);
        
        req.cmd = 8'h20;  // 32-bit write command
        req.addr = 32'h0000_1024;
        req.data = new[4];
        req.data[0] = 8'hEF;  // LSB
        req.data[1] = 8'hBE;
        req.data[2] = 8'hAD;
        req.data[3] = 8'hDE;  // MSB
        
        finish_item(req);
        
        `uvm_info("SIMPLE_TEST_REG", "✓ REG_TEST_1 write request sent", UVM_LOW)
        
        #5000;
        
        // Test REG_TEST_1 (0x1024) - Read back
        `uvm_info("SIMPLE_TEST_REG", "Testing REG_TEST_1 (0x1024) read...", UVM_LOW)
        
        req = uart_frame_transaction::type_id::create("read_req2");
        start_item(req);
        
        req.cmd = 8'hA0;  // 32-bit read command
        req.addr = 32'h0000_1024;
        req.data = new[0]; // No data for read operation
        
        finish_item(req);
        
        `uvm_info("SIMPLE_TEST_REG", "✓ REG_TEST_1 read request sent", UVM_LOW)
        
        #5000;
        
        `uvm_info("SIMPLE_TEST_REG", "=== Simple Test Register Verification Complete ===", UVM_LOW)
        
    endtask
    
endclass