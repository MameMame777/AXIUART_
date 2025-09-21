`timescale 1ns / 1ps

// Frame_Builder Diagnostic Sequence for UART-AXI4 Bridge Testing
class uart_axi4_frame_builder_sequence extends uvm_sequence #(uart_frame_transaction);
    
    `uvm_object_utils(uart_axi4_frame_builder_sequence)
    
    function new(string name = "uart_axi4_frame_builder_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction req;
        
        `uvm_info("FB_SEQ", "=== Frame_Builder Diagnostic Sequence Started ===", UVM_LOW)
        
        // Test 1: Read Response Frame Generation (16-bit read, single beat)
        `uvm_info("FB_SEQ", "Test 1: Read Response Frame Generation", UVM_LOW)
        req = uart_frame_transaction::type_id::create("read_req");
        start_item(req);
        req.cmd = 8'h91;           // Read: RW=1, INC=0, SIZE=16bit(01), LEN=1 (0001)
        req.addr = 32'h12345678;
        req.data = new[0];         // Host command has no data payload
        req.is_write = 1'b0;
        req.auto_increment = 1'b0;
        req.size = 2'b01;          // 16-bit
        req.length = 4'h0;         // LEN=1 (length+1)
        finish_item(req);
        
        #100ns; // Wait for response processing
        
        // Test 2: Write Response Frame Generation (32-bit write, single beat)
        `uvm_info("FB_SEQ", "Test 2: Write Response Frame Generation", UVM_LOW)
        req = uart_frame_transaction::type_id::create("write_req");
        start_item(req);
        req.cmd = 8'h43;           // Write: RW=0, INC=1, SIZE=32bit(10), LEN=1 (0011)
        req.addr = 32'h87654320;   // 32-bit aligned address
        req.data = new[4];         // 32-bit write data
        req.data[0] = 8'haa;
        req.data[1] = 8'hbb;  
        req.data[2] = 8'hcc;
        req.data[3] = 8'hdd;
        req.is_write = 1'b1;
        req.auto_increment = 1'b1;
        req.size = 2'b10;          // 32-bit
        req.length = 4'h0;         // LEN=1 (length+1)
        finish_item(req);
        
        #100ns; // Wait for response processing
        
        // Test 3: Error Response - Invalid command
        `uvm_info("FB_SEQ", "Test 3: Error Response Frame Generation", UVM_LOW)
        req = uart_frame_transaction::type_id::create("error_req");
        start_item(req);
        req.cmd = 8'h80;           // Invalid command (reserved bits set)
        req.addr = 32'h00000000;
        req.data = new[0];
        req.is_write = 1'b0;
        req.auto_increment = 1'b0;
        req.size = 2'b00;          // 8-bit
        req.length = 4'h0;         // LEN=1
        finish_item(req);
        
        #100ns; // Wait for response processing
        
        // Test 4: Multiple Sequential Read Responses  
        `uvm_info("FB_SEQ", "Test 4: Multiple Sequential Responses", UVM_LOW)
        
        // 4a: 16-bit read
        req = uart_frame_transaction::type_id::create("seq_read1");
        start_item(req);
        req.cmd = 8'h91;           // Read 16-bit, single beat
        req.addr = 32'h00001000;
        req.data = new[0];
        req.is_write = 1'b0;
        req.auto_increment = 1'b0;
        req.size = 2'b01;          // 16-bit
        req.length = 4'h0;         // LEN=1
        finish_item(req);
        #50ns;
        
        // 4b: 32-bit read  
        req = uart_frame_transaction::type_id::create("seq_read2");
        start_item(req);
        req.cmd = 8'h83;           // Read 32-bit, single beat  
        req.addr = 32'h00001004;
        req.data = new[0];
        req.is_write = 1'b0;
        req.auto_increment = 1'b0;
        req.size = 2'b10;          // 32-bit
        req.length = 4'h0;         // LEN=1
        finish_item(req);
        #50ns;
        
        // 4c: 32-bit write
        req = uart_frame_transaction::type_id::create("seq_write1");
        start_item(req);
        req.cmd = 8'h43;           // Write 32-bit, single beat
        req.addr = 32'h00001008;
        req.data = new[4];
        req.data[0] = 8'h11;
        req.data[1] = 8'h22;
        req.data[2] = 8'h33; 
        req.data[3] = 8'h44;
        req.is_write = 1'b1;
        req.auto_increment = 1'b1;
        req.size = 2'b10;          // 32-bit
        req.length = 4'h0;         // LEN=1
        finish_item(req);
        
        // Test 5: Rapid Command Generation  
        `uvm_info("FB_SEQ", "Test 5: Rapid Response Generation", UVM_LOW)
        for (int i = 0; i < 5; i++) begin
            req = uart_frame_transaction::type_id::create($sformatf("rapid_%0d", i));
            start_item(req);
            if (i % 2 == 0) begin
                // Read commands
                req.cmd = 8'h60;       // Read 8-bit, no increment, LEN=1
                req.addr = (32'h2000 + i * 8);
                req.data = new[0];
                req.is_write = 1'b0;
                req.auto_increment = 1'b0;
                req.size = 2'b00;      // 8-bit
                req.length = 4'h0;     // LEN=1
            end else begin
                // Read commands (changed from write to read for consistency)  
                req.cmd = 8'h83;       // Read 32-bit, single beat
                req.addr = (32'h2008 + i * 8);  
                req.data = new[0];
                req.is_write = 1'b0;
                req.auto_increment = 1'b0;
                req.size = 2'b10;      // 32-bit
                req.length = 4'h0;     // LEN=1
            end
            finish_item(req);
            #25ns; // Minimal delay for stress testing
        end
        
        `uvm_info("FB_SEQ", "=== Frame_Builder Diagnostic Sequence Completed ===", UVM_LOW)
    endtask
    
endclass