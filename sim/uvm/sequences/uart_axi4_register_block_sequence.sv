`timescale 1ns / 1ps

// =============================================================================
// uart_axi4_register_block_sequence.sv
// Register Block AXI4-Lite Diagnostic Sequence
// 
// Purpose: Test AXI4-Lite transactions to verify Register_Block state machine
// =============================================================================

`timescale 1ns / 1ps

class uart_axi4_register_block_sequence extends uvm_sequence#(uart_frame_transaction);

    `uvm_object_utils(uart_axi4_register_block_sequence)
    
    function new(string name = "uart_axi4_register_block_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction req;
        
        `uvm_info(get_type_name(), "Starting Register Block AXI4-Lite diagnostic sequence", UVM_LOW)
        
        // Test 1: Single AXI Write Transaction
        `uvm_info(get_type_name(), "=== Test 1: Single AXI Write Transaction ===", UVM_LOW)
        req = uart_frame_transaction::type_id::create("write_req");
        start_item(req);
        assert(req.randomize() with {
            cmd == 8'h01;           // Write command
            addr == 32'h00000100;   // Control register
            length == 3;            // 4 bytes (length+1)
            size == 2'b00;          // 8-bit transactions
            data[0] == 8'hAA;       // Test pattern
            data[1] == 8'hBB;
            data[2] == 8'hCC;
            data[3] == 8'hDD;
        });
        finish_item(req);
        
        // Wait and observe AXI handshakes
        #50000ns;
        
        // Test 2: Single AXI Read Transaction
        `uvm_info(get_type_name(), "=== Test 2: Single AXI Read Transaction ===", UVM_LOW)
        req = uart_frame_transaction::type_id::create("read_req");
        start_item(req);
        assert(req.randomize() with {
            cmd == 8'h81;           // Read command (RW bit set)
            addr == 32'h00000100;   // Control register
            length == 3;            // 4 bytes (length+1)
            size == 2'b00;          // 8-bit transactions
        });
        finish_item(req);
        
        // Wait and observe AXI handshakes
        #50000ns;
        
        // Test 3: Multiple Register Accesses
        `uvm_info(get_type_name(), "=== Test 3: Multiple Register Accesses ===", UVM_LOW)
        
        // Write to Status Register
        req = uart_frame_transaction::type_id::create("status_write");
        start_item(req);
        assert(req.randomize() with {
            cmd == 8'h01;
            addr == 32'h00000104;   // Status register
            length == 3;            // 4 bytes (length+1)
            size == 2'b00;          // 8-bit transactions
            data[0] == 8'h11;
            data[1] == 8'h22;
            data[2] == 8'h33;
            data[3] == 8'h44;
        });
        finish_item(req);
        
        #30000ns;
        
        // Read from Status Register
        req = uart_frame_transaction::type_id::create("status_read");
        start_item(req);
        assert(req.randomize() with {
            cmd == 8'h81;
            addr == 32'h00000104;   // Status register
            length == 3;            // 4 bytes (length+1)
            size == 2'b00;          // 8-bit transactions
        });
        finish_item(req);
        
        #30000ns;
        
        // Test 4: Rapid Transaction Sequence
        `uvm_info(get_type_name(), "=== Test 4: Rapid Transaction Sequence ===", UVM_LOW)
        
        for (int i = 0; i < 5; i++) begin
            // Write transaction
            req = uart_frame_transaction::type_id::create($sformatf("rapid_write_%0d", i));
            start_item(req);
            assert(req.randomize() with {
                cmd == 8'h01;
                addr == 32'h00000108 + (i * 4);  // Different registers
                length == 3;            // 4 bytes (length+1)
                size == 2'b00;          // 8-bit transactions
                data[0] == i + 8'h10;
                data[1] == i + 8'h20;
                data[2] == i + 8'h30;
                data[3] == i + 8'h40;
            });
            finish_item(req);
            
            #10000ns; // Short delay between transactions
            
            // Read transaction
            req = uart_frame_transaction::type_id::create($sformatf("rapid_read_%0d", i));
            start_item(req);
            assert(req.randomize() with {
                cmd == 8'h81;
                addr == 32'h00000108 + (i * 4);  // Same register
                length == 3;            // 4 bytes (length+1)
                size == 2'b00;          // 8-bit transactions
            });
            finish_item(req);
            
            #10000ns;
        end
        
        // Test 5: Error Condition Testing (Invalid Address)
        `uvm_info(get_type_name(), "=== Test 5: Invalid Address Access ===", UVM_LOW)
        req = uart_frame_transaction::type_id::create("invalid_addr_req");
        start_item(req);
        assert(req.randomize() with {
            cmd == 8'h81;
            addr == 32'hFFFFFFFF;   // Invalid address
            length == 3;            // 4 bytes (length+1)
            size == 2'b00;          // 8-bit transactions
        });
        finish_item(req);
        
        #50000ns;
        
        `uvm_info(get_type_name(), "Register Block AXI4-Lite diagnostic sequence completed", UVM_LOW)
        
    endtask

endclass