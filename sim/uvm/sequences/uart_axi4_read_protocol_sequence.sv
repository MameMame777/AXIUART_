`timescale 1ns / 1ps

// ================================================
// uart_axi4_read_protocol_sequence.sv
// Read Protocol Verification Sequence
// Tests the Frame_Builder fix for read protocol responses
// ================================================

class uart_axi4_read_protocol_sequence extends uvm_sequence #(uart_frame_transaction);

    `uvm_object_utils(uart_axi4_read_protocol_sequence)
    
    // Register addresses (from register_map.md)
    parameter bit [31:0] REG_BASE_ADDR = 32'h00001000;
    parameter bit [31:0] REG_VERSION   = REG_BASE_ADDR + 32'h01C;  // 0x0000101C
    parameter bit [31:0] REG_TEST_0    = REG_BASE_ADDR + 32'h020;  // 0x00001020
    
    function new(string name = "uart_axi4_read_protocol_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction req;
        
        `uvm_info(get_type_name(), "=== Read Protocol Verification Sequence Started ===", UVM_LOW)
        
        // Test 1: Read Version Register
        `uvm_info(get_type_name(), "=== Test 1: Version Register Read ===", UVM_LOW)
        req = uart_frame_transaction::type_id::create("version_read");
        start_item(req);
        assert(req.randomize() with {
            is_write == 1'b0;           // Read operation
            auto_increment == 1'b0;     // Single register
            size == 2'b10;             // 32-bit transaction
            length == 0;                // Single beat
        });
        // Set address and cmd after randomization (non-rand fields)
        req.addr = REG_VERSION;         // Version register address
        req.cmd = READ_CMD | (req.auto_increment << 6) | (req.size << 4) | req.length;
        finish_item(req);
        
        `uvm_info(get_type_name(), 
            $sformatf("Version read request: ADDR=0x%08X, SIZE=32-bit, LEN=1", REG_VERSION), 
            UVM_LOW)
        
        // Wait for response processing
        #50000ns;
        
        // Test 2: Write Test Register 0
        `uvm_info(get_type_name(), "=== Test 2: Test Register Write ===", UVM_LOW)
        req = uart_frame_transaction::type_id::create("test_write");
        start_item(req);
        assert(req.randomize() with {
            is_write == 1'b1;           // Write operation
            auto_increment == 1'b0;     // Single register
            length == 0;                // Single beat
            size == 2'b10;             // 32-bit transaction
        });
        // Set address, cmd, and data after randomization (non-rand fields)
        req.addr = REG_TEST_0;         // Test register 0 address
        req.cmd = WRITE_CMD | (req.auto_increment << 6) | (req.size << 4) | req.length;
        req.data = new[4];             // Allocate data array
        req.data[0] = 8'h78;          // Test value 0x12345678 (little-endian)
        req.data[1] = 8'h56;
        req.data[2] = 8'h34;
        req.data[3] = 8'h12;
        finish_item(req);
        
        `uvm_info(get_type_name(), 
            $sformatf("Test write request: ADDR=0x%08X, DATA=0x12345678", REG_TEST_0), 
            UVM_LOW)
        
        // Wait for write completion
        #50000ns;
        
        // Test 3: Read back Test Register 0
        `uvm_info(get_type_name(), "=== Test 3: Test Register Read-back ===", UVM_LOW)
        req = uart_frame_transaction::type_id::create("test_read");
        start_item(req);
        assert(req.randomize() with {
            is_write == 1'b0;           // Read operation
            auto_increment == 1'b0;     // Single register
            length == 0;                // Single beat
            size == 2'b10;             // 32-bit transaction
        });
        // Set address and cmd after randomization (non-rand fields)
        req.addr = REG_TEST_0;         // Test register 0 address
        req.cmd = READ_CMD | (req.auto_increment << 6) | (req.size << 4) | req.length;
        finish_item(req);
        
        `uvm_info(get_type_name(), 
            $sformatf("Test read-back request: ADDR=0x%08X", REG_TEST_0), 
            UVM_LOW)
        
        // Wait for read completion
        #50000ns;
        
        // Test 4: Multi-register Read Pattern
        `uvm_info(get_type_name(), "=== Test 4: Multi-register Read Pattern ===", UVM_LOW)
        
        // Read multiple test registers to check for consistent protocol behavior
        for (int i = 0; i < 4; i++) begin
            automatic bit [31:0] test_addr = REG_BASE_ADDR + 32'h020 + (i * 4);
            
            req = uart_frame_transaction::type_id::create($sformatf("multi_read_%0d", i));
            start_item(req);
            assert(req.randomize() with {
                is_write == 1'b0;       // Read operation
                auto_increment == 1'b0; // Single register
                length == 0;            // Single beat
                size == 2'b10;         // 32-bit transaction
            });
            // Set address and cmd after randomization (non-rand fields)
            req.addr = test_addr;      // Test register addresses
            req.cmd = READ_CMD | (req.auto_increment << 6) | (req.size << 4) | req.length;
            finish_item(req);
            
            `uvm_info(get_type_name(), 
                $sformatf("Multi-read %0d: ADDR=0x%08X", i, test_addr), 
                UVM_LOW)
                
            // Wait between reads
            #50000ns;
        end
        
        `uvm_info(get_type_name(), "Read Protocol Verification sequence completed", UVM_LOW)
    endtask
    
endclass