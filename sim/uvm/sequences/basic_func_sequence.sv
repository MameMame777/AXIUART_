`timescale 1ns / 1ps

// Basic Functional Sequence for UART-AXI4 Bridge Testing
class uart_axi4_basic_sequence extends uvm_sequence #(uart_frame_transaction);
    
    `uvm_object_utils(uart_axi4_basic_sequence)
    
    // Configuration
    uart_axi4_env_config cfg;
    
    // Test parameters
    int num_transactions = 10;
    bit test_reads = 1;
    bit test_writes = 1;
    
    function new(string name = "uart_axi4_basic_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction req;
        
        `uvm_info("BASIC_SEQ", $sformatf("Starting basic sequence with %0d transactions", num_transactions), UVM_LOW)
        
        for (int i = 0; i < num_transactions; i++) begin
            `uvm_do_with(req, {
                if (test_writes && test_reads) {
                    cmd[7] dist { 0 := 50, 1 := 50 }; // 50% writes, 50% reads
                } else if (test_writes) {
                    cmd[7] == 0; // Write only
                } else {
                    cmd[7] == 1; // Read only
                }
                cmd[6:4] inside {3'b001, 3'b010, 3'b100}; // Valid data length codes
                cmd[3:0] == 0; // Reserved bits
                addr[1:0] == 0; // Word-aligned addresses
                addr inside {[32'h1000:32'h101C]}; // Valid register block range (BASE_ADDR + register offsets)
                if (!cmd[7]) { // Write command
                    data.size() inside {1, 2, 4}; // Valid data sizes
                }
            })
            
            // Initialize data array with predictable values after randomization
            if (!req.cmd[7]) begin // Write command
                for (int j = 0; j < req.data.size(); j++) begin
                    req.data[j] = 8'h10 + i + j;
                end
            end
            
            `uvm_info("BASIC_SEQ", $sformatf("Transaction %0d: CMD=0x%02X, ADDR=0x%08X", 
                      i+1, req.cmd, req.addr), UVM_MEDIUM)
        end
        
        `uvm_info("BASIC_SEQ", "Basic sequence completed", UVM_LOW)
    endtask
    
endclass

// Read-focused sequence
class uart_axi4_read_sequence extends uvm_sequence #(uart_frame_transaction);
    
    `uvm_object_utils(uart_axi4_read_sequence)
    
    int num_reads = 5;
    logic [31:0] base_addr = 32'h1000;
    
    function new(string name = "uart_axi4_read_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction req;
        
        `uvm_info("READ_SEQ", $sformatf("Starting read sequence with %0d reads from base 0x%08X", 
                  num_reads, base_addr), UVM_LOW)
        
        for (int i = 0; i < num_reads; i++) begin
            `uvm_do_with(req, {
                cmd[7] == 1; // Read command
                cmd[6:4] inside {3'b001, 3'b010, 3'b100}; // 1, 2, or 4 bytes
                cmd[3:0] == 0; // Reserved
                addr == base_addr + (i * 4); // Sequential word addresses
            })
        end
        
        `uvm_info("READ_SEQ", "Read sequence completed", UVM_LOW)
    endtask
    
endclass

// Write-focused sequence
class uart_axi4_write_sequence extends uvm_sequence #(uart_frame_transaction);
    
    `uvm_object_utils(uart_axi4_write_sequence)
    
    int num_writes = 5;
    logic [31:0] base_addr = 32'h2000;
    
    function new(string name = "uart_axi4_write_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction req;
        
        `uvm_info("WRITE_SEQ", $sformatf("Starting write sequence with %0d writes to base 0x%08X", 
                  num_writes, base_addr), UVM_LOW)
        
        for (int i = 0; i < num_writes; i++) begin
            `uvm_do_with(req, {
                cmd[7] == 0; // Write command
                cmd[6:4] inside {3'b001, 3'b010, 3'b100}; // 1, 2, or 4 bytes
                cmd[3:0] == 0; // Reserved
                addr == base_addr + (i * 4); // Sequential word addresses
                data.size() == (1 << (cmd[6:4] - 1)); // Match data size to length field
                foreach(data[j]) {
                    data[j] == 8'hA0 + i + j; // Predictable test pattern
                }
            })
        end
        
        `uvm_info("WRITE_SEQ", "Write sequence completed", UVM_LOW)
    endtask
    
endclass

// Burst test sequence (multiple sizes)
class uart_axi4_burst_sequence extends uvm_sequence #(uart_frame_transaction);
    
    `uvm_object_utils(uart_axi4_burst_sequence)
    
    function new(string name = "uart_axi4_burst_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction req;
        logic [31:0] test_addr = 32'h3000;
        
        `uvm_info("BURST_SEQ", "Starting burst sequence with different data sizes", UVM_LOW)
        
        // Test 1-byte transactions
        for (int i = 0; i < 4; i++) begin
            `uvm_do_with(req, {
                cmd == 8'h10; // Write 1 byte
                addr == test_addr + i;
                data.size() == 1;
                data[0] == 8'h10 + i;
            })
        end
        
        // Test 2-byte transactions  
        for (int i = 0; i < 2; i++) begin
            `uvm_do_with(req, {
                cmd == 8'h20; // Write 2 bytes
                addr == test_addr + 16 + (i * 2);
                data.size() == 2;
                data[0] == 8'h20 + (i * 2);
                data[1] == 8'h21 + (i * 2);
            })
        end
        
        // Test 4-byte transactions
        `uvm_do_with(req, {
            cmd == 8'h40; // Write 4 bytes
            addr == test_addr + 32;
            data.size() == 4;
            data[0] == 8'h40;
            data[1] == 8'h41;
            data[2] == 8'h42;
            data[3] == 8'h43;
        })
        
        // Read back the data
        for (int i = 0; i < 4; i++) begin
            `uvm_do_with(req, {
                cmd == 8'h90; // Read 1 byte
                addr == test_addr + i;
            })
        end
        
        for (int i = 0; i < 2; i++) begin
            `uvm_do_with(req, {
                cmd == 8'hA0; // Read 2 bytes
                addr == test_addr + 16 + (i * 2);
            })
        end
        
        `uvm_do_with(req, {
            cmd == 8'hC0; // Read 4 bytes
            addr == test_addr + 32;
        })
        
        `uvm_info("BURST_SEQ", "Burst sequence completed", UVM_LOW)
    endtask
    
endclass