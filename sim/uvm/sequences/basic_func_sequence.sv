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

// Directed sequence targeting multi-beat auto-increment writes to stress WSTRB handling
class uart_axi4_multi_beat_write_seq extends uvm_sequence #(uart_frame_transaction);

    `uvm_object_utils(uart_axi4_multi_beat_write_seq)

    int beats = 4;
    logic [31:0] base_addr = 32'h1000;

    function new(string name = "uart_axi4_multi_beat_write_seq");
        super.new(name);
    endfunction

    virtual task body();
        uart_frame_transaction req;
        uart_frame_transaction enable_req;
        int bytes_per_beat;
        int total_bytes;

        `uvm_info("MULTI_BEAT_SEQ", $sformatf("Starting %0d-beat auto-increment write sequence", beats), UVM_LOW)

        bytes_per_beat = 1 << 2; // 32-bit beats
        total_bytes = beats * bytes_per_beat;

        // Ensure bridge is enabled before issuing the stress write
        `uvm_create(enable_req)

        enable_req.is_write = 1'b1;
        enable_req.auto_increment = 1'b0;
        enable_req.size = 2'b10;
        enable_req.length = 4'd0;    // Single 32-bit beat
        enable_req.addr = base_addr;
        enable_req.data = new[bytes_per_beat];
        enable_req.expect_error = 1'b0;

        // Write CONTROL register with bridge_enable=1 while clearing other bits
        enable_req.data[0] = 8'h01;
        enable_req.data[1] = 8'h00;
        enable_req.data[2] = 8'h00;
        enable_req.data[3] = 8'h00;

        enable_req.build_cmd();
        enable_req.calculate_crc();

        `uvm_send(enable_req)

        `uvm_create(req)

        req.is_write = 1'b1;
        req.auto_increment = 1'b1;
        req.size = 2'b10;        // 32-bit beats
        req.length = beats - 1;  // LEN field encodes beats-1
        req.addr = base_addr;
        req.data = new[total_bytes];

        for (int i = 0; i < total_bytes; i++) begin
            req.data[i] = 8'hC0 + i;
        end

        // Keep bridge enabled when the CONTROL register beat is written
        req.data[0] |= 8'h01;

        req.build_cmd();
        req.calculate_crc();

        `uvm_send(req)

        `uvm_info("MULTI_BEAT_SEQ", $sformatf("Completed multi-beat write: CMD=0x%02X ADDR=0x%08X", req.cmd, req.addr), UVM_LOW)
    endtask

endclass