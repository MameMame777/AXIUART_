`timescale 1ns / 1ps

// Error Injection Sequence for UART-AXI4 Bridge Testing
class uart_axi4_error_sequence extends uvm_sequence #(uart_frame_transaction);
    
    `uvm_object_utils(uart_axi4_error_sequence)
    
    function new(string name = "uart_axi4_error_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction req;
        
        `uvm_info("ERROR_SEQ", "Starting error injection sequence", UVM_LOW)
        
        // Test invalid command format
        `uvm_info("ERROR_SEQ", "Testing invalid command format", UVM_MEDIUM)
        req = uart_frame_transaction::type_id::create("invalid_cmd_req");
        start_item(req);
        req.cmd = 8'h70; // Invalid data length (bits 6:4 = 3'b111)
        req.addr = 32'h1008;
        req.sof = SOF_HOST_TO_DEVICE;
        req.direction = UART_RX;
        req.error_inject = 1;
        req.expect_error = 1;
        finish_item(req);
        
        // Test misaligned addresses
        `uvm_info("ERROR_SEQ", "Testing misaligned addresses", UVM_MEDIUM)
        req = uart_frame_transaction::type_id::create("misaligned_req");
        start_item(req);
        req.cmd = 8'h20; // 2-byte write
        req.addr = 32'h1009; // Odd address for 2-byte access
        req.sof = SOF_HOST_TO_DEVICE;
        req.direction = UART_RX;
        req.error_inject = 1;
        req.expect_error = 1;
        req.data = new[2];
        req.data[0] = 8'hAA;
        req.data[1] = 8'hBB;
        finish_item(req);
        
        req = uart_frame_transaction::type_id::create("misaligned_word_req");
        start_item(req);
        req.cmd = 8'h40; // 4-byte write
        req.addr = 32'h1002; // Non-word aligned for 4-byte access
        req.sof = SOF_HOST_TO_DEVICE;
        req.direction = UART_RX;
        req.error_inject = 1;
        req.expect_error = 1;
        req.data = new[4];
        req.data[0] = 8'hCC;
        req.data[1] = 8'hDD;
        req.data[2] = 8'hEE;
        req.data[3] = 8'hFF;
        finish_item(req);
        
        // Test reserved command bits
        `uvm_info("ERROR_SEQ", "Testing reserved command bits", UVM_MEDIUM)
        start_item(req);
        req.cmd = 8'h11; // Reserved bits set
        req.addr = 32'h2000;
        req.error_inject = 1;
        req.expect_error = 1;
        req.data = new[1];
        req.data[0] = 8'hCC;
        finish_item(req);
        
        // Test CRC errors (will be handled by driver/monitor)
        `uvm_info("ERROR_SEQ", "Testing frame with intentional CRC error", UVM_MEDIUM)
        start_item(req);
        req.cmd = 8'h10;
        req.addr = 32'h3000;
        req.error_inject = 1;
        req.expect_error = 1;
        req.force_crc_error = 1; // Special flag for driver
        req.data = new[1];
        req.data[0] = 8'hDD;
        finish_item(req);
        
        // Test timeout scenarios (driver will inject timing issues)
        `uvm_info("ERROR_SEQ", "Testing timeout scenarios", UVM_MEDIUM)
        start_item(req);
        req.cmd = 8'h90; // Read
        req.addr = 32'h4000;
        req.error_inject = 1;
        req.expect_error = 1;
        req.force_timeout = 1; // Special flag for driver
        req.data = new[0]; // No data for read
        finish_item(req);
        
        // Test frame format errors
        `uvm_info("ERROR_SEQ", "Testing frame format errors", UVM_MEDIUM)
        start_item(req);
        req.cmd = 8'h10;
        req.addr = 32'h5000;
        req.error_inject = 1;
        req.expect_error = 1;
        req.corrupt_frame_format = 1; // Special flag for driver
        req.data = new[1];
        req.data[0] = 8'hEE;
        finish_item(req);
        
        `uvm_info("ERROR_SEQ", "Error injection sequence completed", UVM_LOW)
    endtask
    
endclass

// CRC Error Injection Sequence
class uart_axi4_crc_error_sequence extends uvm_sequence #(uart_frame_transaction);
    
    `uvm_object_utils(uart_axi4_crc_error_sequence)
    
    function new(string name = "uart_axi4_crc_error_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction req;
        
        `uvm_info("CRC_ERROR_SEQ", "Starting CRC error sequence", UVM_LOW)
        
        // Generate transactions with intentional CRC errors
        for (int i = 0; i < 5; i++) begin
            `uvm_do_with(req, {
                cmd inside {8'h10, 8'h20, 8'h40, 8'h90, 8'hA0, 8'hC0}; // Valid commands
                addr == 32'h6000 + (i * 4);
                if (!cmd[7]) { // Write
                    data.size() == (1 << (cmd[6:4] - 1));
                    foreach(data[j]) data[j] == 8'hCC + j;
                }
                force_crc_error == 1;
            })
            
            // Add delay between error injections
            #1000ns;
        end
        
        `uvm_info("CRC_ERROR_SEQ", "CRC error sequence completed", UVM_LOW)
    endtask
    
endclass

// Protocol Violation Sequence
class uart_axi4_protocol_violation_sequence extends uvm_sequence #(uart_frame_transaction);
    
    `uvm_object_utils(uart_axi4_protocol_violation_sequence)
    
    function new(string name = "uart_axi4_protocol_violation_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction req;
        
        `uvm_info("PROTOCOL_VIOL_SEQ", "Starting protocol violation sequence", UVM_LOW)
        
        // Test incomplete frames
        `uvm_do_with(req, {
            cmd == 8'h10;
            addr == 32'h7000;
            data.size() == 1;
            truncate_frame == 1; // Special flag to truncate frame
        })
        
        // Test wrong SOF
        `uvm_do_with(req, {
            cmd == 8'h20;
            addr == 32'h7004;
            data.size() == 2;
            wrong_sof == 1; // Special flag for wrong SOF
        })
        
        // Test data size mismatch
        `uvm_do_with(req, {
            cmd == 8'h20; // Says 2 bytes
            addr == 32'h7008;
            data.size() == 4; // But send 4 bytes
        })
        
        // Test excessive data length
        `uvm_do_with(req, {
            cmd == 8'h40; // Says 4 bytes
            addr == 32'h700C;
            data.size() == 8; // But send 8 bytes
        })
        
        `uvm_info("PROTOCOL_VIOL_SEQ", "Protocol violation sequence completed", UVM_LOW)
    endtask
    
endclass

// Boundary Test Sequence
class uart_axi4_boundary_sequence extends uvm_sequence #(uart_frame_transaction);
    
    `uvm_object_utils(uart_axi4_boundary_sequence)
    
    function new(string name = "uart_axi4_boundary_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction req;
        
        `uvm_info("BOUNDARY_SEQ", "Starting boundary test sequence", UVM_LOW)
        
        // Test minimum address
        `uvm_do_with(req, {
            cmd == 8'h10;
            addr == 32'h00000000;
            data.size() == 1;
            data[0] == 8'h00;
        })
        
        // Test maximum valid address (implementation dependent)
        `uvm_do_with(req, {
            cmd == 8'h40;
            addr == 32'hFFFFFFFC; // Last word-aligned address
            data.size() == 4;
            foreach(data[i]) data[i] == 8'hFF;
        })
        
        // Test address wraparound scenarios
        `uvm_do_with(req, {
            cmd == 8'h20;
            addr == 32'hFFFFFFFE; // This will cause alignment issues
            data.size() == 2;
        })
        
        // Test all valid data patterns
        for (int pattern = 0; pattern < 8; pattern++) begin
            `uvm_do_with(req, {
                cmd == 8'h40;
                addr == 32'h8000 + (pattern * 4);
                data.size() == 4;
                data[0] == ((pattern & 1) ? 8'hFF : 8'h00);
                data[1] == ((pattern & 2) ? 8'hFF : 8'h00);
                data[2] == ((pattern & 4) ? 8'hFF : 8'h00);
                data[3] == 8'h55 + pattern; // Unique identifier
            })
        end
        
        `uvm_info("BOUNDARY_SEQ", "Boundary test sequence completed", UVM_LOW)
    endtask
    
endclass