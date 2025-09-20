`timescale 1ns / 1ps

// Active UART Protocol Sequence - implements real UART communication to improve coverage
class uart_protocol_active_sequence extends uvm_sequence #(uart_frame_transaction);
    `uvm_object_utils(uart_protocol_active_sequence)

    function new(string name = "uart_protocol_active_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction frame_tx;
        
        `uvm_info(get_type_name(), "Starting UART Protocol Active Sequence", UVM_MEDIUM)
        
        // Test 1: Basic write command
        `uvm_create(frame_tx)
        frame_tx.sof = 8'hAA;
        frame_tx.cmd = 8'h57; // Write command
        frame_tx.addr = 32'h1000;
        frame_tx.len = 8'h01;
        frame_tx.data = new[1];
        frame_tx.data[0] = 8'hAB;
        frame_tx.crc = 8'h00; // Will be calculated by DUT
        frame_tx.force_crc_error = 0;
        frame_tx.force_timeout = 0;
        frame_tx.corrupt_frame_format = 0;
        frame_tx.truncate_frame = 0;
        frame_tx.wrong_sof = 0;
        `uvm_send(frame_tx)
        
        // Add delay between frames
        #1000ns;
        
        // Test 2: Basic read command  
        `uvm_create(frame_tx)
        frame_tx.sof = 8'hAA;
        frame_tx.cmd = 8'hD2; // Read command
        frame_tx.addr = 32'h1000; 
        frame_tx.len = 8'h01;
        frame_tx.data = new[0]; // No data for read
        frame_tx.crc = 8'h00;
        frame_tx.force_crc_error = 0;
        frame_tx.force_timeout = 0;
        frame_tx.corrupt_frame_format = 0;
        frame_tx.truncate_frame = 0;
        frame_tx.wrong_sof = 0;
        `uvm_send(frame_tx)

        // Add delay between frames
        #1000ns;

        // Test 3: 8-bit auto-increment write
        `uvm_create(frame_tx)
        frame_tx.sof = 8'hAA;
        frame_tx.cmd = 8'h5F; // 8-bit auto-increment write
        frame_tx.addr = 32'h2000;
        frame_tx.len = 8'h04; 
        frame_tx.data = new[4];
        frame_tx.data[0] = 8'h11;
        frame_tx.data[1] = 8'h22; 
        frame_tx.data[2] = 8'h33;
        frame_tx.data[3] = 8'h44;
        frame_tx.crc = 8'h00;
        frame_tx.force_crc_error = 0;
        frame_tx.force_timeout = 0;
        frame_tx.corrupt_frame_format = 0;
        frame_tx.truncate_frame = 0;
        frame_tx.wrong_sof = 0;
        `uvm_send(frame_tx)

        // Add delay between frames
        #1000ns;

        // Test 4: 32-bit write
        `uvm_create(frame_tx) 
        frame_tx.sof = 8'hAA;
        frame_tx.cmd = 8'h6B; // 32-bit write
        frame_tx.addr = 32'h3000;
        frame_tx.len = 8'h04;
        frame_tx.data = new[4];
        frame_tx.data[0] = 8'hDE;
        frame_tx.data[1] = 8'hAD; 
        frame_tx.data[2] = 8'hBE;
        frame_tx.data[3] = 8'hEF;
        frame_tx.crc = 8'h00;
        frame_tx.force_crc_error = 0;
        frame_tx.force_timeout = 0;
        frame_tx.corrupt_frame_format = 0;
        frame_tx.truncate_frame = 0;
        frame_tx.wrong_sof = 0;
        `uvm_send(frame_tx)

        // Add delay between frames
        #1000ns;

        // Test 5: Misaligned address test 
        `uvm_create(frame_tx)
        frame_tx.sof = 8'hAA;
        frame_tx.cmd = 8'h6B; // 32-bit write to misaligned address
        frame_tx.addr = 32'h3001; // Not 4-byte aligned - should trigger error
        frame_tx.len = 8'h04;
        frame_tx.data = new[4];
        frame_tx.data[0] = 8'hFF;
        frame_tx.data[1] = 8'hFF;
        frame_tx.data[2] = 8'hFF;
        frame_tx.data[3] = 8'hFF;
        frame_tx.crc = 8'h00;
        frame_tx.force_crc_error = 0;
        frame_tx.force_timeout = 0;
        frame_tx.corrupt_frame_format = 0;
        frame_tx.truncate_frame = 0;
        frame_tx.wrong_sof = 0;
        `uvm_send(frame_tx)
        
        `uvm_info(get_type_name(), "UART Protocol Active Sequence completed", UVM_MEDIUM)
    endtask

endclass
