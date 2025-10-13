`timescale 1ns / 1ps

// UART AXI4 Write Protocol Sequence
// Created: October 13, 2025
// Purpose: AXI4 write protocol verification sequence
// Compliant with Phase 4.1.3 specifications

class uart_axi4_write_protocol_sequence extends uart_base_sequence;
    
    `uvm_object_utils(uart_axi4_write_protocol_sequence)
    
    // Sequence configuration
    int num_write_transactions = 20;
    bit enable_burst_writes = 1'b1;
    bit enable_single_writes = 1'b1;
    bit enable_unaligned_writes = 1'b1;
    
    function new(string name = "uart_axi4_write_protocol_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_transaction req;
        bit [31:0] write_addresses[$];
        bit [31:0] write_data[$];
        
        `uvm_info("WRITE_PROTOCOL_SEQ", "Starting AXI4 write protocol sequence", UVM_MEDIUM)
        
        // Initialize test addresses and data
        prepare_write_test_vectors(write_addresses, write_data);
        
        // Phase 1: Single aligned writes
        if (enable_single_writes) begin
            execute_single_write_phase(write_addresses, write_data);
        end
        
        // Phase 2: Burst writes
        if (enable_burst_writes) begin
            execute_burst_write_phase(write_addresses, write_data);
        end
        
        // Phase 3: Unaligned writes
        if (enable_unaligned_writes) begin
            execute_unaligned_write_phase(write_addresses, write_data);
        end
        
        // Phase 4: Protocol verification
        execute_protocol_verification_phase();
        
        `uvm_info("WRITE_PROTOCOL_SEQ", "AXI4 write protocol sequence completed", UVM_MEDIUM)
    endtask
    
    virtual task prepare_write_test_vectors(ref bit [31:0] addresses[$], ref bit [31:0] data[$]);
        // Prepare standard AXI4 write test vectors
        addresses.push_back(32'h1000_0000); // UART TX data register
        addresses.push_back(32'h1000_0004); // UART control register
        addresses.push_back(32'h1000_0008); // UART status register
        addresses.push_back(32'h1000_000C); // UART baud rate register
        addresses.push_back(32'h1000_0010); // Bridge control register
        
        data.push_back(32'h5A5A5A5A);
        data.push_back(32'hA5A5A5A5);
        data.push_back(32'h12345678);
        data.push_back(32'h87654321);
        data.push_back(32'hDEADBEEF);
        
        `uvm_info("WRITE_PROTOCOL_SEQ", $sformatf("Prepared %0d write test vectors", addresses.size()), UVM_LOW)
    endtask
    
    virtual task execute_single_write_phase(ref bit [31:0] addresses[$], ref bit [31:0] data[$]);
        uart_transaction req;
        
        `uvm_info("WRITE_PROTOCOL_SEQ", "Starting single write phase", UVM_MEDIUM)
        
        for (int i = 0; i < addresses.size(); i++) begin
            req = uart_transaction::type_id::create("write_req");
            start_item(req);
            
            if (!req.randomize() with {
                req.transaction_type == WRITE;
                req.address == addresses[i];
                req.data == data[i];
                req.enable_protocol_checking == 1'b1;
            }) begin
                `uvm_fatal("WRITE_PROTOCOL_SEQ", "Failed to randomize single write transaction")
            end
            
            finish_item(req);
            
            // Protocol timing compliance
            #100ns;
        end
        
        `uvm_info("WRITE_PROTOCOL_SEQ", "Single write phase completed", UVM_MEDIUM)
    endtask
    
    virtual task execute_burst_write_phase(ref bit [31:0] addresses[$], ref bit [31:0] data[$]);
        uart_transaction req;
        
        `uvm_info("WRITE_PROTOCOL_SEQ", "Starting burst write phase", UVM_MEDIUM)
        
        // Execute burst writes with different burst lengths
        for (int burst_len = 2; burst_len <= 4; burst_len++) begin
            for (int i = 0; i < addresses.size() - burst_len + 1; i++) begin
                req = uart_transaction::type_id::create("burst_write_req");
                start_item(req);
                
                if (!req.randomize() with {
                    req.transaction_type == BURST_WRITE;
                    req.address == addresses[i];
                    req.burst_length == burst_len;
                    req.enable_protocol_checking == 1'b1;
                }) begin
                    `uvm_fatal("WRITE_PROTOCOL_SEQ", "Failed to randomize burst write transaction")
                end
                
                finish_item(req);
                
                // Burst timing compliance
                #200ns;
            end
        end
        
        `uvm_info("WRITE_PROTOCOL_SEQ", "Burst write phase completed", UVM_MEDIUM)
    endtask
    
    virtual task execute_unaligned_write_phase(ref bit [31:0] addresses[$], ref bit [31:0] data[$]);
        uart_transaction req;
        bit [31:0] unaligned_addr;
        
        `uvm_info("WRITE_PROTOCOL_SEQ", "Starting unaligned write phase", UVM_MEDIUM)
        
        for (int i = 0; i < addresses.size(); i++) begin
            // Create unaligned addresses (non-4-byte aligned)
            unaligned_addr = addresses[i] + 1; // +1, +2, +3 byte offset
            
            req = uart_transaction::type_id::create("unaligned_write_req");
            start_item(req);
            
            if (!req.randomize() with {
                req.transaction_type == WRITE;
                req.address == unaligned_addr;
                req.data == data[i];
                req.enable_protocol_checking == 1'b1;
                req.expect_alignment_error == 1'b1;
            }) begin
                `uvm_fatal("WRITE_PROTOCOL_SEQ", "Failed to randomize unaligned write transaction")
            end
            
            finish_item(req);
            
            // Unaligned timing compliance
            #150ns;
        end
        
        `uvm_info("WRITE_PROTOCOL_SEQ", "Unaligned write phase completed", UVM_MEDIUM)
    endtask
    
    virtual task execute_protocol_verification_phase();
        uart_transaction req;
        
        `uvm_info("WRITE_PROTOCOL_SEQ", "Starting protocol verification phase", UVM_MEDIUM)
        
        // Test AXI4 protocol compliance
        for (int i = 0; i < 5; i++) begin
            req = uart_transaction::type_id::create("protocol_verify_req");
            start_item(req);
            
            if (!req.randomize() with {
                req.transaction_type == PROTOCOL_VERIFY;
                req.enable_protocol_checking == 1'b1;
                req.enable_timing_checks == 1'b1;
            }) begin
                `uvm_fatal("WRITE_PROTOCOL_SEQ", "Failed to randomize protocol verification transaction")
            end
            
            finish_item(req);
            
            // Protocol verification timing
            #300ns;
        end
        
        `uvm_info("WRITE_PROTOCOL_SEQ", "Protocol verification phase completed", UVM_MEDIUM)
    endtask
    
endclass : uart_axi4_write_protocol_sequence