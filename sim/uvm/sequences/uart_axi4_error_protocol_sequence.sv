`timescale 1ns / 1ps

// UART AXI4 Error Protocol Sequence
// Created: October 13, 2025
// Purpose: Error handling and protocol violation verification sequence
// Compliant with Phase 4.1.3 specifications

class uart_axi4_error_protocol_sequence extends uart_base_sequence;
    
    `uvm_object_utils(uart_axi4_error_protocol_sequence)
    
    // Sequence configuration
    int num_error_scenarios = 15;
    bit enable_address_errors = 1'b1;
    bit enable_protocol_violations = 1'b1;
    bit enable_timeout_errors = 1'b1;
    
    function new(string name = "uart_axi4_error_protocol_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_transaction req;
        
        `uvm_info("ERROR_PROTOCOL_SEQ", "Starting AXI4 error protocol sequence", UVM_MEDIUM)
        
        // Phase 1: Address error scenarios
        if (enable_address_errors) begin
            execute_address_error_phase();
        end
        
        // Phase 2: Protocol violation scenarios
        if (enable_protocol_violations) begin
            execute_protocol_violation_phase();
        end
        
        // Phase 3: Timeout error scenarios
        if (enable_timeout_errors) begin
            execute_timeout_error_phase();
        end
        
        // Phase 4: Recovery verification
        execute_error_recovery_phase();
        
        `uvm_info("ERROR_PROTOCOL_SEQ", "AXI4 error protocol sequence completed", UVM_MEDIUM)
    endtask
    
    virtual task execute_address_error_phase();
        uart_transaction req;
        bit [31:0] invalid_addresses[$];
        
        `uvm_info("ERROR_PROTOCOL_SEQ", "Starting address error phase", UVM_MEDIUM)
        
        // Prepare invalid addresses
        invalid_addresses.push_back(32'hFFFF_FFFF); // Out of range
        invalid_addresses.push_back(32'h0000_0000); // Null address
        invalid_addresses.push_back(32'h2000_0000); // Invalid memory space
        invalid_addresses.push_back(32'h1000_FFFF); // Beyond UART address space
        
        for (int i = 0; i < invalid_addresses.size(); i++) begin
            req = uart_transaction::type_id::create("addr_error_req");
            start_item(req);
            
            if (!req.randomize() with {
                req.transaction_type == WRITE;
                req.address == invalid_addresses[i];
                req.enable_error_injection == 1'b1;
                req.expect_address_error == 1'b1;
            }) begin
                `uvm_fatal("ERROR_PROTOCOL_SEQ", "Failed to randomize address error transaction")
            end
            
            finish_item(req);
            
            // Error response timing
            #250ns;
        end
        
        `uvm_info("ERROR_PROTOCOL_SEQ", "Address error phase completed", UVM_MEDIUM)
    endtask
    
    virtual task execute_protocol_violation_phase();
        uart_transaction req;
        
        `uvm_info("ERROR_PROTOCOL_SEQ", "Starting protocol violation phase", UVM_MEDIUM)
        
        // Test invalid AXI4 protocol scenarios
        for (int i = 0; i < 5; i++) begin
            req = uart_transaction::type_id::create("protocol_viol_req");
            start_item(req);
            
            if (!req.randomize() with {
                req.transaction_type == PROTOCOL_VIOLATION;
                req.enable_error_injection == 1'b1;
                req.expect_protocol_error == 1'b1;
            }) begin
                `uvm_fatal("ERROR_PROTOCOL_SEQ", "Failed to randomize protocol violation transaction")
            end
            
            finish_item(req);
            
            // Protocol violation timing
            #300ns;
        end
        
        `uvm_info("ERROR_PROTOCOL_SEQ", "Protocol violation phase completed", UVM_MEDIUM)
    endtask
    
    virtual task execute_timeout_error_phase();
        uart_transaction req;
        
        `uvm_info("ERROR_PROTOCOL_SEQ", "Starting timeout error phase", UVM_MEDIUM)
        
        // Test timeout scenarios
        for (int i = 0; i < 3; i++) begin
            req = uart_transaction::type_id::create("timeout_error_req");
            start_item(req);
            
            if (!req.randomize() with {
                req.transaction_type == TIMEOUT_TEST;
                req.enable_error_injection == 1'b1;
                req.expect_timeout_error == 1'b1;
            }) begin
                `uvm_fatal("ERROR_PROTOCOL_SEQ", "Failed to randomize timeout error transaction")
            end
            
            finish_item(req);
            
            // Timeout error timing (extended)
            #1000000ns; // 1ms timeout
        end
        
        `uvm_info("ERROR_PROTOCOL_SEQ", "Timeout error phase completed", UVM_MEDIUM)
    endtask
    
    virtual task execute_error_recovery_phase();
        uart_transaction req;
        
        `uvm_info("ERROR_PROTOCOL_SEQ", "Starting error recovery phase", UVM_MEDIUM)
        
        // Test system recovery after errors
        for (int i = 0; i < 3; i++) begin
            req = uart_transaction::type_id::create("recovery_req");
            start_item(req);
            
            if (!req.randomize() with {
                req.transaction_type == ERROR_RECOVERY;
                req.enable_recovery_testing == 1'b1;
            }) begin
                `uvm_fatal("ERROR_PROTOCOL_SEQ", "Failed to randomize error recovery transaction")
            end
            
            finish_item(req);
            
            // Recovery timing
            #500ns;
        end
        
        `uvm_info("ERROR_PROTOCOL_SEQ", "Error recovery phase completed", UVM_MEDIUM)
    endtask
    
endclass : uart_axi4_error_protocol_sequence