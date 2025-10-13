`timescale 1ns / 1ps

// UART AXI4 Bridge Control Sequence
// Created: October 13, 2025
// Purpose: Bridge enable/disable and control register verification sequence
// Compliant with Phase 4.1.3 specifications

class uart_axi4_bridge_control_sequence extends uart_base_sequence;
    
    `uvm_object_utils(uart_axi4_bridge_control_sequence)
    
    // Sequence configuration
    int num_bridge_operations = 15;
    bit enable_bridge_toggle = 1'b1;
    bit enable_control_reg_test = 1'b1;
    bit enable_status_monitoring = 1'b1;
    
    function new(string name = "uart_axi4_bridge_control_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_transaction req;
        bit [31:0] control_registers[$];
        bit [31:0] expected_status[$];
        
        `uvm_info("BRIDGE_CONTROL_SEQ", "Starting AXI4 bridge control sequence", UVM_MEDIUM)
        
        // Initialize bridge control test vectors
        prepare_bridge_control_vectors(control_registers, expected_status);
        
        // Execute bridge control operations
        for (int i = 0; i < num_bridge_operations; i++) begin
            `uvm_info("BRIDGE_CONTROL_SEQ", $sformatf("Bridge operation %0d/%0d", i+1, num_bridge_operations), UVM_HIGH)
            
            // Test bridge enable/disable functionality
            if (enable_bridge_toggle) begin
                execute_bridge_toggle_test(i);
            end
            
            // Test control register access
            if (enable_control_reg_test && i < control_registers.size()) begin
                execute_control_register_test(control_registers[i], expected_status[i]);
            end
            
            // Monitor bridge status
            if (enable_status_monitoring) begin
                monitor_bridge_status();
            end
            
            // Add delay between operations
            #(100000ns + ($urandom_range(50000, 150000)));
        end
        
        `uvm_info("BRIDGE_CONTROL_SEQ", "Bridge control sequence completed", UVM_MEDIUM)
    endtask
    
    virtual task prepare_bridge_control_vectors(ref bit [31:0] control_regs[$], ref bit [31:0] status_vals[$]);
        `uvm_info("BRIDGE_CONTROL_SEQ", "Preparing bridge control test vectors", UVM_HIGH)
        
        // Bridge enable control register
        control_regs.push_back(32'h0000_0008); // UART_BRIDGE_CTRL register
        status_vals.push_back(32'h0000_0001);  // Expected bridge enabled status
        
        // Bridge disable control register
        control_regs.push_back(32'h0000_0008); // UART_BRIDGE_CTRL register
        status_vals.push_back(32'h0000_0000);  // Expected bridge disabled status
        
        // Bridge configuration registers
        control_regs.push_back(32'h0000_000C); // UART_BRIDGE_CONFIG register
        status_vals.push_back(32'h0000_0003);  // Expected config status
        
        // Bridge interrupt enable
        control_regs.push_back(32'h0000_0010); // UART_BRIDGE_INT_EN register
        status_vals.push_back(32'h0000_0007);  // Expected interrupt status
        
        `uvm_info("BRIDGE_CONTROL_SEQ", $sformatf("Prepared %0d control vectors", control_regs.size()), UVM_HIGH)
    endtask
    
    virtual task execute_bridge_toggle_test(int iteration);
        uart_transaction req;
        bit [31:0] bridge_ctrl_reg = 32'h0000_0008;
        bit [31:0] enable_value = 32'h0000_0001;
        bit [31:0] disable_value = 32'h0000_0000;
        
        `uvm_info("BRIDGE_TOGGLE_TEST", $sformatf("Bridge toggle test iteration %0d", iteration), UVM_HIGH)
        
        // Enable bridge
        req = uart_transaction::type_id::create("bridge_enable_req");
        if (!req.randomize() with {
            address == bridge_ctrl_reg;
            data == enable_value;
            transaction_type == WRITE;
            enable_bridge_awareness == 1'b1;
        }) begin
            `uvm_fatal("BRIDGE_CONTROL_SEQ", "Failed to randomize bridge enable transaction")
        end
        start_item(req);
        finish_item(req);
        
        // Wait for bridge to stabilize
        #500000ns;
        
        // Verify bridge enabled status
        verify_bridge_status(1'b1);
        
        // Disable bridge
        req = uart_transaction::type_id::create("bridge_disable_req");
        if (!req.randomize() with {
            address == bridge_ctrl_reg;
            data == disable_value;
            transaction_type == WRITE;
            enable_bridge_awareness == 1'b1;
        }) begin
            `uvm_fatal("BRIDGE_CONTROL_SEQ", "Failed to randomize bridge disable transaction")
        end
        start_item(req);
        finish_item(req);
        
        // Wait for bridge to stabilize
        #500000ns;
        
        // Verify bridge disabled status
        verify_bridge_status(1'b0);
        
        `uvm_info("BRIDGE_TOGGLE_TEST", "Bridge toggle test completed", UVM_HIGH)
    endtask
    
    virtual task execute_control_register_test(bit [31:0] reg_addr, bit [31:0] expected_val);
        uart_transaction req;
        
        `uvm_info("CONTROL_REG_TEST", $sformatf("Testing control register 0x%08x", reg_addr), UVM_HIGH)
        
        // Write to control register
        req = uart_transaction::type_id::create("control_write_req");
        if (!req.randomize() with {
            address == reg_addr;
            data == expected_val;
            transaction_type == WRITE;
            enable_bridge_awareness == 1'b1;
        }) begin
            `uvm_fatal("BRIDGE_CONTROL_SEQ", "Failed to randomize control register write")
        end
        start_item(req);
        finish_item(req);
        
        // Wait for register update
        #200000ns;
        
        // Read back and verify
        req = uart_transaction::type_id::create("control_read_req");
        if (!req.randomize() with {
            address == reg_addr;
            transaction_type == READ;
            enable_bridge_awareness == 1'b1;
        }) begin
            `uvm_fatal("BRIDGE_CONTROL_SEQ", "Failed to randomize control register read")
        end
        start_item(req);
        finish_item(req);
        
        `uvm_info("CONTROL_REG_TEST", $sformatf("Control register test completed for 0x%08x", reg_addr), UVM_HIGH)
    endtask
    
    virtual task monitor_bridge_status();
        uart_transaction req;
        bit [31:0] status_reg = 32'h0000_0004; // UART_BRIDGE_STATUS register
        
        `uvm_info("BRIDGE_STATUS_MON", "Monitoring bridge status", UVM_HIGH)
        
        // Read bridge status register
        req = uart_transaction::type_id::create("status_read_req");
        if (!req.randomize() with {
            address == status_reg;
            transaction_type == READ;
            enable_bridge_awareness == 1'b1;
        }) begin
            `uvm_fatal("BRIDGE_CONTROL_SEQ", "Failed to randomize status read transaction")
        end
        start_item(req);
        finish_item(req);
        
        `uvm_info("BRIDGE_STATUS_MON", "Bridge status monitoring completed", UVM_HIGH)
    endtask
    
    virtual task verify_bridge_status(bit expected_enabled);
        uart_transaction req;
        bit [31:0] status_reg = 32'h0000_0004; // UART_BRIDGE_STATUS register
        
        `uvm_info("BRIDGE_VERIFY", $sformatf("Verifying bridge status (expected enabled: %0b)", expected_enabled), UVM_HIGH)
        
        // Read bridge status
        req = uart_transaction::type_id::create("verify_status_req");
        if (!req.randomize() with {
            address == status_reg;
            transaction_type == READ;
            enable_bridge_awareness == 1'b1;
        }) begin
            `uvm_fatal("BRIDGE_CONTROL_SEQ", "Failed to randomize status verification transaction")
        end
        start_item(req);
        finish_item(req);
        
        // Note: Actual verification logic would be implemented in the monitor/scoreboard
        `uvm_info("BRIDGE_VERIFY", "Bridge status verification completed", UVM_HIGH)
    endtask
    
endclass : uart_axi4_bridge_control_sequence