// Error Injection Test Sequence
// Target Board: Zybo Z7-20
// Date: July 26, 2025
// Description: Error handling and recovery test

`ifndef ERROR_INJECTION_SEQUENCE_SV
`define ERROR_INJECTION_SEQUENCE_SV

class error_injection_sequence extends axi4_lite_base_sequence;
    
    // UVM registration
    `uvm_object_utils(error_injection_sequence)
    
    // Constructor
    function new(string name = "error_injection_sequence");
        super.new(name);
    endfunction
    
    // Main sequence body
    virtual task body();
        `uvm_info("ERROR_INJ", "Starting error injection test", UVM_LOW)
        
        // Step 1: Initialize system
        setup_error_test();
        
        // Step 2: Test invalid register access
        test_invalid_register_access();
        
        // Step 3: Test FIFO overflow conditions
        test_fifo_overflow();
        
        // Step 4: Test FIFO underflow conditions  
        test_fifo_underflow();
        
        // Step 5: Test invalid write strobes
        test_invalid_write_strobes();
        
        // Step 6: Test concurrent access scenarios
        test_concurrent_access();
        
        // Step 7: Verify error recovery
        test_error_recovery();
        
        `uvm_info("ERROR_INJ", "Error injection test completed", UVM_LOW)
    endtask
    
    // Setup for error testing
    task setup_error_test();
        `uvm_info("ERROR_INJ", "Setting up error test environment", UVM_MEDIUM)
        
        // Enable UART
        write_register(ADDR_CONTROL_REG, 32'h00000001);
        
        // Clear existing errors
        write_register(ADDR_ERROR_STATUS, 32'hFFFFFFFF);
        
        // Set low FIFO thresholds to trigger conditions easily
        write_register(ADDR_FIFO_THRESH, 32'h00020002);
        
        #100ns;
    endtask
    
    // Test invalid register addresses
    task test_invalid_register_access();
        bit [31:0] rdata;
        bit [1:0] resp;
        bit [31:0] invalid_addresses[] = {
            32'h00000020, // Beyond valid range
            32'h00000024,
            32'h00000100,
            32'hFFFFFFFF
        };
        
        `uvm_info("ERROR_INJ", "Testing invalid register access", UVM_MEDIUM)
        
        foreach (invalid_addresses[i]) begin
            // Test read to invalid address
            read_register(invalid_addresses[i], rdata, resp);
            if (resp == AXI_RESP_SLVERR || resp == AXI_RESP_DECERR) begin
                `uvm_info("ERROR_INJ", $sformatf("Invalid read addr 0x%08h correctly returned error response: %b", 
                         invalid_addresses[i], resp), UVM_MEDIUM)
            end else begin
                `uvm_warning("ERROR_INJ", $sformatf("Invalid read addr 0x%08h should have returned error", 
                            invalid_addresses[i]))
            end
            
            // Test write to invalid address
            write_register(invalid_addresses[i], 32'hDEADBEEF);
            
            #100ns;
        end
    endtask
    
    // Test FIFO overflow conditions
    task test_fifo_overflow();
        bit [31:0] status;
        bit [1:0] resp;
        
        `uvm_info("ERROR_INJ", "Testing FIFO overflow conditions", UVM_MEDIUM)
        
        // Fill TX FIFO beyond capacity
        for (int i = 0; i < 70; i++) begin  // Exceed 64-entry FIFO
            write_register(ADDR_TX_DATA_REG, 32'h00000040 + (i % 26)); // 'A' to 'Z'
            
            // Check for overflow after filling
            if (i > 60) begin
                read_register(ADDR_ERROR_STATUS, status, resp);
                if (resp == AXI_RESP_OKAY && status[4] == 1'b1) begin // TX overflow bit
                    `uvm_info("ERROR_INJ", $sformatf("TX FIFO overflow detected at entry %0d", i), UVM_MEDIUM)
                    break;
                end
            end
            #10ns;
        end
        
        // Verify overflow error is set
        read_register(ADDR_ERROR_STATUS, status, resp);
        if (resp == AXI_RESP_OKAY) begin
            `uvm_info("ERROR_INJ", $sformatf("Error status after overflow test: 0x%08h", status), UVM_MEDIUM)
        end
    endtask
    
    // Test FIFO underflow conditions
    task test_fifo_underflow();
        bit [31:0] rdata, status;
        bit [1:0] resp;
        
        `uvm_info("ERROR_INJ", "Testing FIFO underflow conditions", UVM_MEDIUM)
        
        // Ensure RX FIFO is empty
        read_register(ADDR_FIFO_STATUS, status, resp);
        if (resp == AXI_RESP_OKAY && status[0] == 1'b1) begin // RX FIFO empty
            // Try to read from empty FIFO multiple times
            for (int i = 0; i < 5; i++) begin
                read_register(ADDR_RX_DATA_REG, rdata, resp);
                `uvm_info("ERROR_INJ", $sformatf("Read %0d from empty RX FIFO: data=0x%08h, resp=%b", 
                         i, rdata, resp), UVM_MEDIUM)
                #50ns;
            end
            
            // Check for underflow error
            read_register(ADDR_ERROR_STATUS, status, resp);
            if (resp == AXI_RESP_OKAY) begin
                `uvm_info("ERROR_INJ", $sformatf("Error status after underflow test: 0x%08h", status), UVM_MEDIUM)
            end
        end
    endtask
    
    // Test invalid write strobes
    task test_invalid_write_strobes();
        bit [3:0] invalid_strobes[] = {
            4'b0000,  // No strobes
            4'b0101,  // Non-contiguous
            4'b1010,  // Non-contiguous
            4'b1101   // Non-contiguous
        };
        
        `uvm_info("ERROR_INJ", "Testing invalid write strobes", UVM_MEDIUM)
        
        foreach (invalid_strobes[i]) begin
            // Create transaction with invalid strobe
            begin
                axi4_lite_transaction tr = axi4_lite_transaction::type_id::create("invalid_strb_tr");
                
                if (!tr.randomize() with {
                    trans_type == axi4_lite_transaction::WRITE;
                    addr == ADDR_CONTROL_REG;
                    data == 32'h12345678;
                    strb == invalid_strobes[i];
                }) begin
                    `uvm_error("ERROR_INJ", "Failed to create invalid strobe transaction")
                end
                
                start_item(tr);
                finish_item(tr);
                
                `uvm_info("ERROR_INJ", $sformatf("Tested invalid strobe pattern: %b, response: %b", 
                         invalid_strobes[i], tr.resp), UVM_MEDIUM)
            end
            
            #100ns;
        end
    endtask
    
    // Test concurrent access scenarios
    task test_concurrent_access();
        `uvm_info("ERROR_INJ", "Testing concurrent access scenarios", UVM_MEDIUM)
        
        // Simulate rapid read/write to same register
        fork
            begin
                for (int i = 0; i < 10; i++) begin
                    write_register(ADDR_CONTROL_REG, 32'h00000001 | (i << 4));
                    #20ns;
                end
            end
            begin
                bit [31:0] rdata;
                bit [1:0] resp;
                for (int i = 0; i < 10; i++) begin
                    read_register(ADDR_CONTROL_REG, rdata, resp);
                    #25ns;
                end
            end
        join
        
        // Test alternating TX/RX access
        fork
            begin
                for (int i = 0; i < 5; i++) begin
                    write_register(ADDR_TX_DATA_REG, 32'h00000050 + i);
                    #30ns;
                end
            end
            begin
                bit [31:0] rdata;
                bit [1:0] resp;
                for (int i = 0; i < 5; i++) begin
                    read_register(ADDR_RX_DATA_REG, rdata, resp);
                    #35ns;
                end
            end
        join
        
        #200ns;
    endtask
    
    // Test error recovery mechanisms
    task test_error_recovery();
        bit [31:0] status, rdata;
        bit [1:0] resp;
        
        `uvm_info("ERROR_INJ", "Testing error recovery", UVM_MEDIUM)
        
        // Read current error status
        read_register(ADDR_ERROR_STATUS, status, resp);
        `uvm_info("ERROR_INJ", $sformatf("Current error status: 0x%08h", status), UVM_MEDIUM)
        
        if (status != 32'h00000000) begin
            // Clear all errors
            write_register(ADDR_ERROR_STATUS, status); // Write-1-to-clear
            
            // Verify errors are cleared
            read_register(ADDR_ERROR_STATUS, rdata, resp);
            if (resp == AXI_RESP_OKAY && rdata == 32'h00000000) begin
                `uvm_info("ERROR_INJ", "Error recovery successful - all errors cleared", UVM_MEDIUM)
            end else begin
                `uvm_warning("ERROR_INJ", $sformatf("Error recovery incomplete: remaining errors = 0x%08h", rdata))
            end
        end
        
        // Test system functionality after error recovery
        write_register(ADDR_TX_DATA_REG, 32'h00000052); // Send 'R' for Recovery
        
        read_register(ADDR_FIFO_STATUS, status, resp);
        `uvm_info("ERROR_INJ", $sformatf("Post-recovery FIFO status: 0x%08h", status), UVM_MEDIUM)
    endtask

endclass

`endif // ERROR_INJECTION_SEQUENCE_SV
