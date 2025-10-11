`timescale 1ns / 1ps

//================================================================================
// Test Register Write/Read Verification Test
// 
// Purpose: Verify that register write operations actually update register values
//          and that subsequent reads return the written values
// 
// This test addresses the FPGA issue where writes report success but reads
// return fixed pattern values instead of written data
//================================================================================

class uart_axi4_register_verification_test extends enhanced_uart_axi4_base_test;
    
    `uvm_component_utils(uart_axi4_register_verification_test)
    
    function new(string name = "uart_axi4_register_verification_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        uart_axi4_register_verification_sequence reg_verify_seq;
        
        phase.raise_objection(this);
        
        `uvm_info("TEST", "=== Starting Register Write/Read Verification Test ===", UVM_LOW)
        
        // Create and start the register verification sequence
        reg_verify_seq = uart_axi4_register_verification_sequence::type_id::create("reg_verify_seq");
        reg_verify_seq.start(m_env.m_agent.m_sequencer);
        
        `uvm_info("TEST", "=== Register Write/Read Verification Test Complete ===", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass

//================================================================================
// Register Verification Sequence
//================================================================================

class uart_axi4_register_verification_sequence extends uvm_sequence #(uart_frame_transaction);
    
    `uvm_object_utils(uart_axi4_register_verification_sequence)
    
    function new(string name = "uart_axi4_register_verification_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction write_req, read_req;
        
        // Test data for each register
        logic [31:0] test_addresses[4];
        logic [31:0] test_values[4];
        string reg_names[4];
        int pass_count;
        
        // Initialize arrays
        test_addresses[0] = 32'h00001020; test_addresses[1] = 32'h00001024; 
        test_addresses[2] = 32'h00001028; test_addresses[3] = 32'h0000102C;
        
        test_values[0] = 32'hA5A5A5A5; test_values[1] = 32'h5A5A5A5A;
        test_values[2] = 32'h12345678; test_values[3] = 32'h87654321;
        
        reg_names[0] = "REG_TEST_0"; reg_names[1] = "REG_TEST_1";
        reg_names[2] = "REG_TEST_2"; reg_names[3] = "REG_TEST_3";
        
        `uvm_info("SEQ", "Starting register verification sequence", UVM_MEDIUM)
        
        // Phase 1: Read initial values
        `uvm_info("SEQ", "=== Phase 1: Reading initial register values ===", UVM_LOW)
        for (int i = 0; i < 4; i++) begin
            read_req = uart_frame_transaction::type_id::create($sformatf("read_initial_%s", reg_names[i]));
            start_item(read_req);
            
            // Configure read transaction
            read_req.is_write = 0;       // READ operation
            read_req.addr = test_addresses[i];
            read_req.length = 0;         // length=0 means 1 beat
            read_req.size = 2'b10;       // 32-bit transfer
            read_req.auto_increment = 0;
            
            finish_item(read_req);
            
            `uvm_info("SEQ", $sformatf("%s initial value: 0x%08X", reg_names[i], 
                {read_req.response_data[3], read_req.response_data[2], read_req.response_data[1], read_req.response_data[0]}), UVM_LOW)
        end
        
        // Phase 2: Write test values
        `uvm_info("SEQ", "=== Phase 2: Writing test values to registers ===", UVM_LOW)
        for (int i = 0; i < 4; i++) begin
            write_req = uart_frame_transaction::type_id::create($sformatf("write_%s", reg_names[i]));
            start_item(write_req);
            
            // Configure write transaction  
            write_req.is_write = 1;      // WRITE operation
            write_req.addr = test_addresses[i];
            write_req.data = new[4];
            write_req.data[0] = test_values[i][7:0];
            write_req.data[1] = test_values[i][15:8];
            write_req.data[2] = test_values[i][23:16];
            write_req.data[3] = test_values[i][31:24];
            write_req.length = 0;        // length=0 means 1 beat
            write_req.size = 2'b10;      // 32-bit transfer
            write_req.auto_increment = 0;
            
            finish_item(write_req);
            
            if (write_req.response_status == 8'h00) begin
                `uvm_info("SEQ", $sformatf("Write to %s (0x%08X) = 0x%08X SUCCESS", 
                    reg_names[i], test_addresses[i], test_values[i]), UVM_LOW)
            end else begin
                `uvm_error("SEQ", $sformatf("Write to %s (0x%08X) FAILED with status 0x%02X", 
                    reg_names[i], test_addresses[i], write_req.response_status))
            end
        end
        
        // Phase 3: Read back and verify
        `uvm_info("SEQ", "=== Phase 3: Reading back and verifying written values ===", UVM_LOW)
        pass_count = 0;
        
        for (int i = 0; i < 4; i++) begin
            read_req = uart_frame_transaction::type_id::create($sformatf("read_verify_%s", reg_names[i]));
            start_item(read_req);
            
            // Configure read transaction
            read_req.is_write = 0;       // READ operation
            read_req.addr = test_addresses[i];
            read_req.length = 0;         // length=0 means 1 beat
            read_req.size = 2'b10;       // 32-bit transfer
            read_req.auto_increment = 0;
            
            finish_item(read_req);
            
            // Reconstruct 32-bit value from response data
            logic [31:0] read_value = {read_req.response_data[3], read_req.response_data[2], 
                                      read_req.response_data[1], read_req.response_data[0]};
            
            // Verify the read value matches the written value
            if (read_value == test_values[i]) begin
                `uvm_info("SEQ", $sformatf("Register %s verification PASS: wrote 0x%08X, read 0x%08X", 
                    reg_names[i], test_values[i], read_value), UVM_LOW)
                pass_count++;
            end else begin
                `uvm_error("SEQ", $sformatf("Register %s verification FAIL: wrote 0x%08X, read 0x%08X", 
                    reg_names[i], test_values[i], read_value))
            end
        end
        
        // Phase 4: Multiple write/read cycles
        `uvm_info("SEQ", "=== Phase 4: Multiple write/read cycles for one register ===", UVM_LOW)
        
        begin
            logic [31:0] cycle_values[5];
            logic [31:0] target_addr;
            
            cycle_values[0] = 32'hDEADBEEF; cycle_values[1] = 32'hCAFEBABE; 
            cycle_values[2] = 32'h12345678; cycle_values[3] = 32'h87654321;
            cycle_values[4] = 32'hFFFFFFFF;
            
            target_addr = 32'h00001020;  // Use first test register
            
            for (int cycle = 0; cycle < 5; cycle++) begin
                // Write value
                write_req = uart_frame_transaction::type_id::create($sformatf("write_cycle_%0d", cycle));
                start_item(write_req);
                
                write_req.is_write = 1;
                write_req.addr = target_addr;
                write_req.data = new[4];
                write_req.data[0] = cycle_values[cycle][7:0];
                write_req.data[1] = cycle_values[cycle][15:8];
                write_req.data[2] = cycle_values[cycle][23:16];
                write_req.data[3] = cycle_values[cycle][31:24];
                write_req.length = 0;
                write_req.size = 2'b10;
                write_req.auto_increment = 0;
                
                finish_item(write_req);
                
                // Read back immediately  
                read_req = uart_frame_transaction::type_id::create($sformatf("read_cycle_%0d", cycle));
                start_item(read_req);
                
                read_req.is_write = 0;
                read_req.addr = target_addr;
                read_req.length = 0;
                read_req.size = 2'b10;
                read_req.auto_increment = 0;
                
                finish_item(read_req);
                
                // Check result
                logic [31:0] read_cycle_value = {read_req.response_data[3], read_req.response_data[2], 
                                               read_req.response_data[1], read_req.response_data[0]};
                
                if (read_cycle_value == cycle_values[cycle]) begin
                    `uvm_info("SEQ", $sformatf("Cycle %0d: PASS - wrote/read 0x%08X", 
                        cycle, cycle_values[cycle]), UVM_LOW)
                end else begin
                    `uvm_error("SEQ", $sformatf("Cycle %0d: FAIL - wrote 0x%08X, read 0x%08X", 
                        cycle, cycle_values[cycle], read_cycle_value))
                end
            end
        end
        
        // Final summary
        `uvm_info("SEQ", $sformatf("=== TEST SUMMARY: %0d/4 registers passed basic verification ===", pass_count), UVM_LOW)
        
        if (pass_count == 4) begin
            `uvm_info("SEQ", "笨・ALL REGISTER TESTS PASSED - RTL register functionality is correct", UVM_LOW)
        end else begin
            `uvm_error("SEQ", $sformatf("笨・REGISTER TESTS FAILED - %0d registers failed verification", (4-pass_count)))
        end
        
    endtask
    
endclass
