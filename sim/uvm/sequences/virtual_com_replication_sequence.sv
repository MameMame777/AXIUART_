`timescale 1ns / 1ps

//==============================================================================
// Virtual COM Port Replication Sequence
// 
// Purpose: Replicate the exact test patterns that achieved 100% success
//          in the virtual COM port verification (rx_tx_verification.py)
//
// Author: UVM Verification Team
// Date: 2025-10-09
// Version: 1.0
//==============================================================================

class virtual_com_replication_sequence extends uvm_sequence #(uart_frame_transaction);
    `uvm_object_utils(virtual_com_replication_sequence)
    
    // Test patterns from successful virtual COM verification
    typedef struct {
        string name;
        bit [7:0] frame_data[$];
        bit [7:0] expected_response[$];
        string description;
    } test_pattern_t;
    
    test_pattern_t test_patterns[$];
    
    function new(string name = "virtual_com_replication_sequence");
        super.new(name);
        create_test_patterns();
    endfunction
    
    function void create_test_patterns();
        test_pattern_t pattern;
        
        // Test Pattern 1: Basic Register Write (0x1020 <- 0x42)
        // Frame: A5 00 20 10 00 00 42 CA (from successful virtual verification)
        pattern.name = "basic_register_write";
        pattern.description = "Write 0x42 to register 0x1020";
        pattern.frame_data = '{8'hA5, 8'h00, 8'h20, 8'h10, 8'h00, 8'h00, 8'h42, 8'hCA};
        pattern.expected_response = '{8'h5A, 8'h00, 8'h20, 8'hE0}; // OK response
        test_patterns.push_back(pattern);
        
        // Test Pattern 2: Register Read (0x1020)
        // Frame: A5 80 20 10 00 00 FB (from successful virtual verification)
        pattern.name = "basic_register_read";
        pattern.description = "Read from register 0x1020";
        pattern.frame_data = '{8'hA5, 8'h80, 8'h20, 8'h10, 8'h00, 8'h00, 8'hFB};
        pattern.expected_response = '{8'h5A, 8'h80, 8'h42}; // Simplified read response
        test_patterns.push_back(pattern);
        
        // Test Pattern 3: Test Register Write (0x1020 <- 0xDEADBEEF)
        // 32-bit write to test register  
        pattern.name = "test_register_32bit_write";
        pattern.description = "Write 32-bit value to test register";
        pattern.frame_data = '{8'hA5, 8'h02, 8'h20, 8'h10, 8'h00, 8'h00, 8'hEF, 8'hBE, 8'hAD, 8'hDE, 8'h78}; // 32-bit write with CRC
        pattern.expected_response = '{8'h5A, 8'h02, 8'h20}; // Simplified OK response
        test_patterns.push_back(pattern);
        
        // Test Pattern 4: Error Case - Invalid CRC
        pattern.name = "invalid_crc_test";
        pattern.description = "Frame with corrupted CRC";
        pattern.frame_data = '{8'hA5, 8'h00, 8'h20, 8'h10, 8'h00, 8'h00, 8'h42, 8'h00}; // Wrong CRC
        pattern.expected_response = '{8'h5A, 8'h04}; // CRC error response (shortened)
        test_patterns.push_back(pattern);
        
        `uvm_info("VCOM_SEQ", $sformatf("Created %0d test patterns from successful virtual COM verification", 
                 test_patterns.size()), UVM_MEDIUM)
    endfunction
    
    virtual task body();
        uart_frame_transaction req;
        int pattern_num = 0;
        
        `uvm_info("VCOM_SEQ", "=== Starting Virtual COM Port Replication Sequence ===", UVM_LOW)
        `uvm_info("VCOM_SEQ", "Executing exact test patterns that achieved 100% success", UVM_LOW)
        
        foreach (test_patterns[i]) begin
            pattern_num++;
            
            `uvm_info("VCOM_SEQ", $sformatf("Pattern %0d/%0d: %s", 
                     pattern_num, test_patterns.size(), test_patterns[i].name), UVM_MEDIUM)
            `uvm_info("VCOM_SEQ", $sformatf("Description: %s", test_patterns[i].description), UVM_MEDIUM)
            
            // Create transaction with exact frame from successful verification
            req = uart_frame_transaction::type_id::create("req");
            start_item(req);
            
            // Configure transaction with successful pattern
            req.frame_data = new[test_patterns[i].frame_data.size()];
            for (int j = 0; j < test_patterns[i].frame_data.size(); j++) begin
                req.frame_data[j] = test_patterns[i].frame_data[j];
            end
            
            // Set transaction properties
            req.sof = test_patterns[i].frame_data[0];
            req.cmd = test_patterns[i].frame_data[1];
            req.addr = {test_patterns[i].frame_data[5], test_patterns[i].frame_data[4], 
                       test_patterns[i].frame_data[3], test_patterns[i].frame_data[2]};
            
            // Extract data bytes (variable length depending on command)
            case (req.cmd & 8'h0F) // Extract size field
                2'h0: begin // 8-bit
                    req.data = new[1];
                    req.data[0] = test_patterns[i].frame_data[6];
                end
                2'h1: begin // 16-bit
                    req.data = new[2];
                    req.data[0] = test_patterns[i].frame_data[6];
                    req.data[1] = test_patterns[i].frame_data[7];
                end
                2'h2: begin // 32-bit
                    req.data = new[4];
                    req.data[0] = test_patterns[i].frame_data[6];
                    req.data[1] = test_patterns[i].frame_data[7];
                    req.data[2] = test_patterns[i].frame_data[8];
                    req.data[3] = test_patterns[i].frame_data[9];
                end
                default: begin
                    req.data = new[0]; // Read operation or no data
                end
            endcase
            
            // Set response expectation
            req.expect_error = (test_patterns[i].name == "invalid_crc_test") ? 1 : 0;
            
            // Set error injection for CRC test
            if (test_patterns[i].name == "invalid_crc_test") begin
                req.force_crc_error = 1;
            end else begin
                req.force_crc_error = 0;
            end
            
            // Send transaction
            finish_item(req);
            
            `uvm_info("VCOM_SEQ", $sformatf("Pattern %s completed", test_patterns[i].name), UVM_MEDIUM)
            
            // Small delay between patterns
            #(10us);
        end
        
        `uvm_info("VCOM_SEQ", $sformatf("=== Virtual COM Replication Complete: %0d patterns executed ===", 
                 pattern_num), UVM_LOW)
    endtask
    
endclass : virtual_com_replication_sequence