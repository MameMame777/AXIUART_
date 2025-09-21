`timescale 1ns / 1ps

// Frame_Builder Diagnostic Sequence for UART-AXI4 Bridge Testing
class uart_axi4_frame_builder_sequence extends uvm_sequence #(uart_frame_transaction);
    
    `uvm_object_utils(uart_axi4_frame_builder_sequence)
    
    function new(string name = "uart_axi4_frame_builder_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction req;
        
        `uvm_info("FB_SEQ", "=== Frame_Builder Diagnostic Sequence Started ===", UVM_LOW)
        
        // Test 1: Read Response Frame Generation
        `uvm_info("FB_SEQ", "Test 1: Read Response Frame Generation", UVM_LOW)
        `uvm_do_with(req, {
            cmd == 8'ha1;  // Read command response
            addr == 32'h12345678;
            data.size() == 4;
            data[0] == 8'hde;
            data[1] == 8'had;
            data[2] == 8'hbe;
            data[3] == 8'hef;
        })
        
        #100ns; // Wait for response processing
        
        // Test 2: Write Response Frame Generation
        `uvm_info("FB_SEQ", "Test 2: Write Response Frame Generation", UVM_LOW)
        `uvm_do_with(req, {
            cmd == 8'ha2;  // Write command response
            addr == 32'h87654321;
            data.size() == 0;  // Write responses have no data
        })
        
        #100ns; // Wait for response processing
        
        // Test 3: Error Response Frame Generation
        `uvm_info("FB_SEQ", "Test 3: Error Response Frame Generation", UVM_LOW)
        `uvm_do_with(req, {
            cmd == 8'hae;  // Error response
            addr == 32'h00000000;
            data.size() == 1;
            data[0] == 8'h01;  // Error code
        })
        
        #100ns; // Wait for response processing
        
        // Test 4: Multiple Sequential Responses
        `uvm_info("FB_SEQ", "Test 4: Multiple Sequential Responses", UVM_LOW)
        for (int i = 0; i < 3; i++) begin
            `uvm_do_with(req, {
                cmd == 8'ha1;  // Read responses
                addr == (32'h1000 + i * 4);
                data.size() == 4;
                data[0] == (8'h10 + i);
                data[1] == (8'h20 + i);
                data[2] == (8'h30 + i);
                data[3] == (8'h40 + i);
            })
            #50ns; // Short delay between responses
        end
        
        // Test 5: Stress Test - Rapid Response Generation
        `uvm_info("FB_SEQ", "Test 5: Rapid Response Generation", UVM_LOW)
        for (int i = 0; i < 5; i++) begin
            `uvm_do_with(req, {
                cmd inside {8'ha1, 8'ha2};  // Mix of read/write responses
                addr == (32'h2000 + i * 8);
                if (cmd == 8'ha1) {  // Read response
                    data.size() == 4;
                    data[0] == (8'haa + i);
                    data[1] == (8'hbb + i);
                    data[2] == (8'hcc + i);
                    data[3] == (8'hdd + i);
                } else {  // Write response
                    data.size() == 0;
                }
            })
            #25ns; // Minimal delay for stress testing
        end
        
        `uvm_info("FB_SEQ", "=== Frame_Builder Diagnostic Sequence Completed ===", UVM_LOW)
    endtask
    
endclass