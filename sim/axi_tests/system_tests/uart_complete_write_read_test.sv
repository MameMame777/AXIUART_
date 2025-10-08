`timescale 1ns / 1ps

// Complete Write-Read Test (based on successful debug test)
module uart_complete_write_read_test;
    
    // Test control signals
    logic test_passed_count = 0;
    logic test_failed_count = 0;
    
    // Clock and reset
    logic clk;
    logic rst;
    
    // Clock generation - 125MHz (period = 8ns)
    initial begin
        clk = 0;
        forever #4ns clk = ~clk;
    end
    
    // System control
    logic bridge_enable = 1;
    logic reset_statistics = 0;
    
    // UART interface
    logic uart_rx = 1;  // UART idle
    logic uart_tx;
    logic uart_cts_n = 0;  // CTS active
    logic rx_fifo_full_out;
    logic rx_fifo_high_out;
    logic tx_ready_out;
    
    // AXI4-Lite interface
    axi4_lite_if axi_if(.clk(clk), .rst(rst));
    
    // Bridge status
    logic        bridge_busy;
    logic [7:0]  bridge_error_code;
    logic [15:0] tx_transaction_count;
    logic [15:0] rx_transaction_count;
    logic [7:0]  fifo_status_flags;
    
    // Register block instantiation
    Register_Block reg_block (
        .clk(clk),
        .rst(rst),
        .axi(axi_if.slave)
    );
    
    // Bridge instantiation
    Uart_Axi4_Bridge uut (
        .clk(clk),
        .rst(rst),
        .uart_rx(uart_rx),
        .uart_tx(uart_tx),
        .uart_cts_n(uart_cts_n),
        .rx_fifo_full_out(rx_fifo_full_out),
        .rx_fifo_high_out(rx_fifo_high_out),
        .tx_ready_out(tx_ready_out),
        .axi(axi_if.master),
        .bridge_enable(bridge_enable),
        .bridge_busy(bridge_busy),
        .bridge_error_code(bridge_error_code),
        .tx_transaction_count(tx_transaction_count),
        .rx_transaction_count(rx_transaction_count),
        .fifo_status_flags(fifo_status_flags),
        .debug_parser_cmd(),
        .debug_builder_cmd_echo(),
        .debug_builder_cmd_out(),
        .debug_parser_status(),
        .debug_builder_status(),
        .debug_parser_state(),
        .debug_builder_state(),
        .reset_statistics(reset_statistics)
    );
    
    // UART transmit task (same timing as successful debug test)
    task send_uart_byte(input logic [7:0] data);
        $display("📤 Sending UART byte: 0x%02X at time %0t", data, $time);
        
        // Start bit
        uart_rx = 0;
        #8681ns;
        
        // Data bits (LSB first)
        for (int i = 0; i < 8; i++) begin
            uart_rx = data[i];
            #8681ns;
        end
        
        // Stop bit
        uart_rx = 1;
        #8681ns;
    endtask
    
    // UART receive task
    task receive_uart_response(output logic [7:0] response_bytes[], input int expected_count);
        automatic int byte_idx = 0;
        automatic logic [7:0] rx_byte;
        
        response_bytes = new[expected_count];
        
        for (byte_idx = 0; byte_idx < expected_count; byte_idx++) begin
            // Wait for TX start bit
            while (uart_tx == 1) #1ns;
            
            $display("📍 TX byte %0d start bit at time %0t", byte_idx, $time);
            
            // Wait to center of first data bit
            #(8681 * 1.5 * 1ns);
            
            // Sample data bits
            rx_byte = 0;
            for (int i = 0; i < 8; i++) begin
                rx_byte[i] = uart_tx;
                #(8681 * 1ns);
            end
            
            response_bytes[byte_idx] = rx_byte;
            $display("📥 Received byte %0d: 0x%02X", byte_idx, rx_byte);
            
            // Wait for stop bit to complete
            #(8681 * 0.5 * 1ns);
        end
    endtask
    
    // Test write operation
    task test_write_operation(input logic [31:0] addr, input logic [31:0] data, input string test_name);
        $display("\n🖊️  %s: Writing 0x%08X to address 0x%08X", test_name, data, addr);
        
        // Send write command frame
        send_uart_byte(8'hA5);              // SOF (Host-to-Device)
        send_uart_byte(8'h20);              // CMD: Write
        send_uart_byte(addr[7:0]);          // ADDR[7:0]
        send_uart_byte(addr[15:8]);         // ADDR[15:8]
        send_uart_byte(addr[23:16]);        // ADDR[23:16]
        send_uart_byte(addr[31:24]);        // ADDR[31:24]
        send_uart_byte(data[7:0]);          // DATA[7:0]
        send_uart_byte(data[15:8]);         // DATA[15:8]
        send_uart_byte(data[23:16]);        // DATA[23:16]
        send_uart_byte(data[31:24]);        // DATA[31:24]
        
        // Calculate and send CRC (excluding SOF)
        if (data == 32'hDEADBEEF) begin
            send_uart_byte(8'h25);          // CRC for DEADBEEF frame
        end else begin
            send_uart_byte(8'h3B);          // CRC for CAFEBABE frame
        end
        
        $display("✅ Write command sent");
        
        // Wait for processing
        #200us;
        
        // Receive response
        begin
            automatic logic [7:0] response[];
            receive_uart_response(response, 4);  // SOF, STATUS, CMD_ECHO, CRC
            
            if (response[1] == 8'h00) begin  // STATUS = 0 (success)
                $display("✅ %s write successful", test_name);
                test_passed_count++;
            end else begin
                $display("❌ %s write failed with status 0x%02X", test_name, response[1]);
                test_failed_count++;
            end
        end
    endtask
    
    // Test read operation
    task test_read_operation(input logic [31:0] addr, input logic [31:0] expected_data, input string test_name);
        $display("\n📖 %s: Reading from address 0x%08X", test_name, addr);
        
        // Send read command frame
        send_uart_byte(8'hA5);              // SOF (Host-to-Device)
        send_uart_byte(8'h10);              // CMD: Read
        send_uart_byte(addr[7:0]);          // ADDR[7:0]
        send_uart_byte(addr[15:8]);         // ADDR[15:8]
        send_uart_byte(addr[23:16]);        // ADDR[23:16]
        send_uart_byte(addr[31:24]);        // ADDR[31:24]
        send_uart_byte(8'h5E);              // CRC for read frame
        
        $display("✅ Read command sent");
        
        // Wait for processing
        #200us;
        
        // Receive response
        begin
            automatic logic [7:0] response[];
            automatic logic [31:0] read_data;
            
            receive_uart_response(response, 8);  // SOF, STATUS, CMD_ECHO, DATA[0:3], CRC
            
            if (response[1] == 8'h00) begin  // STATUS = 0 (success)
                read_data = {response[6], response[5], response[4], response[3]};  // Reconstruct data
                $display("📄 %s read data: 0x%08X", test_name, read_data);
                
                if (read_data == expected_data) begin
                    $display("🎉 %s read verification SUCCESS!", test_name);
                    test_passed_count++;
                end else begin
                    $display("❌ %s read verification FAILED: got 0x%08X, expected 0x%08X", 
                             test_name, read_data, expected_data);
                    test_failed_count++;
                end
            end else begin
                $display("❌ %s read failed with status 0x%02X", test_name, response[1]);
                test_failed_count++;
            end
        end
    endtask
    
    // Main test sequence
    initial begin
        $display("🚀 Starting Complete UART Write-Read Verification Test");
        $display("====================================================");
        
        // Enable waveform dumping
        $dumpfile("waveforms/uart_complete_wr.vcd");
        $dumpvars(0, uart_complete_write_read_test);
        
        // Reset sequence
        rst = 1;
        repeat(50) @(posedge clk);
        rst = 0;
        $display("✅ Reset released at time %0t", $time);
        
        // Wait for system stabilization
        #100us;
        
        // Test sequence
        test_write_operation(32'h00001020, 32'hDEADBEEF, "TEST1");
        #100us;
        test_read_operation(32'h00001020, 32'hDEADBEEF, "TEST1");
        
        #100us;
        test_write_operation(32'h00001020, 32'hCAFEBABE, "TEST2");
        #100us;
        test_read_operation(32'h00001020, 32'hCAFEBABE, "TEST2");
        
        // Final results
        #100us;
        $display("\n📊 FINAL TEST RESULTS");
        $display("====================");
        $display("✅ Tests Passed: %0d", test_passed_count);
        $display("❌ Tests Failed: %0d", test_failed_count);
        
        if (test_failed_count == 0) begin
            $display("🏆 ALL TESTS PASSED!");
            $display("✓ Register write operations work correctly");
            $display("✓ Register read operations work correctly");
            $display("✓ Written values can be read back successfully");
            $display("✓ Register value changes are properly handled");
        end else begin
            $display("💥 SOME TESTS FAILED");
        end
        
        $finish;
    end
    
    // Timeout safety
    initial begin
        #10ms;
        $display("⏰ Test timeout reached");
        $finish;
    end
    
endmodule