`timescale 1ns / 1ps

// UART Write-Read Verification Test
// Tests: 1) Write data to register, 2) Read back same data, 3) Verify match
module uart_write_read_test;
    
    // Clock and reset
    logic clk;
    logic rst;
    
    // Test control
    logic test_complete;
    int test_passed;
    int test_failed;
    
    // Clock generation - 125MHz
    initial begin
        clk = 0;
        forever #4ns clk = ~clk;
    end
    
    // UART signals
    logic uart_rx;
    logic uart_tx;
    logic uart_cts_n;
    logic rx_fifo_full_out;
    logic rx_fifo_high_out;
    logic tx_ready_out;
    
    // AXI4-Lite interface
    axi4_lite_if axi_if(.clk(clk), .rst(rst));
    
    // Register block for testing
    Register_Block reg_block (
        .clk(clk),
        .rst(rst),
        .axi(axi_if.slave)
    );
    
    // Bridge control and status
    logic        bridge_enable = 1'b1;
    logic        bridge_busy;
    logic [7:0]  bridge_error_code;
    logic [15:0] tx_transaction_count;
    logic [15:0] rx_transaction_count;
    logic [7:0]  fifo_status_flags;
    
    // Instantiate DUT
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
        .reset_statistics(1'b0)
    );
    
    // UART timing parameters
    localparam int UART_BIT_TIME = 8681; // ns per bit for 115200 baud
    
    // UART Transmitter task
    task send_uart_byte(input logic [7:0] data);
        $display("📤 Sending UART byte: 0x%02X at time %0t", data, $time);
        
        // Start bit
        uart_rx = 0;
        #(UART_BIT_TIME * 1ns);
        
        // Data bits (LSB first)
        for (int i = 0; i < 8; i++) begin
            uart_rx = data[i];
            #(UART_BIT_TIME * 1ns);
        end
        
        // Stop bit
        uart_rx = 1;
        #(UART_BIT_TIME * 1ns);
    endtask
    
    // UART Receiver task with improved timing
    task receive_uart_byte(output logic [7:0] data, input int timeout_cycles);
        automatic int timeout_count = 0;
        automatic logic [7:0] received_byte = 0;
        automatic int bit_time_ns = UART_BIT_TIME;
        
        $display("📡 Waiting for UART TX response at time %0t", $time);
        
        // Wait for start bit (falling edge)
        while (uart_tx == 1 && timeout_count < timeout_cycles) begin
            #1ns;
            timeout_count++;
        end
        
        if (timeout_count >= timeout_cycles) begin
            $display("⚠️  UART receive timeout after %0d ns", timeout_count);
            data = 8'hFF;
            return;
        end
        
        $display("📍 Start bit detected at time %0t", $time);
        
        // Wait to middle of first data bit (1.5 bit times from start bit edge)
        #(bit_time_ns * 1.5 * 1ns);
        
        // Sample data bits
        for (int i = 0; i < 8; i++) begin
            received_byte[i] = uart_tx;
            $display("🔢 Bit %0d: %b at time %0t", i, uart_tx, $time);
            #(bit_time_ns * 1ns);
        end
        
        // Check stop bit
        if (uart_tx != 1) begin
            $display("⚠️  Invalid stop bit: expected 1, got %b", uart_tx);
        end
        
        data = received_byte;
        $display("📥 Received UART byte: 0x%02X at time %0t", data, $time);
    endtask
    
    // CRC8 calculation function
    function logic [7:0] calc_crc8(logic [7:0] data_bytes[]);
        automatic logic [7:0] crc = 0;
        for (int i = 0; i < data_bytes.size(); i++) begin
            crc ^= data_bytes[i];
            for (int j = 0; j < 8; j++) begin
                if (crc & 8'h80) begin
                    crc = (crc << 1) ^ 8'h07;
                end else begin
                    crc = crc << 1;
                end
            end
        end
        return crc;
    endfunction
    
    // Send write command frame
    task send_write_command(input logic [31:0] addr, input logic [31:0] data);
        automatic logic [7:0] frame_data[9];
        automatic logic [7:0] crc;
        
        $display("\n🖊️  Sending WRITE command to address 0x%08X with data 0x%08X", addr, data);
        
        // Prepare frame data (excluding SOF)
        frame_data[0] = 8'h20; // CMD: write
        frame_data[1] = addr[7:0];   // ADDR byte 0
        frame_data[2] = addr[15:8];  // ADDR byte 1  
        frame_data[3] = addr[23:16]; // ADDR byte 2
        frame_data[4] = addr[31:24]; // ADDR byte 3
        frame_data[5] = data[7:0];   // DATA byte 0
        frame_data[6] = data[15:8];  // DATA byte 1
        frame_data[7] = data[23:16]; // DATA byte 2
        frame_data[8] = data[31:24]; // DATA byte 3
        
        // Calculate CRC
        crc = calc_crc8(frame_data);
        
        // Send frame with proper spacing
        send_uart_byte(8'hA5);     // SOF (host-to-device)
        #(UART_BIT_TIME * 2 * 1ns); // Inter-byte gap
        send_uart_byte(8'h20);     // CMD
        #(UART_BIT_TIME * 2 * 1ns);
        send_uart_byte(addr[7:0]); // ADDR[7:0]
        #(UART_BIT_TIME * 2 * 1ns);
        send_uart_byte(addr[15:8]); // ADDR[15:8]
        #(UART_BIT_TIME * 2 * 1ns);
        send_uart_byte(addr[23:16]); // ADDR[23:16]
        #(UART_BIT_TIME * 2 * 1ns);
        send_uart_byte(addr[31:24]); // ADDR[31:24]
        #(UART_BIT_TIME * 2 * 1ns);
        send_uart_byte(data[7:0]); // DATA[7:0]
        #(UART_BIT_TIME * 2 * 1ns);
        send_uart_byte(data[15:8]); // DATA[15:8]
        #(UART_BIT_TIME * 2 * 1ns);
        send_uart_byte(data[23:16]); // DATA[23:16]
        #(UART_BIT_TIME * 2 * 1ns);
        send_uart_byte(data[31:24]); // DATA[31:24]
        #(UART_BIT_TIME * 2 * 1ns);
        send_uart_byte(crc);       // CRC
        
        #(UART_BIT_TIME * 5 * 1ns); // End of frame gap
        $display("✅ Write command sent with CRC=0x%02X", crc);
    endtask
    
    // Send read command frame
    task send_read_command(input logic [31:0] addr);
        automatic logic [7:0] frame_data[5];
        automatic logic [7:0] crc;
        
        $display("\n📖 Sending READ command to address 0x%08X", addr);
        
        // Prepare frame data (excluding SOF)
        frame_data[0] = 8'h10; // CMD: read
        frame_data[1] = addr[7:0];   // ADDR byte 0
        frame_data[2] = addr[15:8];  // ADDR byte 1
        frame_data[3] = addr[23:16]; // ADDR byte 2
        frame_data[4] = addr[31:24]; // ADDR byte 3
        
        // Calculate CRC
        crc = calc_crc8(frame_data);
        
        // Send frame with proper spacing
        send_uart_byte(8'hA5);     // SOF (host-to-device)
        #(UART_BIT_TIME * 2 * 1ns);
        send_uart_byte(8'h10);     // CMD (read)
        #(UART_BIT_TIME * 2 * 1ns);
        send_uart_byte(addr[7:0]); // ADDR[7:0]
        #(UART_BIT_TIME * 2 * 1ns);
        send_uart_byte(addr[15:8]); // ADDR[15:8]
        #(UART_BIT_TIME * 2 * 1ns);
        send_uart_byte(addr[23:16]); // ADDR[23:16]
        #(UART_BIT_TIME * 2 * 1ns);
        send_uart_byte(addr[31:24]); // ADDR[31:24]
        #(UART_BIT_TIME * 2 * 1ns);
        send_uart_byte(crc);       // CRC
        
        #(UART_BIT_TIME * 5 * 1ns); // End of frame gap
        $display("✅ Read command sent with CRC=0x%02X", crc);
    endtask
    
    // Receive response frame
    task receive_response(output logic [7:0] status, output logic [7:0] cmd_echo, output logic [31:0] read_data, input logic expect_data);
        automatic logic [7:0] sof, response_crc;
        automatic logic [7:0] received_bytes[8];
        automatic int byte_count = 0;
        
        $display("\n📨 Waiting for response frame...");
        
        // Receive SOF
        receive_uart_byte(sof, 100000);
        if (sof != 8'h5A) begin
            $display("❌ Invalid SOF received: 0x%02X (expected 0x5A)", sof);
            test_failed++;
            return;
        end
        
        // Receive STATUS
        receive_uart_byte(status, 50000);
        $display("📊 STATUS: 0x%02X", status);
        
        // Receive CMD_ECHO
        receive_uart_byte(cmd_echo, 50000);
        $display("🔄 CMD_ECHO: 0x%02X", cmd_echo);
        
        if (expect_data) begin
            // Receive 4 bytes of data for read response
            for (int i = 0; i < 4; i++) begin
                receive_uart_byte(received_bytes[i], 50000);
                $display("📄 DATA[%0d]: 0x%02X", i, received_bytes[i]);
            end
            read_data = {received_bytes[3], received_bytes[2], received_bytes[1], received_bytes[0]};
            $display("📑 Complete read data: 0x%08X", read_data);
        end else begin
            read_data = 32'h0;
        end
        
        // Receive CRC
        receive_uart_byte(response_crc, 50000);
        $display("🔐 Response CRC: 0x%02X", response_crc);
        
        if (status == 8'h00) begin
            $display("✅ Response received successfully");
            test_passed++;
        end else begin
            $display("❌ Error response: STATUS=0x%02X", status);
            test_failed++;
        end
    endtask
    
    // Test sequence
    initial begin
        test_complete = 0;
        test_passed = 0;
        test_failed = 0;
        uart_rx = 1;  // Idle state
        
        $display("🚀 Starting UART Write-Read Verification Test");
        $display("==========================================");
        
        // Enable waveform dumping
        $dumpfile("waveforms/uart_write_read_test.vcd");
        $dumpvars(0, uart_write_read_test);
        
        // Reset sequence
        rst = 1;
        #(100 * 8ns);  // Hold reset for 100 cycles
        rst = 0;
        $display("🔄 Reset released at time %0t", $time);
        
        // Wait for system stabilization
        #(1000 * 8ns);
        
        // Test 1: Write test data to register
        $display("\n=== TEST 1: Write Operation ===");
        send_write_command(32'h00001020, 32'hDEADBEEF);
        
        // Wait for processing and response
        #(20000 * 8ns);
        
        // Receive write response
        begin
            automatic logic [7:0] status, cmd_echo;
            automatic logic [31:0] dummy_data;
            receive_response(status, cmd_echo, dummy_data, 1'b0);
            
            if (status == 8'h00 && cmd_echo == 8'h20) begin
                $display("✅ Write operation completed successfully");
            end else begin
                $display("❌ Write operation failed: STATUS=0x%02X, CMD_ECHO=0x%02X", status, cmd_echo);
            end
        end
        
        // Wait between operations
        #(5000 * 8ns);
        
        // Test 2: Read back the data
        $display("\n=== TEST 2: Read Operation ===");
        send_read_command(32'h00001020);
        
        // Wait for processing and response
        #(20000 * 8ns);
        
        // Receive read response
        begin
            automatic logic [7:0] status, cmd_echo;
            automatic logic [31:0] read_data;
            receive_response(status, cmd_echo, read_data, 1'b1);
            
            if (status == 8'h00 && cmd_echo == 8'h10) begin
                $display("✅ Read operation completed successfully");
                
                // Verify data matches
                if (read_data == 32'hDEADBEEF) begin
                    $display("🎉 DATA VERIFICATION SUCCESS: Read data 0x%08X matches written data", read_data);
                    test_passed++;
                end else begin
                    $display("❌ DATA VERIFICATION FAILED: Read 0x%08X, Expected 0x%08X", read_data, 32'hDEADBEEF);
                    test_failed++;
                end
            end else begin
                $display("❌ Read operation failed: STATUS=0x%02X, CMD_ECHO=0x%02X", status, cmd_echo);
            end
        end
        
        // Test 3: Write different data and verify
        $display("\n=== TEST 3: Second Write-Read Cycle ===");
        send_write_command(32'h00001020, 32'hCAFEBABE);
        
        // Wait for processing and response
        #(20000 * 8ns);
        
        // Receive write response
        begin
            automatic logic [7:0] status, cmd_echo;
            automatic logic [31:0] dummy_data;
            receive_response(status, cmd_echo, dummy_data, 1'b0);
        end
        
        // Wait between operations
        #(5000 * 8ns);
        
        // Read back new data
        send_read_command(32'h00001020);
        
        // Wait for processing and response
        #(20000 * 8ns);
        
        // Receive read response and verify
        begin
            automatic logic [7:0] status, cmd_echo;
            automatic logic [31:0] read_data;
            receive_response(status, cmd_echo, read_data, 1'b1);
            
            if (status == 8'h00 && read_data == 32'hCAFEBABE) begin
                $display("🎉 SECOND DATA VERIFICATION SUCCESS: Read data 0x%08X matches written data", read_data);
                test_passed++;
            end else begin
                $display("❌ SECOND DATA VERIFICATION FAILED: Read 0x%08X, Expected 0x%08X", read_data, 32'hCAFEBABE);
                test_failed++;
            end
        end
        
        // Final results
        #(1000 * 8ns);
        $display("\n📊 Test Results Summary:");
        $display("========================");
        $display("✅ Passed: %0d", test_passed);
        $display("❌ Failed: %0d", test_failed);
        
        if (test_failed == 0) begin
            $display("🏆 ALL TESTS PASSED - Write-Read verification successful!");
        end else begin
            $display("💥 SOME TESTS FAILED - Check implementation");
        end
        
        test_complete = 1;
        $finish;
    end
    
    // Simulation timeout
    initial begin
        #50ms;
        $display("⏰ Simulation timeout reached");
        $finish;
    end
    
endmodule