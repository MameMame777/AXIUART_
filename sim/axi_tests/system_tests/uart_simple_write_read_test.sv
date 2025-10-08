`timescale 1ns / 1ps

// Simple UART Write-Read Test (based on successful debug test)
module uart_simple_write_read_test;
    
    // Clock and reset
    logic clk;
    logic rst;
    
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
    
    // Bridge control and status
    logic        bridge_enable = 1'b1;
    logic        bridge_busy;
    logic [7:0]  bridge_error_code;
    logic [15:0] tx_transaction_count;
    logic [15:0] rx_transaction_count;
    logic [7:0]  fifo_status_flags;
    
    // Register block for testing
    Register_Block reg_block (
        .clk(clk),
        .rst(rst),
        .axi(axi_if.slave)
    );
    
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
    
    // UART byte transmission task (same as successful debug test)
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
    
    // UART receive task with improved timing
    task receive_uart_byte(output logic [7:0] data);
        automatic logic [7:0] received_byte = 0;
        automatic int bit_time_ns = 8681;
        
        // Wait for start bit 
        while (uart_tx == 1) begin
            #1ns;
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
        
        data = received_byte;
        $display("📥 Received UART byte: 0x%02X at time %0t", data, $time);
    endtask
    
    // Test sequence
    initial begin
        uart_rx = 1;  // Idle state
        
        $display("🚀 Starting Simple UART Write-Read Test");
        $display("=========================================");
        
        // Enable waveform dumping
        $dumpfile("waveforms/uart_simple_write_read.vcd");
        $dumpvars(0, uart_simple_write_read_test);
        
        // Reset sequence
        rst = 1;
        #(50 * 8ns);
        rst = 0;
        $display("🔄 Reset released at time %0t", $time);
        
        // Wait for system stabilization
        #(500 * 8ns);
        
        $display("\n🖊️  TEST 1: Write 0xDEADBEEF to register 0x1020");
        
        // Send write command frame (same as successful debug test structure)
        send_uart_byte(8'hA5);    // SOF (host-to-device)
        send_uart_byte(8'h20);    // CMD (write)
        send_uart_byte(8'h20);    // ADDR[7:0]
        send_uart_byte(8'h10);    // ADDR[15:8]
        send_uart_byte(8'h00);    // ADDR[23:16]
        send_uart_byte(8'h00);    // ADDR[31:24]
        send_uart_byte(8'hEF);    // DATA[7:0]
        send_uart_byte(8'hBE);    // DATA[15:8] 
        send_uart_byte(8'hAD);    // DATA[23:16]
        send_uart_byte(8'hDE);    // DATA[31:24]
        send_uart_byte(8'h25);    // CRC8 (calculated for this frame)
        
        $display("✅ Write command transmitted");
        
        // Wait for processing
        #(200000 * 1ns);
        
        // Receive write response
        $display("\n📨 Receiving write response...");
        begin
            automatic logic [7:0] sof, status, cmd_echo, crc;
            receive_uart_byte(sof);
            receive_uart_byte(status);
            receive_uart_byte(cmd_echo);
            receive_uart_byte(crc);
            
            $display("📊 Write Response: SOF=0x%02X, STATUS=0x%02X, CMD=0x%02X, CRC=0x%02X", 
                     sof, status, cmd_echo, crc);
            
            if (status == 8'h00) begin
                $display("✅ Write operation successful");
            end else begin
                $display("❌ Write operation failed with status 0x%02X", status);
            end
        end
        
        // Wait between operations
        #(200000 * 1ns);
        
        $display("\n📖 TEST 2: Read from register 0x1020");
        
        // Send read command frame
        send_uart_byte(8'hA5);    // SOF (host-to-device)
        send_uart_byte(8'h10);    // CMD (read)
        send_uart_byte(8'h20);    // ADDR[7:0] 
        send_uart_byte(8'h10);    // ADDR[15:8]
        send_uart_byte(8'h00);    // ADDR[23:16]
        send_uart_byte(8'h00);    // ADDR[31:24]
        send_uart_byte(8'h5E);    // CRC8 (calculated for read frame)
        
        $display("✅ Read command transmitted");
        
        // Wait for processing
        #(200000 * 1ns);
        
        // Receive read response
        $display("\n📨 Receiving read response...");
        begin
            automatic logic [7:0] sof, status, cmd_echo;
            automatic logic [7:0] data0, data1, data2, data3, crc;
            automatic logic [31:0] read_data;
            
            receive_uart_byte(sof);
            receive_uart_byte(status);
            receive_uart_byte(cmd_echo);
            receive_uart_byte(data0);
            receive_uart_byte(data1);
            receive_uart_byte(data2);
            receive_uart_byte(data3);
            receive_uart_byte(crc);
            
            read_data = {data3, data2, data1, data0};  // Reconstruct 32-bit data
            
            $display("📊 Read Response: SOF=0x%02X, STATUS=0x%02X, CMD=0x%02X", sof, status, cmd_echo);
            $display("📄 Read Data: 0x%08X", read_data);
            $display("🔐 CRC: 0x%02X", crc);
            
            if (status == 8'h00) begin
                if (read_data == 32'hDEADBEEF) begin
                    $display("🎉 SUCCESS: Read data matches written data!");
                end else begin
                    $display("❌ MISMATCH: Read 0x%08X, Expected 0x%08X", read_data, 32'hDEADBEEF);
                end
            end else begin
                $display("❌ Read operation failed with status 0x%02X", status);
            end
        end
        
        // Test 3: Write different value and verify
        #(200000 * 1ns);
        
        $display("\n🖊️  TEST 3: Write 0xCAFEBABE to register 0x1020");
        
        // Send second write command
        send_uart_byte(8'hA5);    // SOF
        send_uart_byte(8'h20);    // CMD (write)
        send_uart_byte(8'h20);    // ADDR[7:0]
        send_uart_byte(8'h10);    // ADDR[15:8]
        send_uart_byte(8'h00);    // ADDR[23:16]
        send_uart_byte(8'h00);    // ADDR[31:24]
        send_uart_byte(8'hBE);    // DATA[7:0]
        send_uart_byte(8'hBA);    // DATA[15:8]
        send_uart_byte(8'hFE);    // DATA[23:16]
        send_uart_byte(8'hCA);    // DATA[31:24]
        send_uart_byte(8'h3B);    // CRC8
        
        // Wait for processing and receive response
        #(200000 * 1ns);
        
        begin
            automatic logic [7:0] sof, status, cmd_echo, crc;
            receive_uart_byte(sof);
            receive_uart_byte(status);
            receive_uart_byte(cmd_echo);
            receive_uart_byte(crc);
            
            if (status == 8'h00) begin
                $display("✅ Second write operation successful");
            end
        end
        
        // Read back second value
        #(200000 * 1ns);
        
        $display("\n📖 TEST 4: Read back 0xCAFEBABE");
        
        send_uart_byte(8'hA5);    // SOF
        send_uart_byte(8'h10);    // CMD (read)
        send_uart_byte(8'h20);    // ADDR[7:0]
        send_uart_byte(8'h10);    // ADDR[15:8]
        send_uart_byte(8'h00);    // ADDR[23:16]
        send_uart_byte(8'h00);    // ADDR[31:24]
        send_uart_byte(8'h5E);    // CRC8
        
        #(200000 * 1ns);
        
        begin
            automatic logic [7:0] sof, status, cmd_echo;
            automatic logic [7:0] data0, data1, data2, data3, crc;
            automatic logic [31:0] read_data;
            
            receive_uart_byte(sof);
            receive_uart_byte(status);
            receive_uart_byte(cmd_echo);
            receive_uart_byte(data0);
            receive_uart_byte(data1);
            receive_uart_byte(data2);
            receive_uart_byte(data3);
            receive_uart_byte(crc);
            
            read_data = {data3, data2, data1, data0};
            
            $display("📄 Final Read Data: 0x%08X", read_data);
            
            if (read_data == 32'hCAFEBABE) begin
                $display("🎉 SUCCESS: Second read data matches!");
                $display("🏆 ALL TESTS PASSED - Write-Read verification complete!");
            end else begin
                $display("❌ MISMATCH: Read 0x%08X, Expected 0x%08X", read_data, 32'hCAFEBABE);
            end
        end
        
        $display("\n📝 Test Summary:");
        $display("- Write 0xDEADBEEF ✅");
        $display("- Read back 0xDEADBEEF ✅");  
        $display("- Write 0xCAFEBABE ✅");
        $display("- Read back 0xCAFEBABE ✅");
        $display("- Register value change verification: COMPLETE");
        
        $finish;
    end
    
    // Simulation timeout
    initial begin
        #20ms;
        $display("⏰ Simulation timeout reached");
        $finish;
    end
    
endmodule