`timescale 1ns / 1ps

// Complete UART Protocol Validation Test
// Tests actual UART frame transmission -> register access -> UART response
module uart_protocol_validation_test;
    
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
    
    // Bridge control and status
    logic        bridge_enable;
    logic        bridge_busy;
    logic [7:0]  bridge_error_code;
    logic [15:0] tx_transaction_count;
    logic [15:0] rx_transaction_count;
    logic [7:0]  fifo_status_flags;
    
    // Debug signals
    logic [7:0] debug_parser_cmd;
    logic [7:0] debug_builder_cmd_echo;
    logic [7:0] debug_builder_cmd_out;
    logic [7:0] debug_parser_status;
    logic [7:0] debug_builder_status;
    logic [3:0] debug_parser_state;
    logic [3:0] debug_builder_state;
    logic       reset_statistics;
    
    // Register Block status inputs/outputs
    logic        bridge_reset_stats;
    logic [7:0]  baud_div_config;
    logic [7:0]  timeout_config;
    logic [3:0]  debug_mode;
    logic [7:0]  error_code;
    logic [15:0] tx_count;
    logic [15:0] rx_count;
    logic [7:0]  fifo_status;
    
    // DUT: Complete UART-AXI Bridge System
    Uart_Axi4_Bridge #(
        .CLK_FREQ_HZ(125_000_000),
        .BAUD_RATE(115200),         // 8.68μs per bit
        .AXI_TIMEOUT(1000),
        .UART_OVERSAMPLE(16),
        .RX_FIFO_DEPTH(64),
        .TX_FIFO_DEPTH(64),
        .MAX_LEN(16)
    ) uart_axi_bridge (
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
        .debug_parser_cmd(debug_parser_cmd),
        .debug_builder_cmd_echo(debug_builder_cmd_echo),
        .debug_builder_cmd_out(debug_builder_cmd_out),
        .debug_parser_status(debug_parser_status),
        .debug_builder_status(debug_builder_status),
        .debug_parser_state(debug_parser_state),
        .debug_builder_state(debug_builder_state),
        .reset_statistics(reset_statistics)
    );
    
    // Register Block (AXI Slave)
    Register_Block register_block (
        .clk(clk),
        .rst(rst),
        .axi(axi_if.slave),
        .bridge_enable(bridge_enable),
        .bridge_reset_stats(bridge_reset_stats),
        .baud_div_config(baud_div_config),
        .timeout_config(timeout_config),
        .debug_mode(debug_mode),
        .bridge_busy(bridge_busy),
        .error_code(bridge_error_code),
        .tx_count(tx_transaction_count),
        .rx_count(rx_transaction_count),
        .fifo_status(fifo_status_flags)
    );
    
    // UART timing parameters
    localparam int UART_BIT_TIME = 1000000000 / 115200; // 8680 ns per bit
    
    // UART Transmitter task (sends data to DUT)
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
    
    // UART Receiver task (receives data from DUT)
    task receive_uart_byte(output logic [7:0] data, input int timeout_cycles);
        automatic int timeout_count = 0;
        automatic logic [7:0] received_byte = 0;
        
        $display("📡 Looking for start bit on uart_tx (currently %b) at time %0t", uart_tx, $time);
        
        // Wait for start bit (falling edge)
        while (uart_tx == 1 && timeout_count < timeout_cycles) begin
            @(posedge clk);
            timeout_count++;
        end
        
        if (timeout_count >= timeout_cycles) begin
            $display("⚠️  UART receive timeout waiting for start bit after %0d cycles", timeout_count);
            data = 8'hFF; // Error indicator
            return;
        end
        
        $display("📡 Start bit detected at time %0t", $time);
        
        // Wait for middle of first data bit (1.5 bit times from start bit edge)
        #(UART_BIT_TIME * 1.5 * 1ns);
        
        // Sample data bits (LSB first) - sample at middle of each bit period
        for (int i = 0; i < 8; i++) begin
            received_byte[i] = uart_tx;
            $display("📡 Bit %0d: %b (time %0t)", i, uart_tx, $time);
            if (i < 7) #(UART_BIT_TIME * 1ns); // Don't wait after last bit
        end
        
        // Wait for stop bit and check it
        #(UART_BIT_TIME * 1ns);
        if (uart_tx != 1) begin
            $display("⚠️  Invalid stop bit (got %b) at time %0t", uart_tx, $time);
        end else begin
            $display("📡 Stop bit OK at time %0t", $time);
        end
        
        data = received_byte;
        $display("📥 Received UART byte: 0x%02X at time %0t", data, $time);
    endtask
    
    // Calculate CRC8 for frame validation
    function automatic logic [7:0] calc_crc8(logic [7:0] data[], int length);
        logic [7:0] crc = 8'h00;
        logic [7:0] polynomial = 8'h07; // CRC-8-CCITT polynomial
        
        for (int i = 0; i < length; i++) begin
            crc = crc ^ data[i];
            for (int j = 0; j < 8; j++) begin
                if (crc[7])
                    crc = (crc << 1) ^ polynomial;
                else
                    crc = crc << 1;
            end
        end
        return crc;
    endfunction
    
    // Send complete UART command frame
    task send_uart_command(
        input logic [7:0]  cmd,
        input logic [31:0] addr,
        input logic [7:0]  data_bytes[64],
        input int          data_length
    );
        automatic logic [7:0] frame_data[256];
        automatic int frame_length = 0;
        automatic logic [7:0] crc;
        
        $display("📡 Sending UART command: cmd=0x%02X, addr=0x%08X, data_len=%0d", cmd, addr, data_length);
        
        // Build frame
        frame_data[frame_length++] = 8'hA5; // SOF
        frame_data[frame_length++] = cmd;
        frame_data[frame_length++] = addr[7:0];   // Little endian
        frame_data[frame_length++] = addr[15:8];
        frame_data[frame_length++] = addr[23:16];
        frame_data[frame_length++] = addr[31:24];
        
        // Add data bytes
        for (int i = 0; i < data_length; i++) begin
            frame_data[frame_length++] = data_bytes[i];
        end
        
        // Calculate and add CRC
        begin
            automatic logic [7:0] crc_data[256];
            for (int i = 1; i < frame_length; i++) begin
                crc_data[i-1] = frame_data[i];
            end
            crc = calc_crc8(crc_data, frame_length-1);
        end
        frame_data[frame_length++] = crc;
        
        // Send frame via UART
        for (int i = 0; i < frame_length; i++) begin
            send_uart_byte(frame_data[i]);
            #(UART_BIT_TIME * 2 * 1ns); // Inter-byte gap
        end
        
        $display("📡 Command frame sent, total bytes: %0d, CRC: 0x%02X", frame_length, crc);
    endtask
    
    // Receive UART response frame
    task receive_uart_response(output logic [7:0] response_data[64], output int response_length);
        automatic logic [7:0] received_byte;
        automatic int timeout_cycles = 1250000; // 10ms timeout at 125MHz
        
        response_length = 0;
        
        $display("📥 Waiting for UART response...");
        
        // Receive SOF (should be 0x5A for device-to-host)
        receive_uart_byte(received_byte, timeout_cycles);
        if (received_byte == 8'hFF) begin
            $display("❌ No UART response received (SOF timeout)");
            return;
        end
        
        if (received_byte != 8'h5A) begin
            $display("⚠️  Invalid SOF: expected 0x5A, got 0x%02X", received_byte);
            // Continue anyway, might be valid response without SOF
        end
        
        $display("📥 SOF received: 0x%02X", received_byte);
        
        // Receive response bytes (status, cmd_echo, crc)
        for (int i = 0; i < 3; i++) begin
            receive_uart_byte(received_byte, timeout_cycles / 10);
            if (received_byte == 8'hFF) begin
                $display("❌ Response byte %0d timeout", i);
                break; // Timeout
            end
            
            response_data[response_length++] = received_byte;
            $display("📥 Response byte %0d: 0x%02X", i, received_byte);
        end
        
        $display("📥 Response complete, length: %0d bytes", response_length);
    endtask
    
    // Main test sequence
    initial begin
        $display("🎯 Starting Complete UART Protocol Validation Test");
        $display("====================================================");
        
        // Initialize
        test_complete = 0;
        test_passed = 0;
        test_failed = 0;
        
        // Reset sequence
        rst = 1;
        uart_rx = 1; // UART idle state
        uart_cts_n = 0; // CTS active (ready to send)
        bridge_enable = 1; // Enable bridge
        reset_statistics = 0;
        
        // Wait for reset
        repeat(50) @(posedge clk);
        rst = 0;
        $display("✅ Reset released at time %0t", $time);
        
        // Wait for system to stabilize
        #100us;
        
        // Test 1: Write to REG_TEST register via UART
        $display("\n🧪 Test 1: UART Write to REG_TEST Register");
        $display("   Writing 0xCAFEBABE to address 0x00001020");
        
        begin
            automatic logic [7:0] write_data[64];
            automatic logic [7:0] response[64];
            automatic int response_len;
            
            // Initialize write data (little endian)
            write_data[0] = 8'hBE; // LSB
            write_data[1] = 8'hBA;
            write_data[2] = 8'hFE;
            write_data[3] = 8'hCA; // MSB
            
            // Send UART write command
            send_uart_command(
                8'b00100000, // cmd: RW=0(write), INC=0, SIZE=10(32-bit), LEN=0000(1 beat)
                32'h00001020, // addr: REG_TEST register
                write_data,
                4
            );
            
            // Wait for response
            receive_uart_response(response, response_len);
            
            if (response_len > 0 && response[0] == 8'h00) begin
                $display("   ✅ PASS: UART write successful (status=0x%02X)", response[0]);
                test_passed++;
            end else begin
                $display("   ❌ FAIL: UART write failed (status=0x%02X)", response_len > 0 ? response[0] : 8'hFF);
                test_failed++;
            end
        end
        
        // Wait between tests
        #50us;
        
        // Test 2: Read from REG_TEST register via UART
        $display("\n🧪 Test 2: UART Read from REG_TEST Register");
        $display("   Reading from address 0x00001020");
        
        begin
            automatic logic [7:0] empty_data[64];
            automatic logic [7:0] response[64];
            automatic int response_len;
            automatic logic [31:0] read_value;
            
            // Send UART read command
            send_uart_command(
                8'b10100000, // cmd: RW=1(read), INC=0, SIZE=10(32-bit), LEN=0000(1 beat)
                32'h00001020, // addr: REG_TEST register
                empty_data,
                0
            );
            
            // Wait for response
            receive_uart_response(response, response_len);
            
            if (response_len >= 5) begin
                read_value = {response[4], response[3], response[2], response[1]}; // Little endian
                $display("   📖 Read data: 0x%08X", read_value);
                if (response[0] == 8'h00 && read_value == 32'hCAFEBABE) begin
                    $display("   ✅ PASS: UART read data matches written data");
                    test_passed++;
                end else begin
                    $display("   ❌ FAIL: UART read data mismatch (status=0x%02X, data=0x%08X)", response[0], read_value);
                    test_failed++;
                end
            end else begin
                $display("   ❌ FAIL: UART read response too short (%0d bytes)", response_len);
                test_failed++;
            end
        end
        
        // Wait between tests
        #50us;
        
        // Test 3: Write to Control register via UART
        $display("\n🧪 Test 3: UART Write to Control Register");
        $display("   Writing 0x00000001 to address 0x00001000");
        
        begin
            automatic logic [7:0] control_data[64];
            automatic logic [7:0] response[64];
            automatic int response_len;
            
            // Initialize control data
            control_data[0] = 8'h01; // Enable bridge
            control_data[1] = 8'h00;
            control_data[2] = 8'h00;
            control_data[3] = 8'h00;
            
            // Send UART write command
            send_uart_command(
                8'b00100000, // cmd: RW=0(write), INC=0, SIZE=10(32-bit), LEN=0000(1 beat)
                32'h00001000, // addr: Control register
                control_data,
                4
            );
            
            // Wait for response
            receive_uart_response(response, response_len);
            
            if (response_len > 0 && response[0] == 8'h00) begin
                $display("   ✅ PASS: UART control register write successful");
                test_passed++;
            end else begin
                $display("   ❌ FAIL: UART control register write failed (status=0x%02X)", response_len > 0 ? response[0] : 8'hFF);
                test_failed++;
            end
        end
        
        // Test Results
        $display("\n🏁 UART Protocol Validation Results");
        $display("====================================");
        $display("Total Tests: %0d", test_passed + test_failed);
        $display("Passed: %0d", test_passed);
        $display("Failed: %0d", test_failed);
        
        if (test_failed == 0) begin
            $display("🎉 ALL TESTS PASSED - UART Protocol Validation SUCCESSFUL");
        end else begin
            $display("❌ SOME TESTS FAILED - UART Protocol Validation FAILED");
        end
        
        test_complete = 1;
        $finish;
    end
    
    // Debug monitoring
    always @(posedge clk) begin
        if (debug_parser_state != 0 && debug_parser_state != 5) begin
            $display("DEBUG: Parser state=%0d, cmd=0x%02X, status=0x%02X at %0t", 
                     debug_parser_state, debug_parser_cmd, debug_parser_status, $time);
        end
        if (debug_builder_state != 0) begin
            $display("DEBUG: Builder state=%0d, cmd_echo=0x%02X, status=0x%02X at %0t", 
                     debug_builder_state, debug_builder_cmd_echo, debug_builder_status, $time);
        end
    end
    
    // Timeout watchdog
    initial begin
        #2ms; // Longer timeout for full protocol test
        $display("❌ TIMEOUT: Protocol validation test exceeded maximum time");
        $finish;
    end
    
    // Waveform dumping
    initial begin
        $dumpfile("uart_protocol_validation.mxd");
        $dumpvars(0, uart_protocol_validation_test);
    end

endmodule