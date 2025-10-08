`timescale 1ns / 1ps

// Simple UART response debug test
module uart_response_debug_test;
    
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
    
    // UART timing parameters
    localparam real UART_BIT_TIME = 8680.6; // 115200 baud = 8680.6ns per bit
    
    // Register Block status inputs/outputs (missing declarations)
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
        .BAUD_RATE(115200),
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
        .bridge_reset_stats(bridge_reset_stats),
        .baud_div_config(baud_div_config),
        .timeout_config(timeout_config),
        .debug_mode(debug_mode),
        .error_code(error_code),
        .tx_count(tx_count),
        .rx_count(rx_count),
        .fifo_status(fifo_status)
    );
    
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
    
    // Monitor UART TX for response
    initial begin
        fork
            forever begin
                @(negedge uart_tx);
                $display("🔍 UART TX start bit detected at time %0t", $time);
                
                // Wait 1.5 bit times to middle of first data bit
                #(UART_BIT_TIME * 1.5 * 1ns);
                
                begin
                    automatic logic [7:0] rx_byte = 0;
                    for (int i = 0; i < 8; i++) begin
                        rx_byte[i] = uart_tx;
                        $display("🔍 TX bit %0d: %b", i, uart_tx);
                        if (i < 7) #(UART_BIT_TIME * 1ns);
                    end
                    
                    $display("🔍 UART TX byte received: 0x%02X at time %0t", rx_byte, $time);
                end
            end
        join_none
    end
    
    // Main test sequence
    initial begin
        $display("🎯 Starting Simple UART Response Debug Test");
        $display("===========================================");
        
        // Initialize
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
        
        // Send simple write command frame manually
        $display("\n📤 Sending UART write command frame");
        send_uart_byte(8'hA5);    // SOF (Host-to-Device) - CORRECTED!
        send_uart_byte(8'h20);    // CMD: Write, 32-bit, 1 beat
        send_uart_byte(8'h20);    // ADDR[7:0] - 0x00001020
        send_uart_byte(8'h10);    // ADDR[15:8]
        send_uart_byte(8'h00);    // ADDR[23:16]
        send_uart_byte(8'h00);    // ADDR[31:24]
        send_uart_byte(8'hBE);    // DATA[7:0] - 0xCAFEBABE
        send_uart_byte(8'hBA);    // DATA[15:8]
        send_uart_byte(8'hFE);    // DATA[23:16]
        send_uart_byte(8'hCA);    // DATA[31:24]
        send_uart_byte(8'h3B);    // CRC8 (correct calculated value excluding SOF)
        
        $display("📤 Write command frame transmission complete");
        
        // Wait for write response processing
        #3ms;
        
        // Now test read operation
        $display("\n📖 Sending READ command frame");
        send_uart_byte(8'hA5);    // SOF (Host-to-Device)
        send_uart_byte(8'h90);    // CMD: Read (bit[7]=1 for read)
        send_uart_byte(8'h20);    // ADDR[7:0] - 0x00001020
        send_uart_byte(8'h10);    // ADDR[15:8]
        send_uart_byte(8'h00);    // ADDR[23:16]
        send_uart_byte(8'h00);    // ADDR[31:24]
        send_uart_byte(8'hDE);    // CRC8 for read command
        
        $display("📤 Read command frame transmission complete");
        
        // Wait for read response processing
        #3ms;
        
        $display("\n✅ Write-Read Test completed");
        $finish;
    end
    
    // Timeout watchdog
    initial begin
        #10ms;
        $display("❌ TIMEOUT: Write-Read test exceeded maximum time");
        $finish;
    end
    
    // Waveform dumping
    initial begin
        $dumpfile("uart_response_debug.mxd");
        $dumpvars(0, uart_response_debug_test);
    end
    
endmodule