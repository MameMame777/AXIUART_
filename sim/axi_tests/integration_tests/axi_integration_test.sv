`timescale 1ns / 1ps

// AXI Master + Register_Block Integration Test
// Tests real RTL modules together to identify actual hardware issues
module axi_integration_test;
    
    // Clock and reset
    logic clk;
    logic rst;
    
    // Test control
    logic test_complete;
    int test_passed;
    int test_failed;
    
    // Clock generation
    initial begin
        clk = 0;
        forever #4ns clk = ~clk; // 125MHz
    end
    
    // AXI4-Lite interface
    axi4_lite_if axi_if(.clk(clk), .rst(rst));
    
    // DUT instantiations - REAL RTL MODULES
    // AXI Master (Device Under Test #1)
    logic [7:0]  cmd;
    logic [31:0] addr;
    logic [7:0]  write_data [0:63];
    logic        start_transaction;
    logic        transaction_done;
    logic [7:0]  axi_status;
    logic [7:0]  read_data [0:63];
    logic [5:0]  read_data_count;
    
    Axi4_Lite_Master #(
        .AXI_TIMEOUT(1000),          // Reduced timeout for faster testing
        .EARLY_BUSY_THRESHOLD(100)
    ) axi_master (
        .clk(clk),
        .rst(rst),
        .cmd(cmd),
        .addr(addr),
        .write_data(write_data),
        .start_transaction(start_transaction),
        .transaction_done(transaction_done),
        .axi_status(axi_status),
        .read_data(read_data),
        .read_data_count(read_data_count),
        .axi(axi_if.master)
    );
    
    // Register Block (Device Under Test #2)
    logic        bridge_enable;
    logic        bridge_reset_stats;
    logic [7:0]  baud_div_config;
    logic [7:0]  timeout_config;
    logic [3:0]  debug_mode;
    logic        bridge_busy;
    logic [7:0]  error_code;
    logic [15:0] tx_count;
    logic [15:0] rx_count;
    logic [7:0]  fifo_status;
    
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
        .error_code(error_code),
        .tx_count(tx_count),
        .rx_count(rx_count),
        .fifo_status(fifo_status)
    );
    
    // Test stimulus and monitoring
    initial begin
        $display("🎯 Starting AXI Master + Register_Block Integration Test");
        $display("===============================================================");
        
        // Initialize
        test_complete = 0;
        test_passed = 0;
        test_failed = 0;
        
        // Reset sequence
        rst = 1;
        start_transaction = 0;
        cmd = 0;
        addr = 0;
        
        // Initialize status inputs to Register_Block
        bridge_busy = 0;
        error_code = 0;
        tx_count = 0;
        rx_count = 0;
        fifo_status = 0;
        
        // Clear write_data array
        for (int i = 0; i < 64; i++) begin
            write_data[i] = 0;
        end
        
        // Wait for reset
        repeat(10) @(posedge clk);
        rst = 0;
        $display("✅ Reset released at time %0t", $time);
        
        // Wait for stabilization
        repeat(10) @(posedge clk);
        
        // Test 1: Write to REG_TEST register (0x1020)
        $display("\n🧪 Test 1: Write to REG_TEST Register");
        $display("   Writing 0xA5A5A5A5 to address 0x00001020");
        
        // Set up write command: 32-bit write, single beat
        cmd = 8'b00100000; // RW=0(write), INC=0, SIZE=10(32-bit), LEN=0000(1 beat)
        addr = 32'h00001020; // REG_TEST address
        write_data[0] = 8'hA5;
        write_data[1] = 8'hA5;
        write_data[2] = 8'hA5;
        write_data[3] = 8'hA5;
        
        // Start transaction
        @(posedge clk);
        start_transaction = 1;
        @(posedge clk);
        start_transaction = 0;
        
        // Wait for completion with timeout
        fork
            begin
                wait(transaction_done);
                $display("   ✅ Transaction completed at time %0t", $time);
                if (axi_status == 8'h00) begin
                    $display("   ✅ PASS: Write status OK (0x%02X)", axi_status);
                    test_passed++;
                end else begin
                    $display("   ❌ FAIL: Write status error (0x%02X)", axi_status);
                    test_failed++;
                end
            end
            begin
                #50us;
                $display("   ❌ FAIL: Write transaction timeout");
                test_failed++;
            end
        join_any
        disable fork;
        
        // Wait before next test
        repeat(20) @(posedge clk);
        
        // Test 2: Read back from REG_TEST register
        $display("\n🧪 Test 2: Read from REG_TEST Register");
        $display("   Reading from address 0x00001020");
        
        // Set up read command: 32-bit read, single beat
        cmd = 8'b10100000; // RW=1(read), INC=0, SIZE=10(32-bit), LEN=0000(1 beat)
        addr = 32'h00001020; // REG_TEST address
        
        // Start transaction
        @(posedge clk);
        start_transaction = 1;
        @(posedge clk);
        start_transaction = 0;
        
        // Wait for completion with timeout
        fork
            begin
                wait(transaction_done);
                $display("   ✅ Transaction completed at time %0t", $time);
                if (axi_status == 8'h00) begin
                    logic [31:0] read_value;
                    read_value = {read_data[3], read_data[2], read_data[1], read_data[0]};
                    $display("   ✅ Read status OK (0x%02X)", axi_status);
                    $display("   📖 Read data: 0x%08X", read_value);
                    if (read_value == 32'hA5A5A5A5) begin
                        $display("   ✅ PASS: Read data matches written data");
                        test_passed++;
                    end else begin
                        $display("   ❌ FAIL: Read data mismatch (expected 0xA5A5A5A5)");
                        test_failed++;
                    end
                end else begin
                    $display("   ❌ FAIL: Read status error (0x%02X)", axi_status);
                    test_failed++;
                end
            end
            begin
                #50us;
                $display("   ❌ FAIL: Read transaction timeout");
                test_failed++;
            end
        join_any
        disable fork;
        
        // Wait before next test
        repeat(20) @(posedge clk);
        
        // Test 3: Write to Control register (0x1000)
        $display("\n🧪 Test 3: Write to UART Control Register");
        $display("   Writing 0x00000001 to address 0x00001000");
        
        // Set up write command: 32-bit write, single beat
        cmd = 8'b00100000; // RW=0(write), INC=0, SIZE=10(32-bit), LEN=0000(1 beat)
        addr = 32'h00001000; // Control register address
        write_data[0] = 8'h01;
        write_data[1] = 8'h00;
        write_data[2] = 8'h00;
        write_data[3] = 8'h00;
        
        // Start transaction
        @(posedge clk);
        start_transaction = 1;
        @(posedge clk);
        start_transaction = 0;
        
        // Wait for completion with timeout
        fork
            begin
                wait(transaction_done);
                $display("   ✅ Transaction completed at time %0t", $time);
                if (axi_status == 8'h00) begin
                    $display("   ✅ PASS: Control register write status OK (0x%02X)", axi_status);
                    test_passed++;
                end else begin
                    $display("   ❌ FAIL: Control register write status error (0x%02X)", axi_status);
                    test_failed++;
                end
            end
            begin
                #50us;
                $display("   ❌ FAIL: Control register write transaction timeout");
                test_failed++;
            end
        join_any
        disable fork;
        
        // Test Results
        $display("\n🏁 Integration Test Results");
        $display("=============================");
        $display("Total Tests: %0d", test_passed + test_failed);
        $display("Passed: %0d", test_passed);
        $display("Failed: %0d", test_failed);
        
        if (test_failed == 0) begin
            $display("🎉 ALL TESTS PASSED - Integration Test SUCCESSFUL");
        end else begin
            $display("❌ SOME TESTS FAILED - Integration Test FAILED");
        end
        
        test_complete = 1;
        $finish;
    end
    
    // Timeout watchdog
    initial begin
        #200us;
        $display("❌ TIMEOUT: Integration test exceeded maximum time");
        $finish;
    end
    
    // Waveform dumping
    initial begin
        $dumpfile("axi_integration_test.mxd");
        $dumpvars(0, axi_integration_test);
    end

endmodule