`timescale 1ns / 1ps

/*
 * AXI4-Lite Basic Operation Testbench
 * 
 * Purpose: Isolated testing of AXI Master + Register_Block 
 *          WITHOUT UART bridge complexity
 * 
 * This testbench directly drives AXI Master inputs to verify:
 * 1. Basic AXI4-Lite protocol compliance
 * 2. Register_Block write/read functionality
 * 3. Data integrity through complete transactions
 */

`include "uvm_macros.svh"
import uvm_pkg::*;

// Include test classes
`include "axi_basic_operation_test.sv"

module axi_basic_tb;

    // Clock and reset generation
    logic clk = 0;
    logic rst = 1;
    
    // Clock generation (125MHz)
    always #4ns clk = ~clk;
    
    // Reset generation
    initial begin
        rst = 1;
        #100ns;
        rst = 0;
    end
    
    // AXI4-Lite interface
    axi4_lite_if axi_if (clk, rst);
    
    // DUT: Direct AXI Master + Register_Block connection
    // This bypasses UART bridge to test pure AXI functionality
    
    // AXI Master instance
    logic [7:0]  axi_cmd = 8'h20;           // Write command
    logic [31:0] axi_addr = 32'h00001020;   // REG_TEST_0 address
    logic [7:0]  axi_write_data [0:63];     // Write data array
    logic        axi_start_transaction = 0; // Transaction trigger
    logic        axi_transaction_done;      // Transaction completion
    logic [7:0]  axi_status;                // Transaction status
    logic [7:0]  axi_read_data [0:63];      // Read data array
    logic [6:0]  axi_read_data_count;       // Read data count
    
    Axi4_Lite_Master axi_master (
        .clk(clk),
        .rst(rst),
        .cmd(axi_cmd),
        .addr(axi_addr),
        .write_data(axi_write_data),
        .start_transaction(axi_start_transaction),
        .transaction_done(axi_transaction_done),
        .axi_status(axi_status),
        .read_data(axi_read_data),
        .read_data_count(axi_read_data_count),
        .axi(axi_if.master)
    );
    
    // Register Block instance
    Register_Block #(
        .ADDR_WIDTH(32),
        .DATA_WIDTH(32),
        .BASE_ADDR(32'h0000_1000)
    ) register_block (
        .clk(clk),
        .rst(rst),
        .axi(axi_if.slave),
        // bridge_enable removed
        .bridge_reset_stats(),
        .baud_div_config(),
        .timeout_config(),
        .debug_mode(),
        .bridge_busy(1'b0),
        .error_code(8'h00),
        .tx_count(16'h0000),
        .rx_count(16'h0000),
        .fifo_status(8'h00)
    );
    
    // Test stimulus
    initial begin
        // Initialize write data array
        for (int i = 0; i < 64; i++) begin
            axi_write_data[i] = 8'h00;
        end
        
        // Wait for reset deassertion
        wait (!rst);
        #200ns;
        
        // Test 1: Basic write to REG_TEST_0
        $display("=== Test 1: Write 0x12345678 to REG_TEST_0 ===");
        axi_cmd = 8'h20;  // Write command
        axi_addr = 32'h00001020;  // REG_TEST_0
        axi_write_data[0] = 8'h78;  // LSB first
        axi_write_data[1] = 8'h56;
        axi_write_data[2] = 8'h34;
        axi_write_data[3] = 8'h12;  // MSB
        
        axi_start_transaction = 1;
        #20ns;
        axi_start_transaction = 0;
        
        // Wait for completion
        wait (axi_transaction_done);
        $display("Write transaction completed, status = 0x%02X", axi_status);
        #200ns;
        
        // Test 2: Read back from REG_TEST_0
        $display("=== Test 2: Read back from REG_TEST_0 ===");
        axi_cmd = 8'hA0;  // Read command
        axi_addr = 32'h00001020;  // REG_TEST_0
        
        axi_start_transaction = 1;
        #20ns;
        axi_start_transaction = 0;
        
        // Wait for completion
        wait (axi_transaction_done);
        $display("Read transaction completed, status = 0x%02X", axi_status);
        $display("Read data count = %d", axi_read_data_count);
        if (axi_read_data_count >= 4) begin
            logic [31:0] read_value = {axi_read_data[3], axi_read_data[2], axi_read_data[1], axi_read_data[0]};
            $display("Read value = 0x%08X", read_value);
            if (read_value == 32'h12345678) begin
                $display("✅ SUCCESS: Write/Read cycle worked correctly!");
            end else begin
                $display("❌ FAILURE: Expected 0x12345678, got 0x%08X", read_value);
            end
        end else begin
            $display("❌ FAILURE: Insufficient read data returned");
        end
        
        #500ns;
        
        // Test 3: Multiple register test
        $display("=== Test 3: Multiple REG_TEST register access ===");
        for (int reg_idx = 0; reg_idx < 4; reg_idx++) begin
            logic [31:0] test_addr = 32'h00001020 + (reg_idx * 4);
            logic [31:0] test_data = 32'h11111111 * (reg_idx + 1);
            
            $display("Writing 0x%08X to address 0x%08X", test_data, test_addr);
            
            // Write
            axi_cmd = 8'h20;
            axi_addr = test_addr;
            axi_write_data[0] = test_data[7:0];
            axi_write_data[1] = test_data[15:8];
            axi_write_data[2] = test_data[23:16];
            axi_write_data[3] = test_data[31:24];
            
            axi_start_transaction = 1;
            #20ns;
            axi_start_transaction = 0;
            wait (axi_transaction_done);
            
            #100ns;
            
            // Read back
            axi_cmd = 8'hA0;
            axi_addr = test_addr;
            
            axi_start_transaction = 1;
            #20ns;
            axi_start_transaction = 0;
            wait (axi_transaction_done);
            
            if (axi_read_data_count >= 4) begin
                logic [31:0] read_value = {axi_read_data[3], axi_read_data[2], axi_read_data[1], axi_read_data[0]};
                $display("Read back 0x%08X from address 0x%08X", read_value, test_addr);
                if (read_value == test_data) begin
                    $display("✅ Register %d: PASS", reg_idx);
                end else begin
                    $display("❌ Register %d: FAIL - Expected 0x%08X, got 0x%08X", reg_idx, test_data, read_value);
                end
            end else begin
                $display("❌ Register %d: FAIL - No read data", reg_idx);
            end
            
            #200ns;
        end
        
        #1000ns;
        $display("=== AXI Basic Operation Test Completed ===");
        $finish;
    end
    
    // Timeout watchdog
    initial begin
        #50us;
        $display("❌ TIMEOUT: Test did not complete within expected time");
        $finish;
    end
    
    // Waveform dumping
    initial begin
        $dumpfile("axi_basic_test.mxd");
        $dumpvars(0, axi_basic_tb);
    end

endmodule