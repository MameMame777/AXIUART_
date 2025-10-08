`timescale 1ns / 1ps

/*
 * Register_Block Unit Test
 * 
 * Purpose: Verify Register_Block AXI slave and REG_TEST register functionality
 * Success Criteria:
 * - REG_TEST registers (0x1020-0x102C) accessible
 * - AXI slave protocol compliance
 * - Data integrity through register operations
 * - Proper BRESP/RRESP generation
 */

module register_block_unit_test;

    // Test parameters
    localparam CLOCK_PERIOD = 8ns;  // 125MHz
    localparam RESET_CYCLES = 10;
    
    // Register addresses (BASE_ADDR + offset)
    localparam ADDR_REG_TEST_0 = 32'h00001020;
    localparam ADDR_REG_TEST_1 = 32'h00001024;
    localparam ADDR_REG_TEST_2 = 32'h00001028;
    localparam ADDR_REG_TEST_3 = 32'h0000102C;

    // Clock and reset
    logic clk = 0;
    logic rst = 1;
    
    // Clock generation
    always #(CLOCK_PERIOD/2) clk = ~clk;
    
    // Reset generation
    initial begin
        rst = 1;
        repeat(RESET_CYCLES) @(posedge clk);
        rst = 0;
        $display("✅ Reset released at time %0t", $time);
    end

    // AXI4-Lite interface
    axi4_lite_if axi_if (clk, rst);

    // DUT: Register_Block
    Register_Block register_block (
        .clk(clk),
        .rst(rst),
        .axi(axi_if.slave)
    );

    // AXI Master Model for testing
    axi_master_model master_model (
        .clk(clk),
        .rst(rst),
        .axi(axi_if.master)
    );

    // Test framework
    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;

    // Write task
    task write_register(input [31:0] addr, input [31:0] data, input string test_name);
        $display("\n🧪 Test %0d: %s", ++test_count, test_name);
        $display("   Writing 0x%08X to address 0x%08X", data, addr);
        master_model.write_transaction(addr, data);
        
        if (master_model.last_bresp == 2'b00) begin
            $display("   ✅ PASS: Write completed successfully");
            pass_count++;
        end else begin
            $display("   ❌ FAIL: Write failed with BRESP=0x%01X", master_model.last_bresp);
            fail_count++;
        end
    endtask

    // Read task  
    task read_register(input [31:0] addr, input [31:0] expected_data, input string test_name);
        logic [31:0] read_data;
        
        $display("\n🧪 Test %0d: %s", ++test_count, test_name);
        $display("   Reading from address 0x%08X, expecting 0x%08X", addr, expected_data);
        
        master_model.read_transaction(addr, read_data);
        
        if (master_model.last_rresp == 2'b00) begin
            if (read_data == expected_data) begin
                $display("   ✅ PASS: Read data matches expected value");
                pass_count++;
            end else begin
                $display("   ❌ FAIL: Data mismatch - Expected: 0x%08X, Got: 0x%08X", expected_data, read_data);
                fail_count++;
            end
        end else begin
            $display("   ❌ FAIL: Read failed with RRESP=0x%01X", master_model.last_rresp);
            fail_count++;
        end
    endtask

    // Main test sequence
    initial begin
        $display("🚀 Starting Register_Block Unit Test");
        $display("=======================================");
        
        // Wait for reset release
        wait (!rst);
        repeat(20) @(posedge clk);
        
        // Test sequence - REG_TEST register access
        write_register(ADDR_REG_TEST_0, 32'h12345678, "REG_TEST_0 Write");
        read_register(ADDR_REG_TEST_0, 32'h12345678, "REG_TEST_0 Read");
        
        write_register(ADDR_REG_TEST_1, 32'hDEADBEEF, "REG_TEST_1 Write");
        read_register(ADDR_REG_TEST_1, 32'hDEADBEEF, "REG_TEST_1 Read");
        
        write_register(ADDR_REG_TEST_2, 32'hCAFEBABE, "REG_TEST_2 Write");
        read_register(ADDR_REG_TEST_2, 32'hCAFEBABE, "REG_TEST_2 Read");
        
        write_register(ADDR_REG_TEST_3, 32'hFEEDFACE, "REG_TEST_3 Write");
        read_register(ADDR_REG_TEST_3, 32'hFEEDFACE, "REG_TEST_3 Read");
        
        // Test data patterns
        write_register(ADDR_REG_TEST_0, 32'h00000000, "Zero Pattern Write");
        read_register(ADDR_REG_TEST_0, 32'h00000000, "Zero Pattern Read");
        
        write_register(ADDR_REG_TEST_0, 32'hFFFFFFFF, "All Ones Write");
        read_register(ADDR_REG_TEST_0, 32'hFFFFFFFF, "All Ones Read");
        
        write_register(ADDR_REG_TEST_0, 32'hAAAA5555, "Alternating Pattern Write");
        read_register(ADDR_REG_TEST_0, 32'hAAAA5555, "Alternating Pattern Read");
        
        // Final results
        repeat(50) @(posedge clk);
        
        $display("\n📊 Register_Block Unit Test Results");
        $display("======================================");
        $display("Total Tests: %0d", test_count);
        $display("Passed: %0d", pass_count);
        $display("Failed: %0d", fail_count);
        
        if (fail_count == 0) begin
            $display("🎉 ALL TESTS PASSED - Register_Block Unit Test SUCCESSFUL");
        end else begin
            $display("❌ %0d TESTS FAILED - Register_Block Unit Test FAILED", fail_count);
        end
        
        $finish;
    end

    // Waveform generation
    initial begin
        $dumpfile("register_block_unit_test.mxd");
        $dumpvars(0, register_block_unit_test);
    end

    // Timeout watchdog
    initial begin
        #50us;
        $display("❌ GLOBAL TIMEOUT: Test suite did not complete");
        $finish;
    end

endmodule

// AXI Master Model for testing Register_Block
module axi_master_model (
    input logic clk,
    input logic rst,
    axi4_lite_if.master axi
);

    // Transaction status
    logic [1:0] last_bresp;
    logic [1:0] last_rresp;
    
    // Write transaction task
    task write_transaction(input [31:0] addr, input [31:0] data);
        // Address phase
        axi.awvalid <= 1;
        axi.awaddr <= addr;
        axi.awprot <= 3'b000;
        
        // Data phase
        axi.wvalid <= 1;
        axi.wdata <= data;
        axi.wstrb <= 4'hF;
        
        axi.bready <= 1;
        
        // Wait for address handshake
        do @(posedge clk); while (!axi.awready);
        axi.awvalid <= 0;
        
        // Wait for data handshake
        do @(posedge clk); while (!axi.wready);
        axi.wvalid <= 0;
        
        // Wait for response
        do @(posedge clk); while (!axi.bvalid);
        last_bresp = axi.bresp;
        @(posedge clk);
        axi.bready <= 0;
        
        $display("MASTER: Write 0x%08X to 0x%08X, BRESP=0x%01X", data, addr, last_bresp);
    endtask
    
    // Read transaction task
    task read_transaction(input [31:0] addr, output [31:0] data);
        // Address phase
        axi.arvalid <= 1;
        axi.araddr <= addr;
        axi.arprot <= 3'b000;
        axi.rready <= 1;
        
        // Wait for address handshake
        do @(posedge clk); while (!axi.arready);
        axi.arvalid <= 0;
        
        // Wait for data response
        do @(posedge clk); while (!axi.rvalid);
        data = axi.rdata;
        last_rresp = axi.rresp;
        @(posedge clk);
        axi.rready <= 0;
        
        $display("MASTER: Read 0x%08X from 0x%08X, RRESP=0x%01X", data, addr, last_rresp);
    endtask
    
    // Initialize signals
    initial begin
        axi.awvalid <= 0;
        axi.awaddr <= 0;
        axi.awprot <= 0;
        axi.wvalid <= 0;
        axi.wdata <= 0;
        axi.wstrb <= 0;
        axi.bready <= 0;
        axi.arvalid <= 0;
        axi.araddr <= 0;
        axi.arprot <= 0;
        axi.rready <= 0;
        last_bresp <= 0;
        last_rresp <= 0;
    end

endmodule