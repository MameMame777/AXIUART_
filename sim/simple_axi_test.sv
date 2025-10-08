`timescale 1ns / 1ps

/*
 * Simple AXI4-Lite Basic Operation Test (No UVM)
 * 
 * Purpose: Verify fundamental AXI Master + Register_Block functionality
 *          WITHOUT UVM complexity or DSIM licensing issues
 */

module simple_axi_test;

    // Clock and reset
    logic clk = 0;
    logic rst = 1;
    
    // Clock generation (125MHz)
    always #4ns clk = ~clk;
    
    // Reset generation  
    initial begin
        rst = 1;
        #100ns;
        rst = 0;
        $display("Reset released at time %0t", $time);
    end
    
    // AXI4-Lite interface
    axi4_lite_if axi_if (clk, rst);
    
    // AXI Master signals
    logic [7:0]  axi_cmd;
    logic [31:0] axi_addr;
    logic [7:0]  axi_write_data [0:63];
    logic        axi_start_transaction;
    logic        axi_transaction_done;
    logic [7:0]  axi_status;
    logic [7:0]  axi_read_data [0:63];
    logic [5:0]  axi_read_data_count;
    
    // DUT: AXI Master
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
    
    // DUT: Register Block
    Register_Block #(
        .ADDR_WIDTH(32),
        .DATA_WIDTH(32),
        .BASE_ADDR(32'h0000_1000)
    ) register_block (
        .clk(clk),
        .rst(rst),
        .axi(axi_if.slave),
        .bridge_enable(),
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
    
    // Test procedure
    initial begin
        // Initialize signals
        axi_cmd = 8'h00;
        axi_addr = 32'h00000000;
        axi_start_transaction = 0;
        
        // Initialize write data array
        for (int i = 0; i < 64; i++) begin
            axi_write_data[i] = 8'h00;
        end
        
        // Wait for reset
        wait (!rst);
        #200ns;
        
        $display("=== Starting AXI Basic Operation Test ===");
        
        // Test 1: Write to REG_TEST_0
        $display("Test 1: Writing 0x12345678 to REG_TEST_0 (0x00001020)");
        axi_cmd = 8'h20;  // Write command (size=32-bit, len=0, rw=0)
        axi_addr = 32'h00001020;
        axi_write_data[0] = 8'h78;  // LSB first
        axi_write_data[1] = 8'h56;
        axi_write_data[2] = 8'h34;
        axi_write_data[3] = 8'h12;  // MSB
        
        // Start transaction
        axi_start_transaction = 1;
        #20ns;
        axi_start_transaction = 0;
        
        // Wait for completion with timeout
        fork
            begin
                wait (axi_transaction_done);
                $display("✅ Write transaction completed, status = 0x%02X", axi_status);
            end
            begin
                #10us;
                $display("❌ Write transaction timeout");
                $finish;
            end
        join_any
        disable fork;
        
        if (axi_status != 8'h00) begin
            $display("❌ Write failed with status 0x%02X", axi_status);
            $finish;
        end
        
        #500ns;
        
        // Test 2: Read from REG_TEST_0
        $display("Test 2: Reading from REG_TEST_0 (0x00001020)");
        axi_cmd = 8'hA0;  // Read command (size=32-bit, len=0, rw=1)
        axi_addr = 32'h00001020;
        
        axi_start_transaction = 1;
        #20ns;
        axi_start_transaction = 0;
        
        // Wait for completion
        fork
            begin
                wait (axi_transaction_done);
                $display("✅ Read transaction completed, status = 0x%02X", axi_status);
                $display("Read data count = %d", axi_read_data_count);
            end
            begin
                #10us;
                $display("❌ Read transaction timeout");
                $finish;
            end
        join_any
        disable fork;
        
        if (axi_status != 8'h00) begin
            $display("❌ Read failed with status 0x%02X", axi_status);
        end else if (axi_read_data_count >= 4) begin
            logic [31:0] read_value = {axi_read_data[3], axi_read_data[2], axi_read_data[1], axi_read_data[0]};
            $display("Read value = 0x%08X", read_value);
            if (read_value == 32'h12345678) begin
                $display("🎉 SUCCESS: Write/Read cycle worked correctly!");
            end else begin
                $display("❌ FAILURE: Expected 0x12345678, got 0x%08X", read_value);
            end
        end else begin
            $display("❌ FAILURE: Insufficient read data returned (count=%d)", axi_read_data_count);
        end
        
        #1000ns;
        $display("=== AXI Basic Operation Test Completed ===");
        $finish;
    end
    
    // Monitor AXI signals for debugging
    always @(posedge clk) begin
        if (axi_if.awvalid && axi_if.awready) begin
            $display("DEBUG: AW handshake - addr=0x%08X", axi_if.awaddr);
        end
        if (axi_if.wvalid && axi_if.wready) begin
            $display("DEBUG: W handshake - data=0x%08X, strb=0x%X", axi_if.wdata, axi_if.wstrb);
        end
        if (axi_if.bvalid && axi_if.bready) begin
            $display("DEBUG: B handshake - resp=0x%X", axi_if.bresp);
        end
        if (axi_if.arvalid && axi_if.arready) begin
            $display("DEBUG: AR handshake - addr=0x%08X", axi_if.araddr);
        end
        if (axi_if.rvalid && axi_if.rready) begin
            $display("DEBUG: R handshake - data=0x%08X, resp=0x%X", axi_if.rdata, axi_if.rresp);
        end
    end
    
    // Timeout watchdog
    initial begin
        #100us;
        $display("❌ GLOBAL TIMEOUT: Test did not complete");
        $finish;
    end

endmodule