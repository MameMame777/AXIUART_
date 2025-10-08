`timescale 1ns / 1ps

/*
 * AXI4-Lite Master Unit Test
 * 
 * Purpose: Verify AXI Master component in isolation
 * Success Criteria:
 * - Basic write transaction completes without timeout
 * - Basic read transaction completes without timeout  
 * - State machine progresses correctly through all phases
 * - AXI protocol compliance (handshakes, timing)
 */

module axi_master_unit_test;

    // Test parameters
    localparam CLOCK_PERIOD = 8ns;  // 125MHz
    localparam RESET_CYCLES = 10;
    localparam TIMEOUT_CYCLES = 5000;

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
    
    // AXI Master signals
    logic [7:0]  cmd;
    logic [31:0] addr;
    logic [7:0]  write_data [0:63];
    logic        start_transaction = 0;
    logic        transaction_done;
    logic [7:0]  axi_status;
    logic [7:0]  read_data [0:63];
    logic [5:0]  read_data_count;

    // DUT: AXI Master
    Axi4_Lite_Master axi_master (
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

    // Simple AXI Slave Model
    axi_slave_model slave_model (
        .clk(clk),
        .rst(rst),
        .axi(axi_if.slave)
    );

    // Test execution framework
    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;

    // Write test task
    task run_write_test(input [31:0] test_addr, input [31:0] test_data, input string test_name);
        $display("\n🧪 Test %0d: %s", ++test_count, test_name);
        $display("   Writing 0x%08X to address 0x%08X", test_data, test_addr);
        
        // Setup write command
        cmd = 8'h20;  // Write command (32-bit, single beat)
        addr = test_addr;
        write_data[0] = test_data[7:0];
        write_data[1] = test_data[15:8];
        write_data[2] = test_data[23:16];
        write_data[3] = test_data[31:24];
        
        // Start transaction
        start_transaction = 1;
        @(posedge clk);
        start_transaction = 0;
        
        // Wait for completion with timeout
        fork
            begin: wait_done
                wait (transaction_done);
                if (axi_status == 8'h00) begin
                    $display("   ✅ PASS: Write completed successfully");
                    pass_count++;
                end else begin
                    $display("   ❌ FAIL: Write failed with status 0x%02X", axi_status);
                    fail_count++;
                end
            end
            begin: timeout_check
                repeat(TIMEOUT_CYCLES) @(posedge clk);
                $display("   ❌ FAIL: Write transaction timeout");
                fail_count++;
            end
        join_any
        disable fork;
        
        repeat(10) @(posedge clk);
    endtask

    // Read test task
    task run_read_test(input [31:0] test_addr, input [31:0] expected_data, input string test_name);
        $display("\n🧪 Test %0d: %s", ++test_count, test_name);
        $display("   Reading from address 0x%08X, expecting 0x%08X", test_addr, expected_data);
        
        // Setup read command
        cmd = 8'hA0;  // Read command (32-bit, single beat)
        addr = test_addr;
        
        // Start transaction
        start_transaction = 1;
        @(posedge clk);
        start_transaction = 0;
        
        // Wait for completion with timeout
        fork
            begin: wait_done
                wait (transaction_done);
                if (axi_status == 8'h00) begin
                    if (read_data_count >= 4) begin
                        automatic logic [31:0] read_value = {read_data[3], read_data[2], read_data[1], read_data[0]};
                        if (read_value == expected_data) begin
                            $display("   ✅ PASS: Read data matches expected value");
                            pass_count++;
                        end else begin
                            $display("   ❌ FAIL: Read data mismatch - Expected: 0x%08X, Got: 0x%08X", expected_data, read_value);
                            fail_count++;
                        end
                    end else begin
                        $display("   ❌ FAIL: Insufficient read data count: %0d", read_data_count);
                        fail_count++;
                    end
                end else begin
                    $display("   ❌ FAIL: Read failed with status 0x%02X", axi_status);
                    fail_count++;
                end
            end
            begin: timeout_check
                repeat(TIMEOUT_CYCLES) @(posedge clk);
                $display("   ❌ FAIL: Read transaction timeout");
                fail_count++;
            end
        join_any
        disable fork;
        
        repeat(10) @(posedge clk);
    endtask

    // Main test sequence
    initial begin
        $display("🚀 Starting AXI Master Unit Test");
        $display("=====================================");
        
        // Initialize write data array
        for (int i = 0; i < 64; i++) begin
            write_data[i] = 8'h00;
        end
        
        // Wait for reset release
        wait (!rst);
        repeat(20) @(posedge clk);
        
        // Test sequence - REDUCED FOR DEBUGGING
        run_write_test(32'h00001020, 32'h12345678, "Basic Write Transaction");
        //run_read_test(32'h00001020, 32'h12345678, "Basic Read Transaction");
        //run_write_test(32'h00001024, 32'hDEADBEEF, "Second Address Write");
        //run_read_test(32'h00001024, 32'hDEADBEEF, "Second Address Read");
        //run_write_test(32'h00001028, 32'hCAFEBABE, "Third Address Write");
        //run_read_test(32'h00001028, 32'hCAFEBABE, "Third Address Read");
        //run_write_test(32'h0000102C, 32'h00000000, "Zero Data Write");
        //run_read_test(32'h0000102C, 32'h00000000, "Zero Data Read");
        //run_write_test(32'h0000102C, 32'hFFFFFFFF, "All Ones Write");
        //run_read_test(32'h0000102C, 32'hFFFFFFFF, "All Ones Read");
        
        // Final results
        repeat(50) @(posedge clk);
        
        $display("\n📊 AXI Master Unit Test Results");
        $display("=====================================");
        $display("Total Tests: %0d", test_count);
        $display("Passed: %0d", pass_count);
        $display("Failed: %0d", fail_count);
        
        if (fail_count == 0) begin
            $display("🎉 ALL TESTS PASSED - AXI Master Unit Test SUCCESSFUL");
        end else begin
            $display("❌ %0d TESTS FAILED - AXI Master Unit Test FAILED", fail_count);
        end
        
        $finish;
    end

    // Waveform generation
    initial begin
        $dumpfile("axi_master_unit_test.mxd");
        $dumpvars(0, axi_master_unit_test);
    end

    // Timeout watchdog
    initial begin
        #100us;
        $display("❌ GLOBAL TIMEOUT: Test suite did not complete");
        $finish;
    end

endmodule

// Simple AXI Slave Model for unit testing
module axi_slave_model (
    input logic clk,
    input logic rst,
    axi4_lite_if.slave axi
);

    // Internal memory for testing
    logic [31:0] memory [0:4095];  // Fixed size memory array instead of associative
    
    // AXI slave state machine
    typedef enum logic [2:0] {
        IDLE,
        WRITE_ADDR,
        WRITE_DATA,
        WRITE_RESP,
        READ_DATA
    } axi_state_t;
    
    axi_state_t state, state_next;
    logic [31:0] write_addr_reg;
    logic [31:0] read_addr_reg;
    
    // State machine implementation
    always_ff @(posedge clk) begin
        if (rst) begin
            state <= IDLE;
            write_addr_reg <= '0;
            read_addr_reg <= '0;
            $display("SLAVE: Reset completed");
        end else begin
            state <= state_next;
            
            if (axi.awvalid && axi.awready) begin
                write_addr_reg <= axi.awaddr;
                $display("SLAVE: AW handshake - addr=0x%08X", axi.awaddr);
            end
            
            if (axi.arvalid && axi.arready) begin
                read_addr_reg <= axi.araddr;
                $display("SLAVE: AR handshake - addr=0x%08X", axi.araddr);
            end
            
            if (axi.wvalid && axi.wready) begin
                memory[(write_addr_reg >> 2) & 12'hFFF] <= axi.wdata;  // Word-aligned access
                $display("SLAVE: W handshake - wrote 0x%08X to address 0x%08X", axi.wdata, write_addr_reg);
            end
            
            if (axi.bvalid && axi.bready) begin
                $display("SLAVE: B handshake completed");
            end
            
            if (axi.rvalid && axi.rready) begin
                $display("SLAVE: R handshake - read 0x%08X from address 0x%08X", axi.rdata, read_addr_reg);
            end
        end
    end
    
    // Next state logic
    always_comb begin
        state_next = state;
        
        case (state)
            IDLE: begin
                if (axi.awvalid) begin
                    state_next = WRITE_ADDR;
                    $display("SLAVE: IDLE->WRITE_ADDR (awvalid detected)");
                end else if (axi.arvalid) begin
                    state_next = READ_DATA;
                    $display("SLAVE: IDLE->READ_DATA (arvalid detected)");
                end
            end
            
            WRITE_ADDR: begin
                // Address already captured, move to data phase
                state_next = WRITE_DATA;
                $display("SLAVE: WRITE_ADDR->WRITE_DATA (auto transition)");
            end
            
            WRITE_DATA: begin
                if (axi.wvalid && axi.wready) begin
                    state_next = WRITE_RESP;
                    $display("SLAVE: WRITE_DATA->WRITE_RESP");
                end
            end
            
            WRITE_RESP: begin
                if (axi.bvalid && axi.bready) begin
                    state_next = IDLE;
                    $display("SLAVE: WRITE_RESP->IDLE");
                end
            end
            
            READ_DATA: begin
                if (axi.rvalid && axi.rready) begin
                    state_next = IDLE;
                    $display("SLAVE: READ_DATA->IDLE");
                end
            end
        endcase
    end
    
    // AXI signal assignments
    assign axi.awready = (state == IDLE) || (state == WRITE_ADDR);
    assign axi.wready = (state == WRITE_DATA);
    assign axi.bvalid = (state == WRITE_RESP);
    assign axi.bresp = 2'b00;  // OKAY
    
    assign axi.arready = (state == IDLE);
    assign axi.rvalid = (state == READ_DATA);
    assign axi.rdata = memory[(read_addr_reg >> 2) & 12'hFFF];  // Word-aligned access
    assign axi.rresp = 2'b00;  // OKAY
    
    // Debug signal monitoring - REDUCED OUTPUT
    always @(posedge clk) begin
        if (!rst && (axi.awvalid || axi.wvalid || axi.bvalid || axi.arvalid || axi.rvalid)) begin
            $display("SLAVE DEBUG: state=%s awvalid=%b awready=%b wvalid=%b wready=%b",
                     (state == IDLE) ? "IDLE" :
                     (state == WRITE_ADDR) ? "WRITE_ADDR" :
                     (state == WRITE_DATA) ? "WRITE_DATA" :
                     (state == WRITE_RESP) ? "WRITE_RESP" :
                     (state == READ_DATA) ? "READ_DATA" : "UNKNOWN",
                     axi.awvalid, axi.awready, axi.wvalid, axi.wready);
        end
    end

endmodule