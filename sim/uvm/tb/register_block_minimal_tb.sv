`timescale 1ns / 1ps

// Minimal Register Block Testbench Top
// Purpose: Test only core Register_Block functionality without complexity

module register_block_minimal_tb;

    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // Clock and reset
    logic clk;
    logic rst;
    
    // AXI4-Lite interface
    axi4_lite_if axi_if(clk, rst);
    
    // DUT instantiation
    Register_Block #(
        .ADDR_WIDTH(32),
        .DATA_WIDTH(32),
        .BASE_ADDR(32'h0000_1000)
    ) dut (
        .clk(clk),
        .rst(rst),
        .axi(axi_if.slave),
        
        // Bridge interface - minimal connections
        // bridge_enable removed
        .bridge_reset_stats(),
        .baud_div_config(),
        .timeout_config(),
        .debug_mode(),
        
        // Status inputs - tie to known values
        .bridge_busy(1'b0),
        .error_code(8'h00),
        .tx_count(16'h0000),
        .rx_count(16'h0000),
        .fifo_status(8'h00)
    );
    
    // Clock generation - 100MHz
    initial begin
        clk = 0;
        forever #5ns clk = ~clk;
    end
    
    // Reset sequence
    initial begin
        rst = 1;
        repeat(10) @(posedge clk);
        rst = 0;
        `uvm_info("TB", "Reset released", UVM_LOW)
    end
    
    // Initialize interface signals
    initial begin
        // Initialize master signals
        axi_if.awvalid = 1'b0;
        axi_if.awaddr = 32'h0;
        axi_if.awprot = 3'b000;
        
        axi_if.wvalid = 1'b0;
        axi_if.wdata = 32'h0;
        axi_if.wstrb = 4'b0000;
        
        axi_if.bready = 1'b0;
        
        axi_if.arvalid = 1'b0;
        axi_if.araddr = 32'h0;
        axi_if.arprot = 3'b000;
        
        axi_if.rready = 1'b0;
        
        // Store interface in config DB immediately
        uvm_config_db#(virtual axi4_lite_if)::set(null, "*", "axi_vif", axi_if);
        
        // Run the test at time 0 (UVM requirement)
        run_test("register_block_minimal_test");
    end
    
    // Timeout watchdog
    initial begin
        #1_000_000; // 1ms timeout
        `uvm_fatal("TIMEOUT", "Test timed out!")
        $finish;
    end

endmodule