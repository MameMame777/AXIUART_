// Clean UVM Testbench for UART-AXI Bridge
// Purpose: Minimal, working UVM testbench
// Date: August 11, 2025

`timescale 1ns / 1ps

// Import UVM and packages
import uvm_pkg::*;
`include "uvm_macros.svh"
import uart_axi_test_pkg::*;

module uart_axi_tb_clean;

    // Clock and reset generation
    logic clk = 0;
    logic rst = 1;
    
    // Clock generation
    initial begin
        forever #4ns clk = ~clk; // 125MHz
    end
    
    // Reset generation
    initial begin
        rst = 1;
        #100ns;
        rst = 0;
    end
    
    // Interface instances
    axi4_lite_if #(.ADDR_WIDTH(8), .DATA_WIDTH(32)) axi_if (.aclk(clk), .aresetn(~rst));
    uart_if uart_if_inst (.clk(clk), .reset(rst));
    
    // UART signals for DUT connection (to avoid interface driving conflicts)
    logic uart_rxd_to_dut;  // Signal driven by testbench, fed to DUT
    logic uart_cts_n_to_dut; // Signal driven by testbench, fed to DUT
    
    // Connect DUT outputs to interface for UVM monitoring
    assign uart_if_inst.rx = uart_rxd_to_dut;      // For UVM driver to control
    assign uart_if_inst.cts_n = uart_cts_n_to_dut; // For UVM driver to control
    
    // Initialize UART input signals
    initial begin
        uart_rxd_to_dut = 1'b1;   // UART idle high
        uart_cts_n_to_dut = 1'b0; // Clear to send (active low)
    end
    
    // DUT instantiation
    Uart_Axi4_Bridge #(
        .SYS_CLK_FREQ(125000000),
        .BAUD_RATE(115200),
        .DATA_BITS(8),
        .STOP_BITS(1),
        .PARITY("NONE"),
        .FLOW_CONTROL(1),
        .FIFO_DEPTH(64),
        .ADDR_WIDTH(8),
        .DATA_WIDTH(32)
    ) dut (
        .sys_clk(clk),
        .sys_rst(rst),
        
        // AXI4-Lite interface - direct connection
        .s_axi_awaddr(axi_if.awaddr),
        .s_axi_awprot(axi_if.awprot),
        .s_axi_awvalid(axi_if.awvalid),
        .s_axi_awready(axi_if.awready),
        .s_axi_wdata(axi_if.wdata),
        .s_axi_wstrb(axi_if.wstrb),
        .s_axi_wvalid(axi_if.wvalid),
        .s_axi_wready(axi_if.wready),
        .s_axi_bresp(axi_if.bresp),
        .s_axi_bvalid(axi_if.bvalid),
        .s_axi_bready(axi_if.bready),
        .s_axi_araddr(axi_if.araddr),
        .s_axi_arprot(axi_if.arprot),
        .s_axi_arvalid(axi_if.arvalid),
        .s_axi_arready(axi_if.arready),
        .s_axi_rdata(axi_if.rdata),
        .s_axi_rresp(axi_if.rresp),
        .s_axi_rvalid(axi_if.rvalid),
        .s_axi_rready(axi_if.rready),
        
        // UART interface - proper signal direction
        .uart_txd(uart_if_inst.tx),      // DUT output -> interface
        .uart_rxd(uart_rxd_to_dut),      // Testbench -> DUT input  
        .uart_rts_n(uart_if_inst.rts_n), // DUT output -> interface
        .uart_cts_n(uart_cts_n_to_dut)   // Testbench -> DUT input
    );
    
    // Initialize interfaces
    initial begin
        // Set interface defaults
        axi_if.awaddr = 0;
        axi_if.awprot = 0;
        axi_if.awvalid = 0;
        axi_if.wdata = 0;
        axi_if.wstrb = 0;
        axi_if.wvalid = 0;
        axi_if.bready = 0;
        axi_if.araddr = 0;
        axi_if.arprot = 0;
        axi_if.arvalid = 0;
        axi_if.rready = 0;
        
        uart_if_inst.rx = 1;
        uart_if_inst.cts_n = 0;
    end
    
    // UVM testbench initialization
    initial begin
        // Register interfaces with UVM config database
        uvm_config_db#(virtual axi4_lite_if)::set(null, "uvm_test_top.*", "axi_vif", axi_if);
        uvm_config_db#(virtual uart_if)::set(null, "uvm_test_top.*", "uart_vif", uart_if_inst);
        
        // Run the test
        run_test("uart_axi_basic_test");
    end
    
    // Basic test monitoring
    initial begin
        `uvm_info("TB_TOP", "Clean UVM Testbench Starting", UVM_LOW)
        
        wait(!rst);
        `uvm_info("TB_TOP", "Reset deasserted", UVM_LOW)
        
        #10us; // Run for 10 microseconds
        `uvm_info("TB_TOP", "Test completed successfully", UVM_LOW)
        $finish;
    end

endmodule
