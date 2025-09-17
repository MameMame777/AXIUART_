// AXI4-Lite Interface Definition
// Target Board: Zybo Z7-20
// Date: July 26, 2025
// Description: SystemVerilog interface for AXI4-Lite with MXD waveform dump support

`ifndef AXI4_LITE_IF_SV
`define AXI4_LITE_IF_SV

interface axi4_lite_if(input logic aclk, input logic aresetn);
    
    // AXI4-Lite Write Address Channel
    logic [31:0]  awaddr;
    logic [2:0]   awprot;
    logic         awvalid;
    logic         awready;
    
    // AXI4-Lite Write Data Channel
    logic [31:0]  wdata;
    logic [3:0]   wstrb;
    logic         wvalid;
    logic         wready;
    
    // AXI4-Lite Write Response Channel
    logic [1:0]   bresp;
    logic         bvalid;
    logic         bready;
    
    // AXI4-Lite Read Address Channel
    logic [31:0]  araddr;
    logic [2:0]   arprot;
    logic         arvalid;
    logic         arready;
    
    // AXI4-Lite Read Data Channel
    logic [31:0]  rdata;
    logic [1:0]   rresp;
    logic         rvalid;
    logic         rready;
    
    // Master clocking block
    clocking master_cb @(posedge aclk);
        default input #1 output #1;
        
        // Write channels
        output awaddr, awprot, awvalid;
        input  awready;
        output wdata, wstrb, wvalid;
        input  wready;
        input  bresp, bvalid;
        output bready;
        
        // Read channels
        output araddr, arprot, arvalid;
        input  arready;
        input  rdata, rresp, rvalid;
        output rready;
    endclocking
    
    // Slave clocking block
    clocking slave_cb @(posedge aclk);
        default input #1 output #1;
        
        // Write channels
        input  awaddr, awprot, awvalid;
        output awready;
        input  wdata, wstrb, wvalid;
        output wready;
        output bresp, bvalid;
        input  bready;
        
        // Read channels
        input  araddr, arprot, arvalid;
        output arready;
        output rdata, rresp, rvalid;
        input  rready;
    endclocking
    
    // Monitor clocking block
    clocking monitor_cb @(posedge aclk);
        default input #1;
        
        input awaddr, awprot, awvalid, awready;
        input wdata, wstrb, wvalid, wready;
        input bresp, bvalid, bready;
        input araddr, arprot, arvalid, arready;
        input rdata, rresp, rvalid, rready;
    endclocking
    
    // Modports
    modport master (clocking master_cb, input aclk, aresetn);
    modport slave  (clocking slave_cb, input aclk, aresetn);
    modport monitor (clocking monitor_cb, input aclk, aresetn);
    
    // Assertions for protocol compliance
    property aw_handshake;
        @(posedge aclk) disable iff (!aresetn)
        awvalid && !awready |=> awvalid;
    endproperty
    
    property w_handshake;
        @(posedge aclk) disable iff (!aresetn)
        wvalid && !wready |=> wvalid;
    endproperty
    
    property b_handshake;
        @(posedge aclk) disable iff (!aresetn)
        bvalid && !bready |=> bvalid;
    endproperty
    
    property ar_handshake;
        @(posedge aclk) disable iff (!aresetn)
        arvalid && !arready |=> arvalid;
    endproperty
    
    property r_handshake;
        @(posedge aclk) disable iff (!aresetn)
        rvalid && !rready |=> rvalid;
    endproperty
    
    // Bind assertions
    assert property (aw_handshake) else $error("AW handshake violation");
    assert property (w_handshake) else $error("W handshake violation");
    assert property (b_handshake) else $error("B handshake violation");
    assert property (ar_handshake) else $error("AR handshake violation");
    assert property (r_handshake) else $error("R handshake violation");
    
    // Task methods for easy AXI transactions
    task axi_write(input [ADDR_WIDTH-1:0] addr, input [DATA_WIDTH-1:0] data);
        @(posedge clk);
        awaddr = addr;
        awvalid = 1'b1;
        wdata = data;
        wstrb = 4'hF;
        wvalid = 1'b1;
        bready = 1'b1;
        
        wait(awready && wready);
        @(posedge clk);
        awvalid = 1'b0;
        wvalid = 1'b0;
        
        wait(bvalid);
        @(posedge clk);
        bready = 1'b0;
    endtask
    
    task axi_read(input [ADDR_WIDTH-1:0] addr, output [DATA_WIDTH-1:0] data);
        @(posedge clk);
        araddr = addr;
        arvalid = 1'b1;
        rready = 1'b1;
        
        wait(arready);
        @(posedge clk);
        arvalid = 1'b0;
        
        wait(rvalid);
        data = rdata;
        @(posedge clk);
        rready = 1'b0;
    endtask
    
    // MXD waveform dump support
    `ifdef DSIM
        initial begin
            $dumpfile("axi4_lite_waves.mxd");
            $dumpvars(0, axi4_lite_if);
        end
    `endif

endinterface

`endif // AXI4_LITE_IF_SV
