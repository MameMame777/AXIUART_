`timescale 1ns / 1ps

/*
 * AXI4-Lite Interface Definition
 * 
 * Purpose: SystemVerilog interface for AXI4-Lite protocol
 * Features:
 * - Master and Slave modports
 * - Complete AXI4-Lite signal set
 * - Clock and reset synchronization
 */

interface axi4_lite_if (
    input logic clk,
    input logic rst
);

    // Write address channel
    logic [31:0] awaddr;
    logic [2:0]  awprot;
    logic        awvalid;
    logic        awready;

    // Write data channel
    logic [31:0] wdata;
    logic [3:0]  wstrb;
    logic        wvalid;
    logic        wready;

    // Write response channel
    logic [1:0]  bresp;
    logic        bvalid;
    logic        bready;

    // Read address channel
    logic [31:0] araddr;
    logic [2:0]  arprot;
    logic        arvalid;
    logic        arready;

    // Read data channel
    logic [31:0] rdata;
    logic [1:0]  rresp;
    logic        rvalid;
    logic        rready;

    // Master modport (for AXI Master)
    modport master (
        output awaddr, awprot, awvalid,
        input  awready,
        output wdata, wstrb, wvalid,
        input  wready,
        input  bresp, bvalid,
        output bready,
        output araddr, arprot, arvalid,
        input  arready,
        input  rdata, rresp, rvalid,
        output rready
    );

    // Slave modport (for AXI Slave)
    modport slave (
        input  awaddr, awprot, awvalid,
        output awready,
        input  wdata, wstrb, wvalid,
        output wready,
        output bresp, bvalid,
        input  bready,
        input  araddr, arprot, arvalid,
        output arready,
        output rdata, rresp, rvalid,
        input  rready
    );

    // Monitor modport (for verification)
    modport monitor (
        input awaddr, awprot, awvalid, awready,
        input wdata, wstrb, wvalid, wready,
        input bresp, bvalid, bready,
        input araddr, arprot, arvalid, arready,
        input rdata, rresp, rvalid, rready
    );

endinterface : axi4_lite_if