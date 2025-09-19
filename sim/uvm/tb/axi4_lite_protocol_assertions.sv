`timescale 1ns / 1ps

import uvm_pkg::*;
`include "uvm_macros.svh"

// AXI4-Lite Protocol Assertions
// SystemVerilog assertions to validate AXI4-Lite protocol compliance

module axi4_lite_protocol_assertions #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32
) (
    input logic clk,
    input logic rst,
    axi4_lite_if.monitor axi_if
);

    // AXI4-Lite Write Address Channel Assertions
    
    // AWxxx: Write address channel signals must be stable when AWVALID is high and AWREADY is low
    property awvalid_stable;
        @(posedge clk) disable iff (rst)
        (axi_if.awvalid && !axi_if.awready) |=> $stable(axi_if.awvalid);
    endproperty
    assert_awvalid_stable: assert property (awvalid_stable)
        else `uvm_error("AXI_ASSERT", "AWVALID not stable during handshake")
    
    property awaddr_stable;
        @(posedge clk) disable iff (rst)
        (axi_if.awvalid && !axi_if.awready) |=> $stable(axi_if.awaddr);
    endproperty
    assert_awaddr_stable: assert property (awaddr_stable)
        else `uvm_error("AXI_ASSERT", "AWADDR not stable during handshake")
    
    property awprot_stable;
        @(posedge clk) disable iff (rst)
        (axi_if.awvalid && !axi_if.awready) |=> $stable(axi_if.awprot);
    endproperty
    assert_awprot_stable: assert property (awprot_stable)
        else `uvm_error("AXI_ASSERT", "AWPROT not stable during handshake")
    
    // AXI4-Lite Write Data Channel Assertions
    
    // Wxxx: Write data channel signals must be stable when WVALID is high and WREADY is low
    property wvalid_stable;
        @(posedge clk) disable iff (rst)
        (axi_if.wvalid && !axi_if.wready) |=> $stable(axi_if.wvalid);
    endproperty
    assert_wvalid_stable: assert property (wvalid_stable)
        else `uvm_error("AXI_ASSERT", "WVALID not stable during handshake")
    
    property wdata_stable;
        @(posedge clk) disable iff (rst)
        (axi_if.wvalid && !axi_if.wready) |=> $stable(axi_if.wdata);
    endproperty
    assert_wdata_stable: assert property (wdata_stable)
        else `uvm_error("AXI_ASSERT", "WDATA not stable during handshake")
    
    property wstrb_stable;
        @(posedge clk) disable iff (rst)
        (axi_if.wvalid && !axi_if.wready) |=> $stable(axi_if.wstrb);
    endproperty
    assert_wstrb_stable: assert property (wstrb_stable)
        else `uvm_error("AXI_ASSERT", "WSTRB not stable during handshake")
    
    // Write strobe alignment check
    property wstrb_valid;
        @(posedge clk) disable iff (rst)
        axi_if.wvalid |-> (axi_if.wstrb != 4'b0000);
    endproperty
    assert_wstrb_valid: assert property (wstrb_valid)
        else `uvm_error("AXI_ASSERT", "WSTRB cannot be all zeros when WVALID is high")
    
    // AXI4-Lite Write Response Channel Assertions
    
    // Bxxx: Write response channel signals must be stable when BVALID is high and BREADY is low
    property bvalid_stable;
        @(posedge clk) disable iff (rst)
        (axi_if.bvalid && !axi_if.bready) |=> $stable(axi_if.bvalid);
    endproperty
    assert_bvalid_stable: assert property (bvalid_stable)
        else `uvm_error("AXI_ASSERT", "BVALID not stable during handshake")
    
    property bresp_stable;
        @(posedge clk) disable iff (rst)
        (axi_if.bvalid && !axi_if.bready) |=> $stable(axi_if.bresp);
    endproperty
    assert_bresp_stable: assert property (bresp_stable)
        else `uvm_error("AXI_ASSERT", "BRESP not stable during handshake")
    
    // AXI4-Lite Read Address Channel Assertions
    
    // ARxxx: Read address channel signals must be stable when ARVALID is high and ARREADY is low
    property arvalid_stable;
        @(posedge clk) disable iff (rst)
        (axi_if.arvalid && !axi_if.arready) |=> $stable(axi_if.arvalid);
    endproperty
    assert_arvalid_stable: assert property (arvalid_stable)
        else `uvm_error("AXI_ASSERT", "ARVALID not stable during handshake")
    
    property araddr_stable;
        @(posedge clk) disable iff (rst)
        (axi_if.arvalid && !axi_if.arready) |=> $stable(axi_if.araddr);
    endproperty
    assert_araddr_stable: assert property (araddr_stable)
        else `uvm_error("AXI_ASSERT", "ARADDR not stable during handshake")
    
    property arprot_stable;
        @(posedge clk) disable iff (rst)
        (axi_if.arvalid && !axi_if.arready) |=> $stable(axi_if.arprot);
    endproperty
    assert_arprot_stable: assert property (arprot_stable)
        else `uvm_error("AXI_ASSERT", "ARPROT not stable during handshake")
    
    // AXI4-Lite Read Data Channel Assertions
    
    // Rxxx: Read data channel signals must be stable when RVALID is high and RREADY is low
    property rvalid_stable;
        @(posedge clk) disable iff (rst)
        (axi_if.rvalid && !axi_if.rready) |=> $stable(axi_if.rvalid);
    endproperty
    assert_rvalid_stable: assert property (rvalid_stable)
        else `uvm_error("AXI_ASSERT", "RVALID not stable during handshake")
    
    property rdata_stable;
        @(posedge clk) disable iff (rst)
        (axi_if.rvalid && !axi_if.rready) |=> $stable(axi_if.rdata);
    endproperty
    assert_rdata_stable: assert property (rdata_stable)
        else `uvm_error("AXI_ASSERT", "RDATA not stable during handshake")
    
    property rresp_stable;
        @(posedge clk) disable iff (rst)
        (axi_if.rvalid && !axi_if.rready) |=> $stable(axi_if.rresp);
    endproperty
    assert_rresp_stable: assert property (rresp_stable)
        else `uvm_error("AXI_ASSERT", "RRESP not stable during handshake")
    
    // AXI4-Lite Protocol Compliance Assertions
    
    // Reset behavior - all VALID signals should be low after reset
    property reset_awvalid;
        @(posedge clk)
        rst |-> !axi_if.awvalid;
    endproperty
    assert_reset_awvalid: assert property (reset_awvalid)
        else `uvm_error("AXI_ASSERT", "AWVALID not low after reset")
    
    property reset_wvalid;
        @(posedge clk)
        rst |-> !axi_if.wvalid;
    endproperty
    assert_reset_wvalid: assert property (reset_wvalid)
        else `uvm_error("AXI_ASSERT", "WVALID not low after reset")
    
    property reset_bready;
        @(posedge clk)
        rst |-> !axi_if.bready;
    endproperty
    assert_reset_bready: assert property (reset_bready)
        else `uvm_error("AXI_ASSERT", "BREADY not low after reset")
    
    property reset_arvalid;
        @(posedge clk)
        rst |-> !axi_if.arvalid;
    endproperty
    assert_reset_arvalid: assert property (reset_arvalid)
        else `uvm_error("AXI_ASSERT", "ARVALID not low after reset")
    
    property reset_rready;
        @(posedge clk)
        rst |-> !axi_if.rready;
    endproperty
    assert_reset_rready: assert property (reset_rready)
        else `uvm_error("AXI_ASSERT", "RREADY not low after reset")
    
    // Handshake completion assertions
    
    // Write address handshake - once started, must complete
    property aw_handshake_complete;
        @(posedge clk) disable iff (rst)
        $rose(axi_if.awvalid) |-> ##[0:1000] (axi_if.awvalid && axi_if.awready);
    endproperty
    assert_aw_handshake_complete: assert property (aw_handshake_complete)
        else `uvm_error("AXI_ASSERT", "Write address handshake did not complete within timeout")
    
    // Write data handshake - once started, must complete
    property w_handshake_complete;
        @(posedge clk) disable iff (rst)
        $rose(axi_if.wvalid) |-> ##[0:1000] (axi_if.wvalid && axi_if.wready);
    endproperty
    assert_w_handshake_complete: assert property (w_handshake_complete)
        else `uvm_error("AXI_ASSERT", "Write data handshake did not complete within timeout")
    
    // Write response handshake - once started, must complete
    property b_handshake_complete;
        @(posedge clk) disable iff (rst)
        $rose(axi_if.bvalid) |-> ##[0:1000] (axi_if.bvalid && axi_if.bready);
    endproperty
    assert_b_handshake_complete: assert property (b_handshake_complete)
        else `uvm_error("AXI_ASSERT", "Write response handshake did not complete within timeout")
    
    // Read address handshake - once started, must complete
    property ar_handshake_complete;
        @(posedge clk) disable iff (rst)
        $rose(axi_if.arvalid) |-> ##[0:1000] (axi_if.arvalid && axi_if.arready);
    endproperty
    assert_ar_handshake_complete: assert property (ar_handshake_complete)
        else `uvm_error("AXI_ASSERT", "Read address handshake did not complete within timeout")
    
    // Read data handshake - once started, must complete
    property r_handshake_complete;
        @(posedge clk) disable iff (rst)
        $rose(axi_if.rvalid) |-> ##[0:1000] (axi_if.rvalid && axi_if.rready);
    endproperty
    assert_r_handshake_complete: assert property (r_handshake_complete)
        else `uvm_error("AXI_ASSERT", "Read data handshake did not complete within timeout")
    
    // Address alignment assertions for AXI4-Lite
    property awaddr_aligned;
        @(posedge clk) disable iff (rst)
        axi_if.awvalid |-> (axi_if.awaddr[1:0] == 2'b00);
    endproperty
    assert_awaddr_aligned: assert property (awaddr_aligned)
        else `uvm_error("AXI_ASSERT", "AWADDR not 32-bit aligned")
    
    property araddr_aligned;
        @(posedge clk) disable iff (rst)
        axi_if.arvalid |-> (axi_if.araddr[1:0] == 2'b00);
    endproperty
    assert_araddr_aligned: assert property (araddr_aligned)
        else `uvm_error("AXI_ASSERT", "ARADDR not 32-bit aligned")
    
    // Coverage for protocol events
    covergroup axi_protocol_coverage @(posedge clk);
        option.per_instance = 1;
        
        awvalid_cp: coverpoint axi_if.awvalid iff (!rst);
        awready_cp: coverpoint axi_if.awready iff (!rst);
        wvalid_cp: coverpoint axi_if.wvalid iff (!rst);
        wready_cp: coverpoint axi_if.wready iff (!rst);
        bvalid_cp: coverpoint axi_if.bvalid iff (!rst);
        bready_cp: coverpoint axi_if.bready iff (!rst);
        arvalid_cp: coverpoint axi_if.arvalid iff (!rst);
        arready_cp: coverpoint axi_if.arready iff (!rst);
        rvalid_cp: coverpoint axi_if.rvalid iff (!rst);
        rready_cp: coverpoint axi_if.rready iff (!rst);
        
        // Handshake crosses
        aw_handshake: cross awvalid_cp, awready_cp;
        w_handshake: cross wvalid_cp, wready_cp;
        b_handshake: cross bvalid_cp, bready_cp;
        ar_handshake: cross arvalid_cp, arready_cp;
        r_handshake: cross rvalid_cp, rready_cp;
        
        // Response types
        bresp_cp: coverpoint axi_if.bresp iff (axi_if.bvalid && !rst) {
            bins OKAY = {2'b00};
            bins EXOKAY = {2'b01};
            bins SLVERR = {2'b10};
            bins DECERR = {2'b11};
        }
        
        rresp_cp: coverpoint axi_if.rresp iff (axi_if.rvalid && !rst) {
            bins OKAY = {2'b00};
            bins EXOKAY = {2'b01};
            bins SLVERR = {2'b10};
            bins DECERR = {2'b11};
        }
    endgroup
    
    axi_protocol_coverage cov_inst = new();
    
    // Monitor for assertion summary
    initial begin
        `uvm_info("AXI_ASSERT", "AXI4-Lite protocol assertions instantiated", UVM_LOW)
    end
    
endmodule