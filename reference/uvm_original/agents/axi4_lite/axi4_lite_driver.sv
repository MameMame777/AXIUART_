// AXI4-Lite UVM Driver
// Target Board: Zybo Z7-20
// Date: July 26, 2025
// Description: UVM driver for AXI4-Lite master interface

`ifndef AXI4_LITE_DRIVER_SV
`define AXI4_LITE_DRIVER_SV

class axi4_lite_driver extends uvm_driver #(axi4_lite_transaction);
    
    // Virtual interface
    virtual axi4_lite_if vif;
    
    // UVM registration
    `uvm_component_utils(axi4_lite_driver)
    
    // Constructor
    function new(string name = "axi4_lite_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual axi4_lite_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("NOVIF", "Virtual interface not found")
        end
    endfunction
    
    // Run phase
    virtual task run_phase(uvm_phase phase);
        axi4_lite_transaction tr;
        
        // Initialize signals
        reset_signals();
        
        forever begin
            seq_item_port.get_next_item(tr);
            `uvm_info("AXI4_LITE_DRV", $sformatf("Driving transaction: %s", tr.convert2string()), UVM_MEDIUM)
            
            case (tr.trans_type)
                axi4_lite_transaction::WRITE: drive_write(tr);
                axi4_lite_transaction::READ:  drive_read(tr);
            endcase
            
            seq_item_port.item_done();
        end
    endtask
    
    // Reset all signals to idle state
    task reset_signals();
        @(posedge vif.aclk);
        vif.awaddr  <= '0;
        vif.awprot  <= '0;
        vif.awvalid <= 1'b0;
        vif.wdata   <= '0;
        vif.wstrb   <= '0;
        vif.wvalid  <= 1'b0;
        vif.bready  <= 1'b0;
        vif.araddr  <= '0;
        vif.arprot  <= '0;
        vif.arvalid <= 1'b0;
        vif.rready  <= 1'b0;
    endtask
    
    // Drive write transaction
    task drive_write(axi4_lite_transaction tr);
        fork
            // Address write channel
            begin
                repeat(tr.addr_delay) @(posedge vif.aclk);
                vif.awaddr  <= tr.addr;
                vif.awprot  <= tr.prot;
                vif.awvalid <= 1'b1;
                
                wait(vif.awready);
                @(posedge vif.aclk);
                vif.awvalid <= 1'b0;
            end
            
            // Write data channel
            begin
                repeat(tr.data_delay) @(posedge vif.aclk);
                vif.wdata  <= tr.data;
                vif.wstrb  <= tr.strb;
                vif.wvalid <= 1'b1;
                
                wait(vif.wready);
                @(posedge vif.aclk);
                vif.wvalid <= 1'b0;
            end
        join
        
        // Write response channel
        repeat(tr.resp_delay) @(posedge vif.aclk);
        vif.bready <= 1'b1;
        
        wait(vif.bvalid);
        tr.resp = vif.bresp;
        tr.error = (vif.bresp != AXI_RESP_OKAY);
        
        @(posedge vif.aclk);
        vif.bready <= 1'b0;
        
        `uvm_info("AXI4_LITE_DRV", $sformatf("Write complete - Addr: 0x%02h, Data: 0x%08h, Resp: %2b", 
                 tr.addr, tr.data, tr.resp), UVM_HIGH)
    endtask
    
    // Drive read transaction
    task drive_read(axi4_lite_transaction tr);
        // Address read channel
        repeat(tr.addr_delay) @(posedge vif.aclk);
        vif.araddr  <= tr.addr;
        vif.arprot  <= tr.prot;
        vif.arvalid <= 1'b1;
        
        wait(vif.arready);
        @(posedge vif.aclk);
        vif.arvalid <= 1'b0;
        
        // Read data channel
        repeat(tr.resp_delay) @(posedge vif.aclk);
        vif.rready <= 1'b1;
        
        wait(vif.rvalid);
        tr.rdata = vif.rdata;
        tr.resp = vif.rresp;
        tr.error = (vif.rresp != AXI_RESP_OKAY);
        
        @(posedge vif.aclk);
        vif.rready <= 1'b0;
        
        `uvm_info("AXI4_LITE_DRV", $sformatf("Read complete - Addr: 0x%02h, Data: 0x%08h, Resp: %2b", 
                 tr.addr, tr.rdata, tr.resp), UVM_HIGH)
    endtask
    
    // Wait for reset deassertion
    task wait_for_reset();
        wait(!vif.aresetn);
        wait(vif.aresetn);
        repeat(5) @(posedge vif.aclk);
    endtask

endclass

`endif // AXI4_LITE_DRIVER_SV
