// AXI4-Lite UVM Monitor
// Target Board: Zybo Z7-20
// Date: July 26, 2025
// Description: UVM monitor for AXI4-Lite interface

`ifndef AXI4_LITE_MONITOR_SV
`define AXI4_LITE_MONITOR_SV

class axi4_lite_monitor extends uvm_monitor;
    
    // Virtual interface
    virtual axi4_lite_if vif;
    
    // Analysis port
    uvm_analysis_port #(axi4_lite_transaction) ap;
    
    // Coverage
    axi4_lite_transaction tr_cov;
    
    // Coverage group
    covergroup axi4_lite_cg;
        option.per_instance = 1;
        
        trans_type_cp: coverpoint tr_cov.trans_type {
            bins read  = {axi4_lite_transaction::READ};
            bins write = {axi4_lite_transaction::WRITE};
        }
        
        addr_cp: coverpoint tr_cov.addr {
            bins control_reg   = {ADDR_CONTROL_REG};
            bins status_reg    = {ADDR_STATUS_REG};
            bins tx_data_reg   = {ADDR_TX_DATA_REG};
            bins rx_data_reg   = {ADDR_RX_DATA_REG};
            bins fifo_status   = {ADDR_FIFO_STATUS};
            bins error_status  = {ADDR_ERROR_STATUS};
            bins fifo_thresh   = {ADDR_FIFO_THRESH};
        }
        
        strb_cp: coverpoint tr_cov.strb {
            bins full_write  = {4'b1111};
            bins byte0_only  = {4'b0001};
            bins byte1_only  = {4'b0010};
            bins byte2_only  = {4'b0100};
            bins byte3_only  = {4'b1000};
            bins lower_half  = {4'b0011};
            bins upper_half  = {4'b1100};
            bins no_strb     = {4'b0000};
        }
        
        resp_cp: coverpoint tr_cov.resp {
            bins okay    = {AXI_RESP_OKAY};
            bins slverr  = {AXI_RESP_SLVERR};
            bins decerr  = {AXI_RESP_DECERR};
        }
        
        // Cross coverage
        trans_addr_cross: cross trans_type_cp, addr_cp;
        write_strb_cross: cross trans_type_cp, strb_cp {
            ignore_bins read_with_strb = binsof(trans_type_cp.read) && 
                                        !binsof(strb_cp.no_strb);
        }
    endgroup
    
    // UVM registration
    `uvm_component_utils(axi4_lite_monitor)
    
    // Constructor
    function new(string name = "axi4_lite_monitor", uvm_component parent = null);
        super.new(name, parent);
        ap = new("ap", this);
        axi4_lite_cg = new();
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
        fork
            monitor_writes();
            monitor_reads();
        join
    endtask
    
    // Monitor write transactions
    task monitor_writes();
        axi4_lite_transaction tr;
        bit [ADDR_WIDTH-1:0] addr;
        bit [2:0] prot;
        bit [DATA_WIDTH-1:0] data;
        bit [(DATA_WIDTH/8)-1:0] strb;
        bit [1:0] resp;
        
        forever begin
            // Wait for write address valid
            @(posedge vif.aclk);
            if (vif.awvalid && vif.awready && vif.wvalid && vif.wready) begin
                // Capture address and data simultaneously
                addr = vif.awaddr;
                prot = vif.awprot;
                data = vif.wdata;
                strb = vif.wstrb;
                
                // Wait for write response
                wait(vif.bvalid && vif.bready);
                resp = vif.bresp;
                
                // Create transaction
                tr = axi4_lite_transaction::type_id::create("axi4_lite_tr");
                tr.trans_type = axi4_lite_transaction::WRITE;
                tr.addr = addr;
                tr.data = data;
                tr.strb = strb;
                tr.prot = prot;
                tr.resp = resp;
                tr.error = (resp != AXI_RESP_OKAY);
                
                // Send to analysis port and update coverage
                ap.write(tr);
                tr_cov = tr;
                axi4_lite_cg.sample();
                
                `uvm_info("AXI4_LITE_MON", $sformatf("Monitored write: %s", tr.convert2string()), UVM_HIGH)
            end
        end
    endtask
    
    // Monitor read transactions
    task monitor_reads();
        axi4_lite_transaction tr;
        bit [ADDR_WIDTH-1:0] addr;
        bit [2:0] prot;
        bit [DATA_WIDTH-1:0] rdata;
        bit [1:0] resp;
        
        forever begin
            // Wait for read address valid
            @(posedge vif.aclk);
            if (vif.arvalid && vif.arready) begin
                addr = vif.araddr;
                prot = vif.arprot;
                
                // Wait for read data
                wait(vif.rvalid && vif.rready);
                rdata = vif.rdata;
                resp = vif.rresp;
                
                // Create transaction
                tr = axi4_lite_transaction::type_id::create("axi4_lite_tr");
                tr.trans_type = axi4_lite_transaction::READ;
                tr.addr = addr;
                tr.prot = prot;
                tr.rdata = rdata;
                tr.resp = resp;
                tr.error = (resp != AXI_RESP_OKAY);
                tr.strb = 4'b0000;  // No strobes for reads
                
                // Send to analysis port and update coverage
                ap.write(tr);
                tr_cov = tr;
                axi4_lite_cg.sample();
                
                `uvm_info("AXI4_LITE_MON", $sformatf("Monitored read: %s", tr.convert2string()), UVM_HIGH)
            end
        end
    endtask
    
    // Report phase
    virtual function void report_phase(uvm_phase phase);
        `uvm_info("AXI4_LITE_MON", $sformatf("AXI4-Lite Coverage: %.2f%%", axi4_lite_cg.get_coverage()), UVM_LOW)
    endfunction

endclass

`endif // AXI4_LITE_MONITOR_SV
