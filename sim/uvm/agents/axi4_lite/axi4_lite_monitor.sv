`timescale 1ns / 1ps

// AXI4-Lite Monitor for UART-AXI4 Bridge UVM Testbench
class axi4_lite_monitor extends uvm_monitor;
    
    `uvm_component_utils(axi4_lite_monitor)
    
    // Configuration
    uart_axi4_env_config cfg;
    
    // Virtual interface
    virtual axi4_lite_if vif;
    
    // Analysis port for sending collected transactions
    uvm_analysis_port #(axi4_lite_transaction) item_collected_port;
    // Alias for environment compatibility
    uvm_analysis_port #(axi4_lite_transaction) analysis_port;
    
    // Coverage collection
    uart_axi4_coverage coverage;
    
    // Internal variables
    bit monitor_enabled = 1;
    
    function new(string name = "axi4_lite_monitor", uvm_component parent = null);
        super.new(name, parent);
        item_collected_port = new("item_collected_port", this);
        analysis_port = item_collected_port;  // Alias
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        if (!uvm_config_db#(uart_axi4_env_config)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("AXI4_LITE_MONITOR", "Failed to get configuration object")
        end
        
        // Get virtual interface
        if (!uvm_config_db#(virtual axi4_lite_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("AXI4_LITE_MONITOR", "Failed to get virtual interface")
        end
        
        // Get coverage collector
        if (!uvm_config_db#(uart_axi4_coverage)::get(this, "", "coverage", coverage)) begin
            `uvm_info("AXI4_LITE_MONITOR", "Coverage collector not found - coverage disabled", UVM_LOW)
        end
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        fork
            collect_write_transactions();
            collect_read_transactions();
        join
    endtask
    
    // Monitor write transactions
    virtual task collect_write_transactions();
        axi4_lite_transaction tr;
        
        forever begin
            if (!monitor_enabled) begin
                @(posedge vif.aclk);
                continue;
            end
            
            // Wait for write address valid
            @(posedge vif.aclk);
            if (vif.awvalid && vif.awready) begin
                tr = axi4_lite_transaction::type_id::create("axi_write_tr");
                tr.trans_type = AXI_WRITE;
                tr.is_write = 1;
                tr.addr = vif.awaddr;
                tr.timestamp = $realtime;
                
                `uvm_info("AXI4_LITE_MONITOR", $sformatf("Write address: 0x%08X", tr.addr), UVM_DEBUG)
                
                // Wait for write data
                fork : write_data_collection
                    begin
                        @(posedge vif.aclk);
                        wait (vif.wvalid && vif.wready);
                        tr.data = vif.wdata;
                        tr.wdata = vif.wdata;
                        tr.strb = vif.wstrb;
                        tr.wstrb = vif.wstrb;
                        `uvm_info("AXI4_LITE_MONITOR", $sformatf("Write data: 0x%08X, strb=0x%X", 
                                  tr.data, tr.strb), UVM_DEBUG)
                    end
                    begin
                        repeat (cfg.axi_timeout_cycles) @(posedge vif.aclk);
                        `uvm_error("AXI4_LITE_MONITOR", "Timeout waiting for write data")
                    end
                join_any
                disable write_data_collection;
                
                // Wait for write response
                fork : write_response_collection
                    begin
                        @(posedge vif.aclk);
                        wait (vif.bvalid && vif.bready);
                        tr.resp = vif.bresp;
                        tr.bresp = vif.bresp;
                        tr.completed = 1;
                        `uvm_info("AXI4_LITE_MONITOR", $sformatf("Write response: 0x%X", tr.resp), UVM_DEBUG)
                    end
                    begin
                        repeat (cfg.axi_timeout_cycles) @(posedge vif.aclk);
                        `uvm_error("AXI4_LITE_MONITOR", "Timeout waiting for write response")
                        tr.completed = 0;
                    end
                join_any
                disable write_response_collection;
                
                // Send collected transaction
                `uvm_info("AXI4_LITE_MONITOR", $sformatf("Write complete: ADDR=0x%08X, DATA=0x%08X, RESP=0x%X", 
                          tr.addr, tr.data, tr.resp), UVM_MEDIUM)
                
                item_collected_port.write(tr);
                
                // Collect coverage
                if (coverage != null) begin
                    coverage.sample_axi_transaction(tr);
                end
            end
        end
    endtask
    
    // Monitor read transactions
    virtual task collect_read_transactions();
        axi4_lite_transaction tr;
        
        forever begin
            if (!monitor_enabled) begin
                @(posedge vif.aclk);
                continue;
            end
            
            // Wait for read address valid
            @(posedge vif.aclk);
            if (vif.arvalid && vif.arready) begin
                tr = axi4_lite_transaction::type_id::create("axi_read_tr");
                tr.trans_type = AXI_READ;
                tr.is_write = 0;
                tr.addr = vif.araddr;
                tr.timestamp = $realtime;
                
                `uvm_info("AXI4_LITE_MONITOR", $sformatf("Read address: 0x%08X", tr.addr), UVM_DEBUG)
                
                // Wait for read response
                fork : read_response_collection
                    begin
                        @(posedge vif.aclk);
                        wait (vif.rvalid && vif.rready);
                        tr.data = vif.rdata;
                        tr.rdata = vif.rdata;
                        tr.resp = vif.rresp;
                        tr.rresp = vif.rresp;
                        tr.completed = 1;
                        `uvm_info("AXI4_LITE_MONITOR", $sformatf("Read response: DATA=0x%08X, RESP=0x%X", 
                                  tr.data, tr.resp), UVM_DEBUG)
                    end
                    begin
                        repeat (cfg.axi_timeout_cycles) @(posedge vif.aclk);
                        `uvm_error("AXI4_LITE_MONITOR", "Timeout waiting for read response")
                        tr.completed = 0;
                    end
                join_any
                disable read_response_collection;
                
                // Send collected transaction
                `uvm_info("AXI4_LITE_MONITOR", $sformatf("Read complete: ADDR=0x%08X, DATA=0x%08X, RESP=0x%X", 
                          tr.addr, tr.data, tr.resp), UVM_MEDIUM)
                
                item_collected_port.write(tr);
                
                // Collect coverage
                if (coverage != null) begin
                    coverage.sample_axi_transaction(tr);
                end
            end
        end
    endtask
    
    // Monitor protocol compliance
    virtual task monitor_protocol_compliance();
        // Check for protocol violations
        forever begin
            @(posedge vif.aclk);
            
            if (!vif.aresetn) continue;
            
            // Check write address channel
            if (vif.awvalid) begin
                // AWVALID should remain high until AWREADY
                check_valid_stable(vif.awvalid, vif.awready, "AWVALID");
                
                // Address should be stable when AWVALID is high
                // Temporarily disabled due to SVA automatic variable issue
                // if ($past(vif.awvalid) && vif.awvalid && !vif.awready) begin
                //     if (vif.awaddr !== $past(vif.awaddr)) begin
                //         `uvm_error("AXI4_LITE_MONITOR", "AWADDR changed while AWVALID high and AWREADY low")
                //     end
                // end
            end
            
            // Check write data channel
            if (vif.wvalid) begin
                check_valid_stable(vif.wvalid, vif.wready, "WVALID");
                
                // Temporarily disabled due to SVA automatic variable issue
                // if ($past(vif.wvalid) && vif.wvalid && !vif.wready) begin
                //     if (vif.wdata !== $past(vif.wdata) || vif.wstrb !== $past(vif.wstrb)) begin
                //         `uvm_error("AXI4_LITE_MONITOR", "WDATA/WSTRB changed while WVALID high and WREADY low")
                //     end
                // end
            end
            
            // Check read address channel
            if (vif.arvalid) begin
                check_valid_stable(vif.arvalid, vif.arready, "ARVALID");
                
                // Temporarily disabled due to SVA automatic variable issue
                // if ($past(vif.arvalid) && vif.arvalid && !vif.arready) begin
                //     if (vif.araddr !== $past(vif.araddr)) begin
                //         `uvm_error("AXI4_LITE_MONITOR", "ARADDR changed while ARVALID high and ARREADY low")
                //     end
                // end
            end
            
            // Check response channels
            check_valid_ready_relationship(vif.bvalid, vif.bready, "B channel");
            check_valid_ready_relationship(vif.rvalid, vif.rready, "R channel");
        end
    endtask
    
    // Helper function to check valid signal stability
    virtual function void check_valid_stable(bit valid, bit ready, string signal_name);
        static bit prev_valid = 0;
        
        if (prev_valid && !valid && !ready) begin
            `uvm_error("AXI4_LITE_MONITOR", $sformatf("%s deasserted before corresponding READY", signal_name))
        end
        
        prev_valid = valid;
    endfunction
    
    // Helper function to check valid-ready relationship
    virtual function void check_valid_ready_relationship(bit valid, bit ready, string channel_name);
        if (ready && !valid) begin
            `uvm_warning("AXI4_LITE_MONITOR", $sformatf("%s: READY high without VALID", channel_name))
        end
    endfunction
    
    // Control functions
    virtual function void enable_monitor();
        monitor_enabled = 1;
        `uvm_info("AXI4_LITE_MONITOR", "Monitor enabled", UVM_LOW)
    endfunction
    
    virtual function void disable_monitor();
        monitor_enabled = 0;
        `uvm_info("AXI4_LITE_MONITOR", "Monitor disabled", UVM_LOW)
    endfunction

endclass