`timescale 1ns / 1ps

// AXI4-Lite Driver for UART-AXI4 Bridge UVM Testbench
// Note: This driver is primarily for active slave emulation if needed
// The DUT is typically the AXI master, so this driver may be unused
class axi4_lite_driver extends uvm_driver #(axi4_lite_transaction);
    
    `uvm_component_utils(axi4_lite_driver)
    
    // Configuration
    uart_axi4_env_config cfg;
    
    // Virtual interface
    virtual axi4_lite_if vif;
    
    function new(string name = "axi4_lite_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        if (!uvm_config_db#(uart_axi4_env_config)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("AXI4_LITE_DRIVER", "Failed to get configuration object")
        end
        
        // Get virtual interface
        if (!uvm_config_db#(virtual axi4_lite_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("AXI4_LITE_DRIVER", "Failed to get virtual interface")
        end
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        axi4_lite_transaction req;
        
        // Initialize AXI slave signals
        initialize_slave_signals();
        
        forever begin
            seq_item_port.get_next_item(req);
            
            `uvm_info("AXI4_LITE_DRIVER", $sformatf("Processing AXI transaction: %s, ADDR=0x%08X", 
                      req.trans_type.name(), req.addr), UVM_MEDIUM)
            
            case (req.trans_type)
                AXI_WRITE: drive_write_response(req);
                AXI_READ:  drive_read_response(req);
                default: `uvm_error("AXI4_LITE_DRIVER", "Unknown transaction type")
            endcase
            
            seq_item_port.item_done();
        end
    endtask
    
    // Initialize AXI slave interface signals
    virtual task initialize_slave_signals();
        vif.awready <= 1'b1;  // Ready to accept write addresses
        vif.wready  <= 1'b1;  // Ready to accept write data
        vif.arready <= 1'b1;  // Ready to accept read addresses
        vif.bvalid  <= 1'b0;  // No write response initially
        vif.bresp   <= 2'b00; // OKAY response
        vif.rvalid  <= 1'b0;  // No read data initially
        vif.rdata   <= 32'h0; // Zero read data
        vif.rresp   <= 2'b00; // OKAY response
        
        `uvm_info("AXI4_LITE_DRIVER", "AXI slave signals initialized", UVM_LOW)
    endtask
    
    // Drive write response (slave behavior)
    virtual task drive_write_response(axi4_lite_transaction tr);
        bit timeout_occurred = 0;
        // Wait for address and data phases to complete
        @(posedge vif.aclk);
        fork : write_response_wait
            begin
                wait (vif.awvalid && vif.awready && vif.wvalid && vif.wready);
            end
            begin
                #1ms; // 1ms timeout
                timeout_occurred = 1;
                `uvm_error("AXI4_LITE_DRIVER", "Write response wait timeout (1ms)")
            end
        join_any
        disable fork;
        if (timeout_occurred) return;
        
        // Add configurable delay before response
        repeat ($urandom_range(cfg.min_axi_response_delay, cfg.max_axi_response_delay)) begin
            @(posedge vif.aclk);
        end
        
        // Drive write response
        vif.bvalid <= 1'b1;
        vif.bresp  <= tr.resp;  // Use response from transaction
        
        // Wait for response handshake
        @(posedge vif.aclk);
        timeout_occurred = 0;
        fork : bready_wait
            begin
                wait (vif.bready);
            end
            begin
                #1ms;
                timeout_occurred = 1;
                `uvm_error("AXI4_LITE_DRIVER", "BREADY wait timeout (1ms)")
            end
        join_any
        disable fork;
        
        // Deassert response
        @(posedge vif.aclk);
        vif.bvalid <= 1'b0;
        vif.bresp  <= 2'b00;
        
        `uvm_info("AXI4_LITE_DRIVER", $sformatf("Write response completed: RESP=0x%X", tr.resp), UVM_DEBUG)
    endtask
    
    // Drive read response (slave behavior)
    virtual task drive_read_response(axi4_lite_transaction tr);
        bit timeout_occurred = 0;
        // Wait for address phase to complete
        @(posedge vif.aclk);
        fork : read_address_wait
            begin
                wait (vif.arvalid && vif.arready);
            end
            begin
                #1ms;
                timeout_occurred = 1;
                `uvm_error("AXI4_LITE_DRIVER", "Read address wait timeout (1ms)")
            end
        join_any
        disable fork;
        if (timeout_occurred) return;
        
        // Add configurable delay before response
        repeat ($urandom_range(cfg.min_axi_response_delay, cfg.max_axi_response_delay)) begin
            @(posedge vif.aclk);
        end
        
        // Drive read response
        vif.rvalid <= 1'b1;
        vif.rdata  <= tr.data;  // Use data from transaction
        vif.rresp  <= tr.resp;  // Use response from transaction
        
        // Wait for response handshake
        @(posedge vif.aclk);
        timeout_occurred = 0;
        fork : rready_wait
            begin
                wait (vif.rready);
            end
            begin
                #1ms;
                timeout_occurred = 1;
                `uvm_error("AXI4_LITE_DRIVER", "RREADY wait timeout (1ms)")
            end
        join_any
        disable fork;
        
        // Deassert response
        @(posedge vif.aclk);
        vif.rvalid <= 1'b0;
        vif.rdata  <= 32'h0;
        vif.rresp  <= 2'b00;
        
        `uvm_info("AXI4_LITE_DRIVER", $sformatf("Read response completed: DATA=0x%08X, RESP=0x%X", 
                  tr.data, tr.resp), UVM_DEBUG)
    endtask
    
    // Memory model for realistic slave behavior
    virtual task memory_model_mode();
        logic [31:0] memory [logic [31:0]];
        logic [31:0] addr, data;
        logic [3:0] strb;
        logic [1:0] resp;
        
        forever begin
            fork
                // Handle write transactions
                begin
                    @(posedge vif.aclk);
                    if (vif.awvalid && vif.awready && vif.wvalid && vif.wready) begin
                        addr = vif.awaddr;
                        data = vif.wdata;
                        strb = vif.wstrb;
                        
                        // Simulate memory write with byte strobes
                        if (strb[0]) memory[addr][7:0]   = data[7:0];
                        if (strb[1]) memory[addr][15:8]  = data[15:8];
                        if (strb[2]) memory[addr][23:16] = data[23:16];
                        if (strb[3]) memory[addr][31:24] = data[31:24];
                        
                        // Generate appropriate response
                        resp = (addr % 4 == 0) ? 2'b00 : 2'b10; // OKAY or SLVERR for alignment
                        
                        // Drive response after delay
                        repeat ($urandom_range(1, 5)) @(posedge vif.aclk);
                        vif.bvalid <= 1'b1;
                        vif.bresp <= resp;
                        
                        @(posedge vif.aclk);
                        fork : mem_bready_wait
                            begin
                                wait (vif.bready);
                            end
                            begin
                                #1ms;
                                `uvm_error("AXI4_LITE_DRIVER", "Memory write BREADY timeout (1ms)")
                            end
                        join_any
                        disable fork;
                        
                        @(posedge vif.aclk);
                        vif.bvalid <= 1'b0;
                        
                        `uvm_info("AXI4_LITE_DRIVER", $sformatf("Memory write: [0x%08X] = 0x%08X", addr, data), UVM_DEBUG)
                    end
                end
                
                // Handle read transactions
                begin
                    @(posedge vif.aclk);
                    if (vif.arvalid && vif.arready) begin
                        addr = vif.araddr;
                        
                        // Read from memory
                        if (memory.exists(addr)) begin
                            data = memory[addr];
                            resp = 2'b00; // OKAY
                        end else begin
                            data = 32'hDEADBEEF; // Default data for uninitialized locations
                            resp = 2'b00; // OKAY (could be SLVERR for real slave)
                        end
                        
                        // Generate response after delay
                        repeat ($urandom_range(1, 5)) @(posedge vif.aclk);
                        vif.rvalid <= 1'b1;
                        vif.rdata <= data;
                        vif.rresp <= resp;
                        
                        @(posedge vif.aclk);
                        fork : mem_rready_wait
                            begin
                                wait (vif.rready);
                            end
                            begin
                                #1ms;
                                `uvm_error("AXI4_LITE_DRIVER", "Memory read RREADY timeout (1ms)")
                            end
                        join_any
                        disable fork;
                        
                        @(posedge vif.aclk);
                        vif.rvalid <= 1'b0;
                        vif.rdata <= 32'h0;
                        
                        `uvm_info("AXI4_LITE_DRIVER", $sformatf("Memory read: [0x%08X] => 0x%08X", addr, data), UVM_DEBUG)
                    end
                end
            join
        end
    endtask

endclass