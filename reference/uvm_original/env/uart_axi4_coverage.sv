// UART-AXI4 Bridge Coverage Collector
// Target Board: Zybo Z7-20
// Date: July 26, 2025
// Description: UVM coverage collector for UART-AXI4 bridge

`ifndef UART_AXI4_COVERAGE_SV
`define UART_AXI4_COVERAGE_SV

class uart_axi4_coverage extends uvm_subscriber #(axi4_lite_transaction);
    
    // Analysis exports for different transaction types
    uvm_analysis_export #(axi4_lite_transaction) axi_export;
    uvm_analysis_export #(uart_transaction) uart_tx_export;
    uvm_analysis_export #(uart_transaction) uart_rx_export;
    
    // Transaction items for coverage
    axi4_lite_transaction axi_tr;
    uart_transaction uart_tx_tr;
    uart_transaction uart_rx_tr;
    
    // Coverage groups
    covergroup axi4_lite_cg;
        option.per_instance = 1;
        option.name = "axi4_lite_coverage";
        
        // Address coverage
        addr_cp: coverpoint axi_tr.addr {
            bins control_reg   = {ADDR_CONTROL_REG};
            bins status_reg    = {ADDR_STATUS_REG};
            bins tx_data_reg   = {ADDR_TX_DATA_REG};
            bins rx_data_reg   = {ADDR_RX_DATA_REG};
            bins fifo_status   = {ADDR_FIFO_STATUS};
            bins error_status  = {ADDR_ERROR_STATUS};
            bins fifo_thresh   = {ADDR_FIFO_THRESH};
            bins invalid_addr  = default;
        }
        
        // Transaction type coverage
        trans_type_cp: coverpoint axi_tr.trans_type {
            bins read  = {axi4_lite_transaction::READ};
            bins write = {axi4_lite_transaction::WRITE};
        }
        
        // Write strobe coverage
        strb_cp: coverpoint axi_tr.strb {
            bins full_write    = {4'b1111};
            bins byte_write    = {4'b0001, 4'b0010, 4'b0100, 4'b1000};
            bins half_write    = {4'b0011, 4'b1100};
            bins invalid_strb  = {4'b0101, 4'b1010, 4'b0110, 4'b1001};
            bins no_strb       = {4'b0000};
        }
        
        // Response coverage
        resp_cp: coverpoint axi_tr.resp {
            bins okay    = {AXI_RESP_OKAY};
            bins slverr  = {AXI_RESP_SLVERR};
            bins decerr  = {AXI_RESP_DECERR};
        }
        
        // Data patterns for TX register
        tx_data_cp: coverpoint axi_tr.data[7:0] iff (axi_tr.addr == ADDR_TX_DATA_REG && axi_tr.trans_type == axi4_lite_transaction::WRITE) {
            bins ascii_ctrl    = {[8'h00:8'h1F]};
            bins ascii_print   = {[8'h20:8'h7E]};
            bins ascii_ext     = {[8'h7F:8'hFF]};
            bins zero          = {8'h00};
            bins max           = {8'hFF};
        }
        
        // Cross coverage
        addr_trans_cross: cross addr_cp, trans_type_cp {
            // Only writes are valid for TX data register
            illegal_bins tx_read = binsof(addr_cp.tx_data_reg) && binsof(trans_type_cp.read);
            // Only reads are valid for RX data register
            illegal_bins rx_write = binsof(addr_cp.rx_data_reg) && binsof(trans_type_cp.write);
        }
        
        write_strb_cross: cross addr_cp, strb_cp {
            ignore_bins read_only_regs = binsof(addr_cp.status_reg) || binsof(addr_cp.rx_data_reg) || 
                                        binsof(addr_cp.fifo_status);
        }
        
        error_resp_cross: cross addr_cp, resp_cp {
            bins valid_addr_okay = binsof(addr_cp) intersect {ADDR_CONTROL_REG, ADDR_STATUS_REG, ADDR_TX_DATA_REG, 
                                                            ADDR_RX_DATA_REG, ADDR_FIFO_STATUS, ADDR_ERROR_STATUS, 
                                                            ADDR_FIFO_THRESH} && binsof(resp_cp.okay);
            bins invalid_addr_error = binsof(addr_cp.invalid_addr) && 
                                    (binsof(resp_cp.slverr) || binsof(resp_cp.decerr));
        }
    endgroup
    
    covergroup uart_tx_cg;
        option.per_instance = 1;
        option.name = "uart_tx_coverage";
        
        // Data pattern coverage
        data_cp: coverpoint uart_tx_tr.data {
            bins ascii_ctrl    = {[8'h00:8'h1F]};
            bins ascii_print   = {[8'h20:8'h7E]};
            bins ascii_ext     = {[8'h7F:8'hFF]};
            bins special_chars = {8'h0A, 8'h0D, 8'h00, 8'h20};
        }
        
        // Error coverage
        error_cp: coverpoint {uart_tx_tr.parity_error, uart_tx_tr.frame_error, uart_tx_tr.overrun_error} {
            bins no_error      = {3'b000};
            bins parity_error  = {3'b100};
            bins frame_error   = {3'b010};
            bins overrun_error = {3'b001};
            bins multi_error   = {3'b011, 3'b101, 3'b110, 3'b111};
        }
        
        // Timing coverage
        timing_cp: coverpoint uart_tx_tr.bit_period {
            bins normal_timing = {1};
            bins slow_timing   = {[2:5]};
            bins very_slow     = {[6:10]};
        }
        
        // Flow control coverage
        flow_ctrl_cp: coverpoint {uart_tx_tr.use_flow_control, uart_tx_tr.rts_assert, uart_tx_tr.cts_ready} {
            bins no_flow_ctrl     = {3'b0xx};
            bins flow_ctrl_ready  = {3'b111};
            bins rts_not_ready    = {3'b101, 3'b100};
            bins cts_not_ready    = {3'b110};
        }
        
        // Cross coverage
        data_error_cross: cross data_cp, error_cp;
        timing_flow_cross: cross timing_cp, flow_ctrl_cp;
    endgroup
    
    covergroup uart_rx_cg;
        option.per_instance = 1;
        option.name = "uart_rx_coverage";
        
        // Similar structure to TX coverage
        data_cp: coverpoint uart_rx_tr.data {
            bins ascii_ctrl    = {[8'h00:8'h1F]};
            bins ascii_print   = {[8'h20:8'h7E]};
            bins ascii_ext     = {[8'h7F:8'hFF]};
            bins special_chars = {8'h0A, 8'h0D, 8'h00, 8'h20};
        }
        
        error_cp: coverpoint {uart_rx_tr.parity_error, uart_rx_tr.frame_error, uart_rx_tr.overrun_error} {
            bins no_error      = {3'b000};
            bins parity_error  = {3'b100};
            bins frame_error   = {3'b010};
            bins overrun_error = {3'b001};
            bins multi_error   = {3'b011, 3'b101, 3'b110, 3'b111};
        }
    endgroup
    
    // System-level coverage
    covergroup system_cg;
        option.per_instance = 1;
        option.name = "system_coverage";
        
        // Register access patterns
        reg_sequence_cp: coverpoint {axi_tr.addr, axi_tr.trans_type} {
            bins control_write = {ADDR_CONTROL_REG, axi4_lite_transaction::WRITE};
            bins status_read   = {ADDR_STATUS_REG, axi4_lite_transaction::READ};
            bins tx_write      = {ADDR_TX_DATA_REG, axi4_lite_transaction::WRITE};
            bins rx_read       = {ADDR_RX_DATA_REG, axi4_lite_transaction::READ};
        }
        
        // System state transitions would be covered here
        // (This would require state tracking)
    endgroup
    
    // UVM registration
    `uvm_component_utils(uart_axi4_coverage)
    
    // Constructor
    function new(string name = "uart_axi4_coverage", uvm_component parent = null);
        super.new(name, parent);
        
        // Create coverage groups
        axi4_lite_cg = new();
        uart_tx_cg = new();
        uart_rx_cg = new();
        system_cg = new();
    endfunction
    
    // Build phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Create analysis exports
        axi_export = new("axi_export", this);
        uart_tx_export = new("uart_tx_export", this);
        uart_rx_export = new("uart_rx_export", this);
    endfunction
    
    // Write method for AXI transactions (from uvm_subscriber)
    virtual function void write(axi4_lite_transaction t);
        axi_tr = t;
        axi4_lite_cg.sample();
        system_cg.sample();
    endfunction
    
    // Analysis port write methods
    function void write_axi(axi4_lite_transaction t);
        write(t);
    endfunction
    
    function void write_uart_tx(uart_transaction t);
        uart_tx_tr = t;
        uart_tx_cg.sample();
        `uvm_info("COVERAGE", $sformatf("UART TX coverage sampled: data=0x%02h", t.data), UVM_HIGH)
    endfunction
    
    function void write_uart_rx(uart_transaction t);
        uart_rx_tr = t;
        uart_rx_cg.sample();
        `uvm_info("COVERAGE", $sformatf("UART RX coverage sampled: data=0x%02h", t.data), UVM_HIGH)
    endfunction
    
    // Connect phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect analysis exports to write methods
        // Note: These connections would be made in the environment
    endfunction
    
    // Report coverage
    function void report_coverage();
        real axi_cov = axi4_lite_cg.get_coverage();
        real uart_tx_cov = uart_tx_cg.get_coverage();
        real uart_rx_cov = uart_rx_cg.get_coverage();
        real system_cov = system_cg.get_coverage();
        real total_cov = (axi_cov + uart_tx_cov + uart_rx_cov + system_cov) / 4.0;
        
        `uvm_info("COVERAGE", "=== Coverage Report ===", UVM_LOW)
        `uvm_info("COVERAGE", $sformatf("AXI4-Lite Coverage: %.2f%%", axi_cov), UVM_LOW)
        `uvm_info("COVERAGE", $sformatf("UART TX Coverage: %.2f%%", uart_tx_cov), UVM_LOW)
        `uvm_info("COVERAGE", $sformatf("UART RX Coverage: %.2f%%", uart_rx_cov), UVM_LOW)
        `uvm_info("COVERAGE", $sformatf("System Coverage: %.2f%%", system_cov), UVM_LOW)
        `uvm_info("COVERAGE", $sformatf("Total Coverage: %.2f%%", total_cov), UVM_LOW)
        `uvm_info("COVERAGE", "======================", UVM_LOW)
        
        // Coverage goals check
        if (total_cov < 80.0) begin
            `uvm_warning("COVERAGE", $sformatf("Coverage goal not met: %.2f%% < 80%%", total_cov))
        end else begin
            `uvm_info("COVERAGE", $sformatf("Coverage goal achieved: %.2f%% >= 80%%", total_cov), UVM_LOW)
        end
    endfunction
    
    // Report phase
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        report_coverage();
    endfunction

endclass

`endif // UART_AXI4_COVERAGE_SV
