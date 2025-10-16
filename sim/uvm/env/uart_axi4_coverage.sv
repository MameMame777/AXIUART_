`timescale 1ns / 1ps

// UVM Coverage Collector for UART-AXI4 Bridge
class uart_axi4_coverage extends uvm_subscriber #(uart_frame_transaction);
    
    `uvm_component_utils(uart_axi4_coverage)
    
    // Configuration
    uart_axi4_env_config cfg;
    
    // Coverage groups
    covergroup frame_coverage with function sample(uart_frame_transaction tr);
        
        // Command field coverage
        rw_bit: coverpoint tr.cmd[7] {
            bins read = {1'b1};
            bins write = {1'b0};
        }
        
        inc_bit: coverpoint tr.cmd[6] {
            bins no_increment = {1'b0};
            bins auto_increment = {1'b1};
        }
        
        size_field: coverpoint tr.cmd[5:4] {
            bins size_8bit = {2'b00};
            bins size_16bit = {2'b01};
            bins size_32bit = {2'b10};
            illegal_bins illegal_size = {2'b11};
        }
        
        length_field: coverpoint tr.cmd[3:0] {
            bins length_1 = {4'h0};
            bins length_2 = {4'h1};
            bins length_3_8 = {[4'h2:4'h7]};
            bins length_9_16 = {[4'h8:4'hF]};
        }
        
        // Address alignment coverage
        addr_alignment: coverpoint {tr.cmd[5:4], tr.addr[1:0]} {
            bins aligned_8bit = {4'b00_00, 4'b00_01, 4'b00_10, 4'b00_11};
            bins aligned_16bit = {4'b01_00, 4'b01_10};
            bins misaligned_16bit = {4'b01_01, 4'b01_11};
            bins aligned_32bit = {4'b10_00};
            bins misaligned_32bit = {4'b10_01, 4'b10_10, 4'b10_11};
        }
        
        // Response status coverage
        response_status: coverpoint tr.response_status {
            bins success = {STATUS_OK};
            bins crc_error = {STATUS_CRC_ERR};
            bins cmd_invalid = {STATUS_CMD_INV};
            bins addr_misalign = {STATUS_ADDR_ALIGN};
            bins timeout = {STATUS_TIMEOUT};
            bins axi_error = {STATUS_AXI_SLVERR};
            bins busy = {STATUS_BUSY};
            bins len_range = {STATUS_LEN_RANGE};
        }
        
        // Cross coverage: operation type vs size vs length
        rw_size_len: cross rw_bit, size_field, length_field {
            ignore_bins invalid_size = binsof(size_field.illegal_size);
        }
        
        // Cross coverage: alignment vs response status
        align_status: cross addr_alignment, response_status;
        
        // WSTRB coverage for different sizes and addresses
        wstrb_coverage: coverpoint {tr.cmd[5:4], tr.addr[1:0]} iff (!tr.cmd[7]) { // Write only
            bins wstrb_8bit_byte0 = {4'b00_00}; // WSTRB = 0001
            bins wstrb_8bit_byte1 = {4'b00_01}; // WSTRB = 0010
            bins wstrb_8bit_byte2 = {4'b00_10}; // WSTRB = 0100
            bins wstrb_8bit_byte3 = {4'b00_11}; // WSTRB = 1000
            bins wstrb_16bit_low = {4'b01_00};  // WSTRB = 0011
            bins wstrb_16bit_high = {4'b01_10}; // WSTRB = 1100
            bins wstrb_32bit = {4'b10_00};      // WSTRB = 1111
        }
        
    endgroup
    
    // Additional coverage for burst operations
    covergroup burst_coverage with function sample(uart_frame_transaction tr);
        
        // Burst length coverage
        burst_length: coverpoint tr.cmd[3:0] {
            bins single = {4'h0};
            bins short_burst = {[4'h1:4'h3]};
            bins medium_burst = {[4'h4:4'h7]};
            bins long_burst = {[4'h8:4'hF]};
        }
        
        // Burst type (increment vs fixed address)
        burst_type: coverpoint tr.cmd[6] {
            bins fixed = {1'b0};
            bins increment = {1'b1};
        }
        
        // Size field (needed for cross coverage)
        size_field: coverpoint tr.cmd[5:4] {
            bins size_8bit = {2'b00};
            bins size_16bit = {2'b01};
            bins size_32bit = {2'b10};
            illegal_bins illegal_size = {2'b11};
        }
        
        // Cross coverage: burst length vs type vs size
        burst_len_type_size: cross burst_length, burst_type, size_field {
            ignore_bins invalid_size = binsof(size_field.illegal_size);
        }
        
    endgroup
    
    // Error injection coverage
    covergroup error_coverage with function sample(uart_frame_transaction tr);
        
        // CRC error coverage
        crc_correct: coverpoint (tr.response_status == STATUS_CRC_ERR) {
            bins correct_crc = {1'b0};
            bins crc_error = {1'b1};
        }
        
        // Timeout coverage
        timeout_occurred: coverpoint (tr.response_status == STATUS_TIMEOUT) {
            bins no_timeout = {1'b0};
            bins timeout = {1'b1};
        }
        
        // AXI error coverage
        axi_error: coverpoint (tr.response_status == STATUS_AXI_SLVERR) {
            bins no_axi_error = {1'b0};
            bins axi_error = {1'b1};
        }
        
    endgroup
    
    function new(string name = "uart_axi4_coverage", uvm_component parent = null);
        super.new(name, parent);
        frame_coverage = new();
        burst_coverage = new();
        error_coverage = new();
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if (!uvm_config_db#(uart_axi4_env_config)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("COVERAGE", "Failed to get configuration object")
        end
    endfunction
    
    // Sample coverage when transaction is received
    virtual function void write(uart_frame_transaction t);
        if (cfg.enable_coverage) begin
            frame_coverage.sample(t);
            burst_coverage.sample(t);
            error_coverage.sample(t);
            
            `uvm_info("COVERAGE", $sformatf("Sampled coverage for transaction: CMD=0x%02X, STATUS=0x%02X", 
                      t.cmd, t.response_status), UVM_DEBUG)
        end
    endfunction
    
    // Additional sampling methods for monitor compatibility
    virtual function void sample_uart_transaction(uart_frame_transaction t);
        write(t);
    endfunction
    
    virtual function void sample_uart_response(uart_frame_transaction t);
        write(t);
    endfunction
    
    // AXI transaction sampling method for AXI monitor
    virtual function void sample_axi_transaction(axi4_lite_transaction t);
        `uvm_info("COVERAGE", $sformatf("Sampled AXI coverage for transaction: ADDR=0x%08X, TYPE=%s", 
                  t.addr, t.trans_type.name()), UVM_DEBUG)
    endfunction
    
    // Report coverage statistics
    virtual function void final_phase(uvm_phase phase);
        real frame_cov;
        real burst_cov;
        real error_cov;
        real total_cov;
        real threshold;

        frame_cov = frame_coverage.get_coverage();
        burst_cov = burst_coverage.get_coverage();
        error_cov = error_coverage.get_coverage();
        total_cov = (frame_cov + burst_cov + error_cov) / 3.0;

        `uvm_info("COVERAGE", "=== COVERAGE REPORT ===", UVM_LOW)
        `uvm_info("COVERAGE", $sformatf("Frame coverage: %0.2f%%", frame_cov), UVM_LOW)
        `uvm_info("COVERAGE", $sformatf("Burst coverage: %0.2f%%", burst_cov), UVM_LOW)
        `uvm_info("COVERAGE", $sformatf("Error coverage: %0.2f%%", error_cov), UVM_LOW)
        `uvm_info("COVERAGE", $sformatf("Total coverage: %0.2f%%", total_cov), UVM_LOW)
        threshold = (cfg != null) ? cfg.coverage_warning_threshold : 80.0;

        if (total_cov < threshold) begin
            `uvm_warning("COVERAGE",
                $sformatf("Coverage %0.2f%% is below configured threshold %0.2f%%",
                          total_cov, threshold))
        end
    endfunction

endclass