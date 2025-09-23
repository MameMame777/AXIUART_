`timescale 1ns / 1ps

// Comprehensive functional coverage package for AXIUART subsystem
// Implements 7 categories of covergroups for systematic feature verification

package axiuart_cov_pkg;
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // Simple transaction item for coverage (minimal dependencies)
    class uart_coverage_transaction extends uvm_sequence_item;
        logic [7:0]  cmd;
        logic [7:0]  len;
        logic [31:0] target_addr;
        logic [7:0]  crc_result;
        bit [6:0]    rx_fifo_level;
        bit [6:0]    tx_fifo_level;
        bit          parity_error;
        bit          framing_error;
        bit          timeout_error;
        bit [2:0]    parser_state;
        bit [2:0]    axi_state;
        bit [2:0]    frame_type;
        bit          force_crc_error;
        logic [7:0]  crc;
        
        `uvm_object_utils_begin(uart_coverage_transaction)
            `uvm_field_int(cmd, UVM_ALL_ON)
            `uvm_field_int(len, UVM_ALL_ON)
        `uvm_object_utils_end
        
        function new(string name = "uart_coverage_transaction");
            super.new(name);
        endfunction
    endclass
    
    // Coverage collection class with hierarchical covergroups
    class axiuart_functional_coverage extends uvm_subscriber#(uart_coverage_transaction);
        `uvm_component_utils(axiuart_functional_coverage)
        
        // Coverage enable/disable controls  
        bit coverage_enabled = 1;
        bit frame_cov_en = 1;
        bit crc_cov_en = 1;
        bit axi_cov_en = 1;
        bit fifo_cov_en = 1;
        bit error_cov_en = 1;
        bit state_cov_en = 1;
        bit cross_cov_en = 1;
        
        // Transaction fields for coverage sampling
        bit [7:0]  frame_cmd;
        bit [7:0]  frame_len;
        bit        crc_enabled;
        bit        crc_match;
        bit [31:0] axi_addr;
        bit [1:0]  axi_size;
        bit [6:0]  rx_fifo_cnt;
        bit [6:0]  tx_fifo_cnt;
        bit        uart_parity_err;
        bit        uart_frame_err;
        bit        uart_timeout;
        bit [2:0]  frame_parser_state;
        bit [2:0]  axi_master_state;
        bit [2:0]  frame_type_field;
        bit [7:0]  crc_result_field;
        
        // Category 1: Frame Characteristics Coverage
        covergroup cg_frame_characteristics;
            option.per_instance = 1;
            option.name = "frame_characteristics";
            
            frame_length: coverpoint frame_len {
                bins small_frames = {[1:4]};
                bins medium_frames = {[5:16]};  
                bins large_frames = {[17:64]};
                bins max_range_frames = {[65:255]};
                option.auto_bin_max = 8;
            }
            
            frame_cmd_type: coverpoint frame_cmd {
                bins read_single = {8'h01};
                bins write_single = {8'h02};
                bins read_burst = {8'h03}; // if supported
                bins config_access = {8'h04};
                bins reserved = default;
                illegal_bins invalid = {8'h00, [8'hF0:8'hFF]};
            }
            
            // Cross coverage for frame characteristics
            frame_len_type_cross: cross frame_length, frame_cmd_type {
                // Ignore impossible combinations
                ignore_bins large_config = binsof(frame_length.large_frames) && 
                                          binsof(frame_cmd_type.config_access);
            }
        endgroup
        
        // Category 2: CRC Coverage
        covergroup cg_crc_scenarios;
            option.per_instance = 1;
            option.name = "crc_scenarios";
            
            crc_enable: coverpoint crc_enabled {
                bins enabled = {1'b1};
                bins disabled = {1'b0};
            }
            
            crc_result: coverpoint crc_match iff (crc_enabled) {
                bins pass = {1'b1};
                bins fail = {1'b0};
            }
            
            crc_len_dependency: coverpoint frame_len iff (crc_enabled) {
                bins short_crc = {[1:8]};
                bins medium_crc = {[9:32]};
                bins long_crc = {[33:128]};
                bins max_crc = {[129:255]};
            }
            
            crc_cross: cross crc_enable, crc_result {
                ignore_bins disabled_result = binsof(crc_enable.disabled) &&
                                             binsof(crc_result);
            }
        endgroup
        
        // Category 3: AXI Alignment Coverage  
        covergroup cg_axi_alignment;
            option.per_instance = 1;
            option.name = "axi_alignment";
            
            address_align: coverpoint axi_addr[1:0] {
                bins aligned = {2'b00};
                bins misalign_1 = {2'b01};
                bins misalign_2 = {2'b10}; 
                bins misalign_3 = {2'b11};
            }
            
            access_size: coverpoint axi_size {
                bins byte_access = {2'b00};  // 8-bit
                bins half_access = {2'b01};  // 16-bit
                bins word_access = {2'b10};  // 32-bit
                illegal_bins invalid_size = {2'b11};
            }
            
            address_range: coverpoint axi_addr {
                bins register_space = {[32'h0000_1000:32'h0000_101F]};
                bins unmapped_low = {[32'h0000_1020:32'h0000_10FF]};
                bins unmapped_high = {[32'h0000_1100:32'h0000_1FFF]};
                bins out_of_range = default;
            }
            
            align_cross: cross address_align, access_size {
                // Word access should only be aligned
                illegal_bins word_misaligned = binsof(access_size.word_access) &&
                    (binsof(address_align.misalign_1) || binsof(address_align.misalign_2) ||
                     binsof(address_align.misalign_3));
            }
        endgroup
        
        // Category 4: FIFO Level Coverage
        covergroup cg_fifo_utilization;
            option.per_instance = 1;
            option.name = "fifo_utilization";
            
            rx_fifo_level: coverpoint rx_fifo_cnt {
                bins empty = {7'b0000000};
                bins low = {[7'b0000001:7'b0001111]};     // 1-15
                bins mid = {[7'b0010000:7'b0101111]};     // 16-47
                bins high = {[7'b0110000:7'b0111110]};    // 48-62
                bins full = {7'b0111111};                 // 63 (64-deep FIFO)
                illegal_bins illegal_overflow = {[7'b1000000:7'b1111111]}; // Direct range
            }
            
            tx_fifo_level: coverpoint tx_fifo_cnt {
                bins empty = {7'b0000000};
                bins low = {[7'b0000001:7'b0001111]};
                bins mid = {[7'b0010000:7'b0101111]};
                bins high = {[7'b0110000:7'b0111110]};
                bins full = {7'b0111111};
                illegal_bins illegal_overflow = {[7'b1000000:7'b1111111]}; // Direct range
            }
            
            fifo_utilization_cross: cross rx_fifo_level, tx_fifo_level {
                // Ignore extreme combinations that are unlikely
                ignore_bins both_full = binsof(rx_fifo_level.full) &&
                                       binsof(tx_fifo_level.full);
            }
        endgroup
        
        // Category 5: UART Error Coverage
        covergroup cg_uart_error_conditions;
            option.per_instance = 1;
            option.name = "uart_error_conditions";
            
            parity_error: coverpoint uart_parity_err {
                bins no_error = {1'b0};
                bins error = {1'b1};
            }
            
            framing_error: coverpoint uart_frame_err {
                bins no_error = {1'b0};
                bins error = {1'b1};
            }
            
            timeout_error: coverpoint uart_timeout {
                bins no_timeout = {1'b0};
                bins timeout = {1'b1};
            }
            
            error_combo: cross parity_error, framing_error, timeout_error {
                // Multiple simultaneous errors are critical
                bins single_parity = binsof(parity_error.error) &&
                                   binsof(framing_error.no_error) &&
                                   binsof(timeout_error.no_timeout);
                bins single_framing = binsof(parity_error.no_error) &&
                                    binsof(framing_error.error) &&
                                    binsof(timeout_error.no_timeout);
                bins single_timeout = binsof(parity_error.no_error) &&
                                    binsof(framing_error.no_error) &&
                                    binsof(timeout_error.timeout);
                bins multiple_errors = binsof(parity_error.error) &&
                                     binsof(framing_error.error);
            }
        endgroup
        
        // Category 6: State Machine Coverage
        covergroup cg_fsm_states;
            option.per_instance = 1;
            option.name = "fsm_states";
            
            frame_parser_state: coverpoint frame_parser_state {
                bins idle = {3'b000};
                bins header = {3'b001};
                bins length = {3'b010};
                bins payload = {3'b011};
                bins crc = {3'b100};
                bins error = {3'b101};
                bins recovery = {3'b110};
                illegal_bins reserved = {3'b111};
            }
            
            axi_master_state: coverpoint axi_master_state {
                bins idle = {3'b000};
                bins addr_phase = {3'b001};
                bins write_data = {3'b010};
                bins read_data = {3'b011};
                bins response = {3'b100};
                bins error_recovery = {3'b101};
                illegal_bins reserved = {[3'b110:3'b111]};
            }
            
            // State transition coverage - critical for FSM verification
            parser_transitions: coverpoint frame_parser_state {
                bins idle_to_header = (3'b000 => 3'b001);
                bins header_to_length = (3'b001 => 3'b010);
                bins length_to_payload = (3'b010 => 3'b011);
                bins payload_to_crc = (3'b011 => 3'b100);
                bins crc_to_idle = (3'b100 => 3'b000);
                bins error_to_recovery = (3'b101 => 3'b110);
                bins recovery_to_idle = (3'b110 => 3'b000);
                bins any_to_error = (3'b000, 3'b001, 3'b010, 3'b011, 3'b100 => 3'b101);
            }
            
            axi_transitions: coverpoint axi_master_state {
                bins idle_to_addr = (3'b000 => 3'b001);
                bins addr_to_write = (3'b001 => 3'b010);
                bins addr_to_read = (3'b001 => 3'b011);
                bins write_to_resp = (3'b010 => 3'b100);
                bins read_to_resp = (3'b011 => 3'b100);
                bins resp_to_idle = (3'b100 => 3'b000);
                bins error_to_recovery = (3'b101 => 3'b101); // Self-loop
                bins recovery_to_idle = (3'b101 => 3'b000);
            }
        endgroup
        
        // Category 7: System Cross Coverage (Most Important) 
        covergroup cg_system_cross;
            option.per_instance = 1;
            option.name = "system_cross";
            
            // Re-define coverpoints needed for cross coverage
            frame_cmd_local: coverpoint frame_cmd {
                bins read_single = {8'h01};
                bins write_single = {8'h02};
                bins read_burst = {8'h03};
                bins config_access = {8'h04};
            }
            
            crc_match_local: coverpoint crc_match {
                bins pass = {1'b1};
                bins fail = {1'b0};
            }
            
            rx_fifo_local: coverpoint rx_fifo_cnt {
                bins empty = {7'b0000000};
                bins low = {[7'b0000001:7'b0001111]};
                bins mid = {[7'b0010000:7'b0101111]};
                bins high = {[7'b0110000:7'b0111110]};
                bins full = {7'b0111111};
            }
            
            frame_crc_cross: cross frame_cmd_local, crc_match_local {
                ignore_bins config_with_crc_fail = binsof(frame_cmd_local.config_access) &&
                                                  binsof(crc_match_local.fail);
            }
            
            fifo_operation_cross: cross rx_fifo_local, frame_cmd_local {
                bins low_fifo_read = binsof(rx_fifo_local.low) && 
                                   binsof(frame_cmd_local.read_single);
                bins high_fifo_write = binsof(rx_fifo_local.high) && 
                                     binsof(frame_cmd_local.write_single);
                bins full_fifo_any = binsof(rx_fifo_local.full) && 
                                   (binsof(frame_cmd_local.read_single) || binsof(frame_cmd_local.write_single));
            }
            
            parity_err_local: coverpoint uart_parity_err {
                bins no_error = {1'b0};
                bins error = {1'b1};
            }
            
            timeout_local: coverpoint uart_timeout {
                bins no_timeout = {1'b0};
                bins timeout = {1'b1};
            }
            
            error_state_cross: cross parity_err_local, timeout_local {
                bins error_with_timeout = binsof(parity_err_local.error) &&
                                       binsof(timeout_local.timeout);
            }
        endgroup
        
        function new(string name="axiuart_functional_coverage", uvm_component parent=null);
            super.new(name, parent);
            
            // Instantiate all covergroups
            if (frame_cov_en) cg_frame_characteristics = new();
            if (crc_cov_en) cg_crc_scenarios = new();
            if (axi_cov_en) cg_axi_alignment = new();
            if (fifo_cov_en) cg_fifo_utilization = new();
            if (error_cov_en) cg_uart_error_conditions = new();
            if (state_cov_en) cg_fsm_states = new();
            if (cross_cov_en) cg_system_cross = new();
        endfunction
        
        function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            
            // Get coverage configuration from testbench
            if (!uvm_config_db#(bit)::get(this, "", "coverage_enabled", coverage_enabled)) begin
                coverage_enabled = 1; // Default enabled
            end
        endfunction
        
        // Sample coverage on each transaction
        virtual function void write(uart_coverage_transaction t);
            if (!coverage_enabled) return;
            
            // Extract data from transaction
            frame_cmd = t.cmd;
            frame_len = t.len;
            
            // CRC fields
            crc_enabled = !t.force_crc_error; // Assume enabled unless force error
            crc_match = (t.crc == t.crc_result);
            crc_result_field = t.crc_result;
            
            // AXI fields  
            axi_addr = t.target_addr;
            axi_size = (frame_len <= 1) ? 2'b00 : (frame_len <= 2) ? 2'b01 : 2'b10;
            
            // FIFO levels (would be obtained from DUT interface)
            // These should be connected to actual DUT signals via interface
            rx_fifo_cnt = t.rx_fifo_level;
            tx_fifo_cnt = t.tx_fifo_level;
            
            // Error conditions
            uart_parity_err = t.parity_error;
            uart_frame_err = t.framing_error; 
            uart_timeout = t.timeout_error;
            
            // State machine states (from DUT interface monitoring)
            frame_parser_state = t.parser_state;
            axi_master_state = t.axi_state;
            frame_type_field = t.frame_type;
            
            // Sample all enabled covergroups
            if (frame_cov_en) cg_frame_characteristics.sample();
            if (crc_cov_en) cg_crc_scenarios.sample();
            if (axi_cov_en) cg_axi_alignment.sample();
            if (fifo_cov_en) cg_fifo_utilization.sample();
            if (error_cov_en) cg_uart_error_conditions.sample();
            if (state_cov_en) cg_fsm_states.sample();
            if (cross_cov_en) cg_system_cross.sample();
        endfunction        // Coverage reporting
        virtual function void report_phase(uvm_phase phase);
            real total_coverage;
            
            `uvm_info(get_type_name(), "=== AXIUART Functional Coverage Report ===", UVM_LOW)
            
            if (cg_frame_characteristics != null) begin
                `uvm_info(get_type_name(), 
                    $sformatf("Frame Characteristics Coverage: %.1f%%", 
                    cg_frame_characteristics.get_coverage()), UVM_LOW)
            end
            
            if (cg_crc_scenarios != null) begin
                `uvm_info(get_type_name(), 
                    $sformatf("CRC Scenarios Coverage: %.1f%%", 
                    cg_crc_scenarios.get_coverage()), UVM_LOW)
            end
            
            if (cg_axi_alignment != null) begin
                `uvm_info(get_type_name(), 
                    $sformatf("AXI Alignment Coverage: %.1f%%", 
                    cg_axi_alignment.get_coverage()), UVM_LOW)
            end
            
            if (cg_fifo_utilization != null) begin
                `uvm_info(get_type_name(), 
                    $sformatf("FIFO Utilization Coverage: %.1f%%", 
                    cg_fifo_utilization.get_coverage()), UVM_LOW)
            end
            
            if (cg_uart_error_conditions != null) begin
                `uvm_info(get_type_name(), 
                    $sformatf("UART Error Coverage: %.1f%%", 
                    cg_uart_error_conditions.get_coverage()), UVM_LOW)
            end
            
            if (cg_fsm_states != null) begin
                `uvm_info(get_type_name(), 
                    $sformatf("FSM States Coverage: %.1f%%", 
                    cg_fsm_states.get_coverage()), UVM_LOW)
            end
            
            if (cg_system_cross != null) begin
                `uvm_info(get_type_name(), 
                    $sformatf("System Cross Coverage: %.1f%%", 
                    cg_system_cross.get_coverage()), UVM_LOW)
            end
            
            `uvm_info(get_type_name(), "=== End Coverage Report ===", UVM_LOW)
        endfunction
        
    endclass

endpackage