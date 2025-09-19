`timescale 1ns / 1ps

`include "uvm_macros.svh"
import uvm_pkg::*;

// System-level coverage collector for AXIUART
class system_coverage extends uvm_subscriber #(uvm_sequence_item);
    `uvm_component_utils(system_coverage)
    
    // Coverage groups for register block functionality
    covergroup register_access_cg;
        option.per_instance = 1;
        option.name = "register_access_coverage";
        
        // Register addresses
        register_addr: coverpoint m_trans.addr {
            bins control_reg   = {32'h0000_1000};
            bins status_reg    = {32'h0000_1004};
            bins config_reg    = {32'h0000_1008};
            bins debug_reg     = {32'h0000_100C};
            bins tx_count_reg  = {32'h0000_1010};
            bins rx_count_reg  = {32'h0000_1014};
            bins fifo_stat_reg = {32'h0000_1018};
            bins version_reg   = {32'h0000_101C};
            bins invalid_addr  = {[32'h0000_1020:32'h0000_1FFF]};
            bins unaligned     = {32'h0000_1001, 32'h0000_1002, 32'h0000_1003,
                                  32'h0000_1005, 32'h0000_1006, 32'h0000_1007};
        }
        
        // Transaction types
        trans_type: coverpoint m_trans.trans_type {
            bins read  = {AXI4_LITE_READ};
            bins write = {AXI4_LITE_WRITE};
        }
        
        // AXI response types
        response: coverpoint m_trans.resp {
            bins okay   = {2'b00};
            bins slverr = {2'b10};
        }
        
        // Write strobes for partial writes
        write_strb: coverpoint m_trans.strb {
            bins full_write  = {4'hF};
            bins byte_0      = {4'h1};
            bins byte_1      = {4'h2};
            bins byte_2      = {4'h4};
            bins byte_3      = {4'h8};
            bins lower_half  = {4'h3};
            bins upper_half  = {4'hC};
            bins others      = default;
        }
        
        // Cross coverage for comprehensive testing
        addr_type_cross: cross register_addr, trans_type {
            // Ignore write transactions to read-only registers
            ignore_bins ro_writes = addr_type_cross with 
                (register_addr inside {32'h0000_1004, 32'h0000_1010, 32'h0000_1014, 32'h0000_1018, 32'h0000_101C} && 
                 trans_type == AXI4_LITE_WRITE);
        }
        
        addr_resp_cross: cross register_addr, response {
            // Valid addresses should return OKAY
            // Invalid/unaligned addresses should return SLVERR
        }
    endgroup
    
    // Coverage for register field values
    covergroup register_fields_cg;
        option.per_instance = 1;
        option.name = "register_fields_coverage";
        
        // CONTROL register fields
        control_enable: coverpoint m_control_enable {
            bins disabled = {1'b0};
            bins enabled  = {1'b1};
        }
        
        // CONFIG register fields
        baud_div: coverpoint m_baud_div {
            bins low    = {[0:63]};
            bins mid    = {[64:127]};
            bins high   = {[128:191]};
            bins max    = {[192:255]};
        }
        
        timeout_cfg: coverpoint m_timeout_cfg {
            bins min     = {0};
            bins low     = {[1:63]};
            bins mid     = {[64:127]};
            bins high    = {[128:191]};
            bins max     = {[192:255]};
        }
        
        // DEBUG register fields
        debug_mode: coverpoint m_debug_mode {
            bins mode_0 = {4'h0};
            bins mode_1 = {4'h1};
            bins mode_2 = {4'h2};
            bins mode_3 = {4'h3};
            bins others = {[4'h4:4'hF]};
        }
    endgroup
    
    // Coverage for system-level behavior
    covergroup system_behavior_cg;
        option.per_instance = 1;
        option.name = "system_behavior_coverage";
        
        // System states
        system_busy: coverpoint m_system_busy {
            bins idle = {1'b0};
            bins busy = {1'b1};
        }
        
        system_ready: coverpoint m_system_ready {
            bins not_ready = {1'b0};
            bins ready     = {1'b1};
        }
        
        // Error conditions
        system_error: coverpoint m_system_error {
            bins no_error    = {8'h00};
            bins uart_error  = {[8'h01:8'h0F]};
            bins axi_error   = {[8'h10:8'h1F]};
            bins frame_error = {[8'h20:8'h2F]};
            bins other_error = {[8'h30:8'hFF]};
        }
        
        // State transitions
        ready_busy_trans: cross system_ready, system_busy {
            bins ready_idle = binsof(system_ready.ready) && binsof(system_busy.idle);
            bins ready_busy = binsof(system_ready.ready) && binsof(system_busy.busy);
            bins not_ready_any = binsof(system_ready.not_ready);
        }
    endgroup
    
    // Transaction tracking variables
    axi4_lite_transaction m_trans;
    bit m_control_enable;
    bit [7:0] m_baud_div;
    bit [7:0] m_timeout_cfg;
    bit [3:0] m_debug_mode;
    bit m_system_busy;
    bit m_system_ready;
    bit [7:0] m_system_error;
    
    function new(string name = "system_coverage", uvm_component parent = null);
        super.new(name, parent);
        
        // Initialize coverage groups
        register_access_cg = new();
        register_fields_cg = new();
        system_behavior_cg = new();
        
        // Initialize tracking variables
        m_control_enable = 1'b0;
        m_baud_div = 8'h00;
        m_timeout_cfg = 8'h00;
        m_debug_mode = 4'h0;
        m_system_busy = 1'b0;
        m_system_ready = 1'b0;
        m_system_error = 8'h00;
    endfunction
    
    virtual function void write(uvm_sequence_item t);
        axi4_lite_transaction axi_trans;
        
        // Cast to AXI transaction
        if (!$cast(axi_trans, t)) begin
            `uvm_warning("SYS_COV", "Failed to cast transaction to AXI4-Lite transaction")
            return;
        end
        
        m_trans = axi_trans;
        
        // Sample register access coverage
        register_access_cg.sample();
        
        // Update register field tracking for writes to specific registers
        if (axi_trans.trans_type == AXI4_LITE_WRITE && axi_trans.resp == 2'b00) begin
            case (axi_trans.addr)
                32'h0000_1000: begin // CONTROL register
                    m_control_enable = axi_trans.data[0];
                    register_fields_cg.sample();
                end
                
                32'h0000_1008: begin // CONFIG register
                    m_baud_div = axi_trans.data[7:0];
                    m_timeout_cfg = axi_trans.data[15:8];
                    register_fields_cg.sample();
                end
                
                32'h0000_100C: begin // DEBUG register
                    m_debug_mode = axi_trans.data[3:0];
                    register_fields_cg.sample();
                end
            endcase
        end
        
        // Sample system behavior (would be updated by system status monitoring)
        system_behavior_cg.sample();
    endfunction
    
    // Method to update system status from external monitors
    virtual function void update_system_status(bit busy, bit ready, bit [7:0] error);
        m_system_busy = busy;
        m_system_ready = ready;
        m_system_error = error;
        system_behavior_cg.sample();
    endfunction
    
    virtual function void report_phase(uvm_phase phase);
        real access_coverage, fields_coverage, behavior_coverage;
        
        access_coverage = register_access_cg.get_inst_coverage();
        fields_coverage = register_fields_cg.get_inst_coverage();
        behavior_coverage = system_behavior_cg.get_inst_coverage();
        
        `uvm_info("SYS_COV", $sformatf("Register Access Coverage: %.2f%%", access_coverage), UVM_MEDIUM)
        `uvm_info("SYS_COV", $sformatf("Register Fields Coverage: %.2f%%", fields_coverage), UVM_MEDIUM)
        `uvm_info("SYS_COV", $sformatf("System Behavior Coverage: %.2f%%", behavior_coverage), UVM_MEDIUM)
        
        if (access_coverage < 90.0) begin
            `uvm_warning("SYS_COV", $sformatf("Register access coverage below target: %.2f%% < 90%%", access_coverage))
        end
        
        if (fields_coverage < 90.0) begin
            `uvm_warning("SYS_COV", $sformatf("Register fields coverage below target: %.2f%% < 90%%", fields_coverage))
        end
        
        if (behavior_coverage < 90.0) begin
            `uvm_warning("SYS_COV", $sformatf("System behavior coverage below target: %.2f%% < 90%%", behavior_coverage))
        end
    endfunction
endclass