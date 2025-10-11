`timescale 1ns / 1ps

//=============================================================================
// Simplified Register Sweep for Toggle Coverage Enhancement
// Purpose: Minimal register access pattern to improve toggle coverage
// Strategy: Direct UART commands to exercise register block signals
//=============================================================================

`ifndef SIMPLE_REGISTER_SWEEP_TEST_SV
`define SIMPLE_REGISTER_SWEEP_TEST_SV

import uvm_pkg::*;
import uart_axi4_test_pkg::*;

class simple_register_sweep_test extends enhanced_uart_axi4_base_test;
    `uvm_component_utils(simple_register_sweep_test)
    
    function new(string name = "simple_register_sweep_test", uvm_component parent = null);
        super.new(name, parent);
        `uvm_info("SIMPLE_TOGGLE", "Simple Register Sweep Test initialized", UVM_LOW)
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        configure_test_specific_reporting();
        
        // Enhanced configuration for register coverage  
        cfg.enable_coverage = 1;
        cfg.num_transactions = 200;  // More transactions for better coverage
        cfg.system_timeout_cycles = 2000;
        
        `uvm_info("SIMPLE_TOGGLE", "Configuration for register toggle enhancement", UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        simple_debug_write_sequence_20250923 debug_seq;
        
        phase.raise_objection(this);
        
        `uvm_info("SIMPLE_TOGGLE", "==========================================", UVM_LOW)
        `uvm_info("SIMPLE_TOGGLE", "    SIMPLE REGISTER SWEEP TEST", UVM_LOW)
        `uvm_info("SIMPLE_TOGGLE", "==========================================", UVM_LOW)
        `uvm_info("SIMPLE_TOGGLE", "Target: Improve Toggle Coverage 14% 竊・50%+", UVM_LOW)
        
        // Wait for reset to complete
        wait (uart_axi4_tb_top.dut.rst == 1'b0);
        repeat (10) @(posedge uart_axi4_tb_top.dut.clk);
        
        // Execute multiple sequences to generate register activity
        for (int i = 0; i < 25; i++) begin
            debug_seq = simple_debug_write_sequence_20250923::type_id::create("debug_seq");
            `uvm_info("SIMPLE_TOGGLE", $sformatf("Executing register sweep iteration %0d/25", i+1), UVM_MEDIUM)
            debug_seq.start(env.uart_agt.sequencer);
            
            // Wait between iterations
            repeat (100) @(posedge uart_axi4_tb_top.dut.clk);
        end
        
        // Additional register-focused transactions
        send_register_focused_frames();
        
        `uvm_info("SIMPLE_TOGGLE", "=== Simple Register Sweep Test Completed ===", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
    // Send specific UART frames targeting register addresses
    virtual task send_register_focused_frames();
        uart_frame_transaction req;
        
        `uvm_info("SIMPLE_TOGGLE", "Sending register-focused UART frames", UVM_MEDIUM)
        
        // Send multiple register read commands with different addresses
        for (int addr_offset = 0; addr_offset < 32; addr_offset += 4) begin
            req = uart_frame_transaction::type_id::create("reg_read_req");
            req.randomize() with {
                frame_data.size() == 6;
                frame_data[0] == 8'h5A;     // SOF
                frame_data[1] == 8'h80;     // READ_CMD
                frame_data[2] == (16'h1000 + addr_offset) >> 8;    // ADDR_H
                frame_data[3] == (16'h1000 + addr_offset) & 8'hFF; // ADDR_L
                frame_data[4] == 8'h04;     // LENGTH
                frame_data[5] == 8'h00;     // Simple CRC
                frame_length == 6;
                error_inject == 0;
                data_randomization == 0;
            };
            
            req.start(env.uart_agt.sequencer);
            #5000; // Wait between register accesses
        end
        
        `uvm_info("SIMPLE_TOGGLE", "Register-focused frames sent", UVM_MEDIUM)
    endtask
    
endclass

`endif // SIMPLE_REGISTER_SWEEP_TEST_SV
