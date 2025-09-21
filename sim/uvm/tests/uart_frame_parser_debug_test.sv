`timescale 1ns / 1ps

// Frame Parser Debug Test - UVM Compatible Version
class uart_frame_parser_debug_test extends uart_axi4_base_test;
    
    `uvm_component_utils(uart_frame_parser_debug_test)
    
    function new(string name = "uart_frame_parser_debug_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Configure for debugging
        uvm_config_db#(int)::set(this, "*", "recording_detail", UVM_FULL);
        
        `uvm_info("PARSER_DEBUG", "Frame Parser debug test configured", UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        uart_axi4_basic_sequence debug_seq;
        
        phase.raise_objection(this, "Starting Frame Parser debug");
        
        `uvm_info("PARSER_DEBUG", "=== Frame Parser Debug Test ===", UVM_LOW)
        
        // Wait for reset to complete
        wait (uart_axi4_tb_top.dut.rst == 1'b0);
        repeat (20) @(posedge uart_axi4_tb_top.dut.clk);
        
        // Run basic sequence to trigger Frame_Parser
        debug_seq = uart_axi4_basic_sequence::type_id::create("debug_seq");
        debug_seq.num_transactions = 3; // Small number for detailed analysis
        debug_seq.start(env.uart_agt.sequencer);
        
        // Wait for completion
        repeat (1000) @(posedge uart_axi4_tb_top.dut.clk);
        
        `uvm_info("PARSER_DEBUG", "=== Frame Parser Debug Completed ===", UVM_LOW)
        
        phase.drop_objection(this, "Frame Parser debug completed");
    endtask
    
    virtual function void final_phase(uvm_phase phase);
        super.final_phase(phase);
        
        `uvm_info("PARSER_DEBUG", "=== DEBUG SUMMARY ===", UVM_LOW)
        `uvm_info("PARSER_DEBUG", "Check waveforms for Frame_Parser internal signals", UVM_LOW)
    endfunction
    
endclass