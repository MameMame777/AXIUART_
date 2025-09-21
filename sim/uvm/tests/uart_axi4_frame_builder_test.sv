`timescale 1ns / 1ps

// Frame_Builder Diagnostic Test for UART-AXI4 Bridge
class uart_axi4_frame_builder_test extends uart_axi4_base_test;
    
    `uvm_component_utils(uart_axi4_frame_builder_test)
    
    function new(string name = "uart_axi4_frame_builder_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Configure test-specific settings for Frame_Builder diagnosis
        uvm_config_db#(int)::set(this, "*", "recording_detail", UVM_FULL);
        
        // Increase frame timeout for Frame_Builder response investigation
        uvm_config_db#(int)::set(this, "*", "frame_timeout_ns", 10_000_000); // 10ms timeout
        
        `uvm_info("FRAME_BUILDER_TEST", "Frame_Builder diagnostic test configured", UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        uart_axi4_frame_builder_sequence fb_seq;
        
        phase.raise_objection(this, "Starting Frame_Builder diagnostic test");
        
        // Set timeout for the diagnostic test
        phase.phase_done.set_drain_time(this, 2000ns);
        
        `uvm_info("FRAME_BUILDER_TEST", "=== Frame_Builder Diagnostic Test Started ===", UVM_LOW)
        
        // Run Frame_Builder diagnostic sequence
        fb_seq = uart_axi4_frame_builder_sequence::type_id::create("fb_seq");
        fb_seq.start(env.uart_agt.sequencer);
        
        // Wait for completion
        #500ns;
        
        `uvm_info("FRAME_BUILDER_TEST", "=== Frame_Builder Diagnostic Test Completed ===", UVM_LOW)
        
        phase.drop_objection(this, "Frame_Builder diagnostic test completed");
    endtask
    
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        
        `uvm_info("FRAME_BUILDER_TEST", "Frame_Builder Diagnostic Test Report:", UVM_LOW)
        `uvm_info("FRAME_BUILDER_TEST", "Check waveform for Frame_Builder response generation", UVM_LOW)
    endfunction

endclass