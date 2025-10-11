`timescale 1ns / 1ps

// =============================================================================
// uart_axi4_read_protocol_test.sv
// Read Protocol Verification Test
// 
// Purpose: Verify Frame_Builder read response protocol fix
// =============================================================================

class uart_axi4_read_protocol_test extends enhanced_uart_axi4_base_test;

    `uvm_component_utils(uart_axi4_read_protocol_test)
    
    function new(string name = "uart_axi4_read_protocol_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        configure_test_specific_reporting();
        
        // Enable waveform dumping for detailed analysis
        $dumpfile("read_protocol_verification.mxd");
        $dumpvars(0, uvm_top);
        
        `uvm_info(get_type_name(), "Read Protocol Verification Test - Build Phase", UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        uart_axi4_read_protocol_sequence read_seq;
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "=== Starting Read Protocol Verification Test ===", UVM_LOW)
        
        read_seq = uart_axi4_read_protocol_sequence::type_id::create("read_seq");
        read_seq.start(env.uart_agt.sequencer);
        
        // Wait for simulation to complete
        #200000ns;
        
        `uvm_info(get_type_name(), "=== Read Protocol Verification Test Complete ===", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
    virtual function void final_phase(uvm_phase phase);
        super.final_phase(phase);
        
        `uvm_info(get_type_name(), 
            "Read Protocol Test completed - Check waveforms for response frame analysis", 
            UVM_LOW)
    endfunction

endclass

