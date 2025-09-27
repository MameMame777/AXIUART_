`timescale 1ns / 1ps

// =============================================================================
// uart_axi4_register_block_test.sv
// Register_Block AXI4-Lite Transaction Diagnostic Test
// 
// Purpose: Verify Register_Block state machine and handshake signal generation
// =============================================================================

`timescale 1ns / 1ps

class uart_axi4_register_block_test extends uart_axi4_base_test;

    `uvm_component_utils(uart_axi4_register_block_test)
    
    function new(string name = "uart_axi4_register_block_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Enable waveform dumping for detailed analysis
        $dumpfile("register_block_diagnostic_test.mxd");
        $dumpvars(0, uvm_top);
        
        `uvm_info(get_type_name(), "Register Block Diagnostic Test - Build Phase", UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        uart_axi4_register_block_sequence reg_seq;
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "=== Starting Register Block AXI4-Lite Diagnostic Test ===", UVM_LOW)
        
        reg_seq = uart_axi4_register_block_sequence::type_id::create("reg_seq");
        reg_seq.start(env.uart_agt.sequencer);
        
        // Wait for simulation to complete
        #100000ns;
        
        `uvm_info(get_type_name(), "=== Register Block Diagnostic Test Complete ===", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
    virtual function void final_phase(uvm_phase phase);
        super.final_phase(phase);
        
        `uvm_info(get_type_name(), 
            "Register Block Test completed - Check waveforms for AXI handshake analysis", 
            UVM_LOW)
    endfunction

endclass