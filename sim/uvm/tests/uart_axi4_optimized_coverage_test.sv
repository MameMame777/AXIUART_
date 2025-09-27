`timescale 1ns / 1ps

// Optimized Coverage Test - Focuses on quick, efficient coverage improvement
class uart_axi4_optimized_coverage_test extends uart_axi4_base_test;
    `uvm_component_utils(uart_axi4_optimized_coverage_test)
    
    function new(string name = "uart_axi4_optimized_coverage_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        simple_debug_write_sequence_20250923 seq;
        
        `uvm_info("OPT_COV_TEST", "==========================================", UVM_LOW)
        `uvm_info("OPT_COV_TEST", "Starting Optimized Coverage Test Suite", UVM_LOW)
        `uvm_info("OPT_COV_TEST", "==========================================", UVM_LOW)
        
        // Raise objection for this phase
        phase.raise_objection(this);
        
        // Wait for reset completion and setup
        #1000ns;
        
        // Phase 1: Multiple quick write operations with different patterns
        `uvm_info("OPT_COV_TEST", "Phase 1: Quick Coverage Testing", UVM_LOW)
        
        // Run several quick transactions to improve coverage
        repeat(10) begin
            seq = simple_debug_write_sequence_20250923::type_id::create("quick_seq");
            seq.start(env.uart_agt.sequencer);
            #1000ns; // Short wait between sequences
        end
        
        `uvm_info("OPT_COV_TEST", "=== Optimized Coverage Test Completed ===", UVM_LOW)
        
        // Drop objection
        phase.drop_objection(this);
    endtask
    
endclass