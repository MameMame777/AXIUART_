`timescale 1ns / 1ps

// Basic Functional Test for UART-AXI4 Bridge
class uart_axi4_basic_test extends uart_axi4_base_test;
    
    `uvm_component_utils(uart_axi4_basic_test)
    
    function new(string name = "uart_axi4_basic_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Configure test-specific settings
        uvm_config_db#(int)::set(this, "*", "recording_detail", UVM_FULL);
        
        `uvm_info("BASIC_TEST", "Basic functional test configured", UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        uart_axi4_basic_sequence basic_seq;
        uart_axi4_read_sequence read_seq;
        uart_axi4_write_sequence write_seq;
        uart_axi4_burst_sequence burst_seq;
        
        phase.raise_objection(this, "Starting basic test");
        
        `uvm_info("BASIC_TEST", "=== Starting Basic Functional Test ===", UVM_LOW)
        
        // Wait for reset to complete
        wait (tb.dut.rst_n == 1'b1);
        repeat (10) @(posedge tb.dut.clk);
        
        // Run basic functionality sequence
        `uvm_info("BASIC_TEST", "Running basic functionality sequence", UVM_MEDIUM)
        basic_seq = uart_axi4_basic_sequence::type_id::create("basic_seq");
        basic_seq.num_transactions = 15;
        basic_seq.test_reads = 1;
        basic_seq.test_writes = 1;
        basic_seq.start(env.uart_agent.sequencer);
        
        // Wait between sequences
        repeat (50) @(posedge tb.dut.clk);
        
        // Run dedicated write sequence
        `uvm_info("BASIC_TEST", "Running write sequence", UVM_MEDIUM)
        write_seq = uart_axi4_write_sequence::type_id::create("write_seq");
        write_seq.num_writes = 8;
        write_seq.base_addr = 32'h1000;
        write_seq.start(env.uart_agent.sequencer);
        
        // Wait between sequences
        repeat (50) @(posedge tb.dut.clk);
        
        // Run dedicated read sequence to read back written data
        `uvm_info("BASIC_TEST", "Running read sequence", UVM_MEDIUM)
        read_seq = uart_axi4_read_sequence::type_id::create("read_seq");
        read_seq.num_reads = 8;
        read_seq.base_addr = 32'h1000;
        read_seq.start(env.uart_agent.sequencer);
        
        // Wait between sequences
        repeat (50) @(posedge tb.dut.clk);
        
        // Run burst sequence with different data sizes
        `uvm_info("BASIC_TEST", "Running burst sequence", UVM_MEDIUM)
        burst_seq = uart_axi4_burst_sequence::type_id::create("burst_seq");
        burst_seq.start(env.uart_agent.sequencer);
        
        // Final wait
        repeat (100) @(posedge tb.dut.clk);
        
        `uvm_info("BASIC_TEST", "=== Basic Functional Test Completed ===", UVM_LOW)
        
        phase.drop_objection(this, "Basic test completed");
    endtask
    
    virtual function void final_phase(uvm_phase phase);
        super.final_phase(phase);
        
        // Print test summary
        `uvm_info("BASIC_TEST", "=== TEST SUMMARY ===", UVM_LOW)
        `uvm_info("BASIC_TEST", $sformatf("Scoreboard Matches: %0d", env.scoreboard.match_count), UVM_LOW)
        `uvm_info("BASIC_TEST", $sformatf("Scoreboard Mismatches: %0d", env.scoreboard.mismatch_count), UVM_LOW)
        
        if (env.scoreboard.mismatch_count == 0) begin
            `uvm_info("BASIC_TEST", "*** TEST PASSED ***", UVM_LOW)
        end else begin
            `uvm_error("BASIC_TEST", "*** TEST FAILED ***")
        end
    endfunction
    
endclass