`timescale 1ns / 1ps

// Error Path Testing for UART-AXI4 Bridge
class uart_axi4_error_paths_test extends uart_axi4_base_test;
    
    `uvm_component_utils(uart_axi4_error_paths_test)
    
    function new(string name = "uart_axi4_error_paths_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Configure for error testing
        uvm_config_db#(int)::set(this, "*", "recording_detail", UVM_HIGH);
        
        // Increase timeout for error scenarios
        cfg.frame_timeout_ns = 5000000; // 5ms timeout for error scenarios
        uvm_config_db#(uart_axi4_env_config)::set(this, "*", "cfg", cfg);
        
        `uvm_info("ERROR_TEST", "Error paths test configured", UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        uart_axi4_error_sequence error_seq;
        uart_axi4_crc_error_sequence crc_error_seq;
        uart_axi4_protocol_violation_sequence protocol_viol_seq;
        uart_axi4_boundary_sequence boundary_seq;
        
        phase.raise_objection(this, "Starting error paths test");
        
        `uvm_info("ERROR_TEST", "=== Starting Error Paths Test ===", UVM_LOW)
        
        // Wait for reset to complete
        wait (tb.dut.rst_n == 1'b1);
        repeat (10) @(posedge tb.dut.clk);
        
        // Test general error conditions
        `uvm_info("ERROR_TEST", "Running general error injection sequence", UVM_MEDIUM)
        error_seq = uart_axi4_error_sequence::type_id::create("error_seq");
        error_seq.start(env.uart_agent.sequencer);
        
        // Wait between sequences
        repeat (100) @(posedge tb.dut.clk);
        
        // Test CRC error handling specifically
        `uvm_info("ERROR_TEST", "Running CRC error sequence", UVM_MEDIUM)
        crc_error_seq = uart_axi4_crc_error_sequence::type_id::create("crc_error_seq");
        crc_error_seq.start(env.uart_agent.sequencer);
        
        // Wait between sequences
        repeat (100) @(posedge tb.dut.clk);
        
        // Test protocol violations
        `uvm_info("ERROR_TEST", "Running protocol violation sequence", UVM_MEDIUM)
        protocol_viol_seq = uart_axi4_protocol_violation_sequence::type_id::create("protocol_viol_seq");
        protocol_viol_seq.start(env.uart_agent.sequencer);
        
        // Wait between sequences
        repeat (100) @(posedge tb.dut.clk);
        
        // Test boundary conditions
        `uvm_info("ERROR_TEST", "Running boundary condition sequence", UVM_MEDIUM)
        boundary_seq = uart_axi4_boundary_sequence::type_id::create("boundary_seq");
        boundary_seq.start(env.uart_agent.sequencer);
        
        // Final wait for all responses
        repeat (200) @(posedge tb.dut.clk);
        
        `uvm_info("ERROR_TEST", "=== Error Paths Test Completed ===", UVM_LOW)
        
        phase.drop_objection(this, "Error paths test completed");
    endtask
    
    virtual function void final_phase(uvm_phase phase);
        super.final_phase(phase);
        
        // Print error test summary
        `uvm_info("ERROR_TEST", "=== ERROR TEST SUMMARY ===", UVM_LOW)
        `uvm_info("ERROR_TEST", $sformatf("Total Error Frames Detected: %0d", env.scoreboard.error_frame_count), UVM_LOW)
        `uvm_info("ERROR_TEST", $sformatf("CRC Error Count: %0d", env.scoreboard.crc_error_count), UVM_LOW)
        `uvm_info("ERROR_TEST", $sformatf("Timeout Error Count: %0d", env.scoreboard.timeout_count), UVM_LOW)
        `uvm_info("ERROR_TEST", $sformatf("Protocol Violation Count: %0d", env.scoreboard.protocol_error_count), UVM_LOW)
        
        // For error testing, we expect some errors to be properly handled
        if (env.scoreboard.error_frame_count > 0) begin
            `uvm_info("ERROR_TEST", "*** ERROR HANDLING TEST PASSED ***", UVM_LOW)
        end else begin
            `uvm_warning("ERROR_TEST", "No errors detected - error injection may not be working")
        end
    endfunction
    
endclass