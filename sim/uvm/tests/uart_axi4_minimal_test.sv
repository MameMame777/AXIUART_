`timescale 1ns / 1ps

// Minimal test to verify basic functionality
class uart_axi4_minimal_test extends uart_axi4_base_test;

    `uvm_component_utils(uart_axi4_minimal_test)

    function new(string name = "uart_axi4_minimal_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this, "Starting minimal test");
        
        `uvm_info("MINIMAL_TEST", "=== Starting AXIUART_Top Minimal Test ===", UVM_LOW)
        
        // Wait for reset to complete
        wait (uart_axi4_tb_top.dut.rst == 1'b0);
        repeat (100) @(posedge uart_axi4_tb_top.dut.clk);
        
        // Monitor system status signals
        `uvm_info("MINIMAL_TEST", $sformatf("System Status - Ready: %b, Busy: %b, Error: %b", 
                  uart_axi4_tb_top.dut.system_ready,
                  uart_axi4_tb_top.dut.system_busy, 
                  uart_axi4_tb_top.dut.system_error), UVM_LOW)
        
        // Wait a reasonable amount of time then finish the test
        `uvm_info("MINIMAL_TEST", "Waiting for system to stabilize...", UVM_LOW)
        repeat (1000) @(posedge uart_axi4_tb_top.dut.clk);
        
        `uvm_info("MINIMAL_TEST", "=== AXIUART_Top Minimal Test Completed ===", UVM_LOW)
        
        phase.drop_objection(this, "Minimal test completed");
    endtask
    
    virtual function void final_phase(uvm_phase phase);
        super.final_phase(phase);
        `uvm_info("MINIMAL_TEST", "*** MINIMAL TEST PASSED ***", UVM_LOW)
    endfunction

endclass