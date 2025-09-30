`timescale 1ns / 1ps

// Directed test to exercise multi-beat auto-increment writes
class uart_axi4_multi_beat_write_test extends uart_axi4_base_test;
    
    `uvm_component_utils(uart_axi4_multi_beat_write_test)
    
    uart_axi4_multi_beat_write_seq multi_seq;
    
    function new(string name = "uart_axi4_multi_beat_write_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void configure_test();
        super.configure_test();
        cfg.enable_system_status_monitoring = 0;
        cfg.bridge_status_verbosity = UVM_NONE;
    endfunction
    
    virtual task main_phase(uvm_phase phase);
        `uvm_info("MULTI_BEAT_TEST", "===============================================", UVM_LOW)
        `uvm_info("MULTI_BEAT_TEST", "     UART-AXI4 MULTI-BEAT WRITE TEST", UVM_LOW)
        `uvm_info("MULTI_BEAT_TEST", "===============================================", UVM_LOW)
        `uvm_info("MULTI_BEAT_TEST", "Driving directed multi-beat write sequence", UVM_LOW)
        
        phase.raise_objection(this, "Running multi-beat write test");
        
        // Wait for DUT reset to complete before starting traffic
        wait (uart_axi4_tb_top.dut.rst == 1'b0);
        repeat (20) @(posedge uart_axi4_tb_top.dut.clk);
        
        multi_seq = uart_axi4_multi_beat_write_seq::type_id::create("multi_seq");
        multi_seq.start(env.uart_agt.sequencer);
        
        // Allow time for AXI responses and scoreboard processing
        repeat (2000) @(posedge uart_axi4_tb_top.dut.clk);
        
        `uvm_info("MULTI_BEAT_TEST", "=== Multi-beat write test completed ===", UVM_LOW)
        phase.drop_objection(this, "Multi-beat write test finished");
    endtask
    
endclass
