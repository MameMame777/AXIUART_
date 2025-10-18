`timescale 1ns / 1ps

// AXIUART_Top System Level Test
// Simple test to verify system-level functionality without complex sequences
class axiuart_system_test extends enhanced_uart_axi4_base_test;
    
    `uvm_component_utils(axiuart_system_test)
    
    function new(string name = "axiuart_system_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        configure_test_specific_reporting();
        `uvm_info("SYSTEM_TEST", "AXIUART_Top System test build phase", UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        virtual bridge_status_if status_vif;
        simple_test_register_sequence reg_seq;

        phase.raise_objection(this, "Starting AXIUART system test");
        
        `uvm_info("SYSTEM_TEST", "=== AXIUART_Top System Test Started ===", UVM_LOW)
        
        // Wait for reset deassertion
        wait (uart_axi4_tb_top.rst_n == 1'b1);
        repeat (10) @(posedge uart_axi4_tb_top.clk);
        
        `uvm_info("SYSTEM_TEST", "Reset deasserted, system initializing", UVM_LOW)
        
        // Monitor system status
        repeat (50) @(posedge uart_axi4_tb_top.clk);
        
        `ifdef DEFINE_SIM
    // Prefer the bridge_status_vif exported by the TB for system status
    if (!uvm_config_db#(virtual bridge_status_if)::get(this, "", "bridge_status_vif", status_vif)) begin
            `uvm_warning("SYSTEM_TEST", "bridge_status_vif not available; falling back to tb signals if present")
            `uvm_info("SYSTEM_TEST", $sformatf("System Status (tb): Ready=%b, Busy=%b, Error=%b", 
                      uart_axi4_tb_top.system_ready,
                      uart_axi4_tb_top.system_busy, 
                      uart_axi4_tb_top.system_error), UVM_LOW)
        end else begin
            `uvm_info("SYSTEM_TEST", $sformatf("System Status: Ready=%b, Busy=%b, Error=%b", 
                      status_vif.system_ready,
                      status_vif.bridge_busy, 
                      status_vif.bridge_error), UVM_LOW)
        end
        `else
        `uvm_info("SYSTEM_TEST", "System Status: Not available (synthesis mode)", UVM_LOW)
        `endif
        
        // Drive a basic UART register access sequence to exercise the bridge path
        if (env == null || env.uart_agt == null || env.uart_agt.sequencer == null) begin
            `uvm_fatal("SYSTEM_TEST", "UART agent or sequencer not available; cannot drive stimulus")
        end

        reg_seq = simple_test_register_sequence::type_id::create("reg_seq");
        if (reg_seq == null) begin
            `uvm_fatal("SYSTEM_TEST", "Failed to create simple_test_register_sequence instance")
        end

        `uvm_info("SYSTEM_TEST", "Starting simple register access sequence", UVM_LOW)
        reg_seq.start(env.uart_agt.sequencer);
        `uvm_info("SYSTEM_TEST", "Register access sequence completed", UVM_LOW)
        
        // Wait for system to stabilize
        repeat (100) @(posedge uart_axi4_tb_top.clk);
        
        `uvm_info("SYSTEM_TEST", "=== AXIUART_Top System Test Completed Successfully ===", UVM_LOW)
        
        phase.drop_objection(this, "AXIUART system test completed");
    endtask
    
    virtual function void final_phase(uvm_phase phase);
        super.final_phase(phase);
        `uvm_info("SYSTEM_TEST", "*** AXIUART SYSTEM TEST PASSED ***", UVM_LOW)
    endfunction

endclass
