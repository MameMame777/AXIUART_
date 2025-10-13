`timescale 1ns / 1ps

// UART AXI4 Bridge Control Test
// Created: October 13, 2025
// Purpose: Bridge enable/disable and control register verification
// Compliant with Phase 4.1.1 specifications

class uart_axi4_bridge_control_test extends enhanced_uart_axi4_base_test;
    
    `uvm_component_utils(uart_axi4_bridge_control_test)
    
    function new(string name = "uart_axi4_bridge_control_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        configure_test_specific_reporting();
        cfg.num_transactions = 25;
        cfg.enable_protocol_checking = 1'b1;
        cfg.enable_bridge_control_testing = 1'b1;
        
        `uvm_info("BRIDGE_CONTROL_TEST", "Bridge control test configuration complete", UVM_LOW)
    endfunction
    
    virtual function void configure_test_specific_reporting();
        // Bridge control specific reporting
        this.set_report_id_verbosity_hier("BRIDGE_CONTROL*", UVM_MEDIUM);
        this.set_report_id_verbosity_hier("BRIDGE_ENABLE*", UVM_MEDIUM);
        this.set_report_id_verbosity_hier("BRIDGE_DISABLE*", UVM_MEDIUM);
        this.set_report_id_verbosity_hier("CONTROL_REG*", UVM_HIGH);
        
        `uvm_info("BRIDGE_CONTROL_CONFIG", "Bridge control specific reporting configured", UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        uart_axi4_bridge_control_sequence bridge_seq;
        phase.raise_objection(this);
        
        `uvm_info("BRIDGE_CONTROL_TEST", "Starting bridge control verification", UVM_LOW)
        
        // Wait for reset deassertion
        wait(cfg.bridge_status_vif.rst_n);
        #1000ns;
        
        // Create and execute bridge control sequence
        bridge_seq = uart_axi4_bridge_control_sequence::type_id::create("bridge_seq");
        if (bridge_seq == null) begin
            `uvm_fatal("BRIDGE_CONTROL_TEST", "Failed to create bridge_control_sequence")
        end
        
        bridge_seq.start(env.uart_agt.sequencer);
        
        // Allow sufficient time for bridge control verification
        #6000000ns;
        
        `uvm_info("BRIDGE_CONTROL_TEST", "Bridge control verification completed", UVM_LOW)
        phase.drop_objection(this);
    endtask
    
    virtual function void final_phase(uvm_phase phase);
        super.final_phase(phase);
        
        `uvm_info("BRIDGE_CONTROL_SUMMARY", "=== BRIDGE CONTROL TEST SUMMARY ===", UVM_LOW)
        `uvm_info("BRIDGE_CONTROL_SUMMARY", $sformatf("Transactions: %0d", cfg.num_transactions), UVM_LOW)
        `uvm_info("BRIDGE_CONTROL_SUMMARY", "Bridge control testing: ENABLED", UVM_LOW)
        `uvm_info("BRIDGE_CONTROL_SUMMARY", "Protocol checking: ENABLED", UVM_LOW)
    endfunction
    
endclass : uart_axi4_bridge_control_test