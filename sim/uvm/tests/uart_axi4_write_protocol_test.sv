`timescale 1ns / 1ps

// UART AXI4 Write Protocol Test
// Created: October 13, 2025
// Purpose: Protocol-specific write operation verification
// Compliant with Phase 4.1.1 specifications

class uart_axi4_write_protocol_test extends enhanced_uart_axi4_base_test;
    
    `uvm_component_utils(uart_axi4_write_protocol_test)
    
    function new(string name = "uart_axi4_write_protocol_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        configure_test_specific_reporting();
        cfg.num_transactions = 50;
        cfg.enable_protocol_checking = 1'b1;
        
        `uvm_info("WRITE_PROTOCOL_TEST", "Write protocol test configuration complete", UVM_LOW)
    endfunction
    
    virtual function void configure_test_specific_reporting();
        // Write protocol specific reporting
        this.set_report_id_verbosity_hier("WRITE_PROTOCOL*", UVM_MEDIUM);
        this.set_report_id_verbosity_hier("AXI4_WRITE*", UVM_MEDIUM);
        this.set_report_id_verbosity_hier("PROTOCOL_CHECK*", UVM_HIGH);
        
        `uvm_info("WRITE_PROTOCOL_CONFIG", "Write protocol specific reporting configured", UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        uart_axi4_write_protocol_sequence write_seq;
        phase.raise_objection(this);
        
        `uvm_info("WRITE_PROTOCOL_TEST", "Starting write protocol verification", UVM_LOW)
        
        // Wait for reset deassertion
        wait(cfg.bridge_status_vif.rst_n);
        #1000ns;
        
        // Create and execute write protocol sequence
        write_seq = uart_axi4_write_protocol_sequence::type_id::create("write_seq");
        if (write_seq == null) begin
            `uvm_fatal("WRITE_PROTOCOL_TEST", "Failed to create write_protocol_sequence")
        end
        
        write_seq.start(env.uart_agt.sequencer);
        
        // Allow sufficient time for protocol completion
        #5000000ns;
        
        `uvm_info("WRITE_PROTOCOL_TEST", "Write protocol verification completed", UVM_LOW)
        phase.drop_objection(this);
    endtask
    
    virtual function void final_phase(uvm_phase phase);
        super.final_phase(phase);
        
        `uvm_info("WRITE_PROTOCOL_SUMMARY", "=== WRITE PROTOCOL TEST SUMMARY ===", UVM_LOW)
        `uvm_info("WRITE_PROTOCOL_SUMMARY", $sformatf("Transactions: %0d", cfg.num_transactions), UVM_LOW)
        `uvm_info("WRITE_PROTOCOL_SUMMARY", "Protocol checking: ENABLED", UVM_LOW)
    endfunction
    
endclass : uart_axi4_write_protocol_test