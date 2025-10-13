`timescale 1ns / 1ps

// UART AXI4 Error Protocol Test
// Created: October 13, 2025
// Purpose: Error handling and protocol violation verification
// Compliant with Phase 4.1.1 specifications

class uart_axi4_error_protocol_test extends enhanced_uart_axi4_base_test;
    
    `uvm_component_utils(uart_axi4_error_protocol_test)
    
    function new(string name = "uart_axi4_error_protocol_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        configure_test_specific_reporting();
        cfg.num_transactions = 30;
        cfg.enable_protocol_checking = 1'b1;
        cfg.enable_error_injection = 1'b1;
        
        `uvm_info("ERROR_PROTOCOL_TEST", "Error protocol test configuration complete", UVM_LOW)
    endfunction
    
    virtual function void configure_test_specific_reporting();
        // Error protocol specific reporting
        this.set_report_id_verbosity_hier("ERROR_PROTOCOL*", UVM_MEDIUM);
        this.set_report_id_verbosity_hier("AXI4_ERROR*", UVM_MEDIUM);
        this.set_report_id_verbosity_hier("PROTOCOL_VIOLATION*", UVM_HIGH);
        this.set_report_id_verbosity_hier("ERROR_INJECTION*", UVM_HIGH);
        
        `uvm_info("ERROR_PROTOCOL_CONFIG", "Error protocol specific reporting configured", UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        uart_axi4_error_protocol_sequence error_seq;
        phase.raise_objection(this);
        
        `uvm_info("ERROR_PROTOCOL_TEST", "Starting error protocol verification", UVM_LOW)
        
        // Wait for reset deassertion
        wait(cfg.bridge_status_vif.rst_n);
        #1000ns;
        
        // Create and execute error protocol sequence
        error_seq = uart_axi4_error_protocol_sequence::type_id::create("error_seq");
        if (error_seq == null) begin
            `uvm_fatal("ERROR_PROTOCOL_TEST", "Failed to create error_protocol_sequence")
        end
        
        error_seq.start(env.uart_agt.sequencer);
        
        // Allow sufficient time for error handling verification
        #7000000ns;
        
        `uvm_info("ERROR_PROTOCOL_TEST", "Error protocol verification completed", UVM_LOW)
        phase.drop_objection(this);
    endtask
    
    virtual function void final_phase(uvm_phase phase);
        super.final_phase(phase);
        
        `uvm_info("ERROR_PROTOCOL_SUMMARY", "=== ERROR PROTOCOL TEST SUMMARY ===", UVM_LOW)
        `uvm_info("ERROR_PROTOCOL_SUMMARY", $sformatf("Transactions: %0d", cfg.num_transactions), UVM_LOW)
        `uvm_info("ERROR_PROTOCOL_SUMMARY", "Error injection: ENABLED", UVM_LOW)
        `uvm_info("ERROR_PROTOCOL_SUMMARY", "Protocol checking: ENABLED", UVM_LOW)
    endfunction
    
endclass : uart_axi4_error_protocol_test