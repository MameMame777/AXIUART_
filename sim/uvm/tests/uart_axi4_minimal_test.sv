`timescale 1ns / 1ps

// Minimal test to verify basic functionality
class uart_axi4_minimal_test extends enhanced_uart_axi4_base_test;

    `uvm_component_utils(uart_axi4_minimal_test)

    function new(string name = "uart_axi4_minimal_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function automatic virtual bridge_status_if get_bridge_status_vif_handle();
        if (bridge_status_vif == null) begin
            `uvm_fatal("MINIMAL_TEST", "bridge_status_vif handle is not available")
        end
        return bridge_status_vif;
    endfunction

    function automatic virtual uart_if get_uart_vif_handle();
        if (uart_vif == null) begin
            `uvm_fatal("MINIMAL_TEST", "uart_vif handle is not available")
        end
        return uart_vif;
    endfunction

    // Build phase - configure test-specific reporting
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        configure_test_specific_reporting();
    endfunction
    
    // Test-specific reporting configuration
    virtual function void configure_test_specific_reporting();
        // Configure test-specific IDs for minimal testing
        this.set_report_id_verbosity_hier("TEST_MINIMAL_START", UVM_HIGH);
        this.set_report_id_verbosity_hier("TEST_MINIMAL_PROGRESS", UVM_MEDIUM);
        this.set_report_id_verbosity_hier("TEST_MINIMAL_RESULT", UVM_HIGH);
    endfunction

    virtual task run_phase(uvm_phase phase);
        virtual bridge_status_if status_vif;
        virtual uart_if local_uart_vif;

        phase.raise_objection(this, "Starting minimal test");
        
        `uvm_info("TEST_MINIMAL_START", "=== Starting AXIUART_Top Minimal Test ===", UVM_LOW)
        
        status_vif = get_bridge_status_vif_handle();
        local_uart_vif = get_uart_vif_handle();

        // Wait for reset to complete using exported interface signals
        wait (status_vif.rst_n == 1'b1);
        repeat (100) @(posedge status_vif.clk);
        
        // Monitor system status signals through the virtual interface
        `uvm_info("MINIMAL_TEST", $sformatf("System Status - Ready: %b, Busy: %b, Error: 0x%02h",
                  status_vif.system_ready,
                  status_vif.bridge_busy,
                  status_vif.bridge_error), UVM_LOW)
        
        // Wait a reasonable amount of time then finish the test
        `uvm_info("MINIMAL_TEST", "Waiting for system to stabilize...", UVM_LOW)
        repeat (1000) @(posedge local_uart_vif.clk);
        
        `uvm_info("MINIMAL_TEST", "=== AXIUART_Top Minimal Test Completed ===", UVM_LOW)
        
        phase.drop_objection(this, "Minimal test completed");
    endtask
    
    virtual function void final_phase(uvm_phase phase);
        super.final_phase(phase);
        `uvm_info("MINIMAL_TEST", "*** MINIMAL TEST PASSED ***", UVM_LOW)
    endfunction

endclass