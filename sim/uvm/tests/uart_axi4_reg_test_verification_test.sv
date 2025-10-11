// =============================================================================
// uart_axi4_reg_test_verification_test.sv
// REG_TEST_0-3 Register Verification Test
// 
// Purpose: UVM test for REG_TEST_0, REG_TEST_1, REG_TEST_2, REG_TEST_3 registers
// =============================================================================

class uart_axi4_reg_test_verification_test extends enhanced_uart_axi4_base_test;

    `uvm_component_utils(uart_axi4_reg_test_verification_test)

    function new(string name = "uart_axi4_reg_test_verification_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        configure_test_specific_reporting();
        
        // Set test-specific configuration
        uvm_config_db#(int)::set(this, "*", "test_duration_ns", 50_000_000); // 50ms
        uvm_config_db#(string)::set(this, "*", "test_name", "REG_TEST Verification");
        
        `uvm_info(get_type_name(), "REG_TEST Verification Test Build Phase", UVM_LOW)
    endfunction

    virtual task run_phase(uvm_phase phase);
        uart_axi4_reg_test_sequence reg_test_seq;
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "=== REG_TEST Register Verification Test ===", UVM_LOW)
        
        // Wait for reset deassertion using bridge status interface from config
        wait(cfg.bridge_status_vif.rst_n);
        #1000ns;
        
        // Create and run the REG_TEST verification sequence
        reg_test_seq = uart_axi4_reg_test_sequence::type_id::create("reg_test_seq");
        reg_test_seq.start(env.uart_agt.sequencer);
        
        // Additional delay for completion
        #1000000ns;
        
        `uvm_info(get_type_name(), "=== REG_TEST Register Verification Test Complete ===", UVM_LOW)
        
        phase.drop_objection(this);
    endtask

endclass
