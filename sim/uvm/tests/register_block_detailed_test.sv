//==============================================================================
// Register Block Detailed Verification Test
// 
// Purpose: Comprehensive testing of Register_Block.sv internal logic
//          This test fills the gap in current UVM testing which only covers
//          high-level communication protocols
//
// Test Coverage:
// - Individual register read/write operations (0x1000-0x1100)
// - Address validation functions (is_read_access_valid/is_write_access_valid)
// - Invalid address error responses
// - AXI4-Lite protocol compliance at signal level
// - Register value accuracy verification
// - Boundary condition testing
//
// Author: UVM Verification Team
// Date: 2025-10-09
// Version: 1.0
//==============================================================================

// This test must be included in uart_axi4_test_pkg.sv
class register_block_detailed_test extends enhanced_uart_axi4_base_test;
    `uvm_component_utils(register_block_detailed_test)
    
    function new(string name = "register_block_detailed_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Configure environment for detailed register testing
        cfg.num_transactions = 20; // Comprehensive test set
        cfg.enable_coverage = 1;
        cfg.enable_scoreboard = 1;
        cfg.enable_protocol_checking = 1;
        
        // Extended timeouts for detailed verification
        cfg.frame_timeout_ns = 50_000_000; // 50ms per operation
        cfg.system_timeout_cycles = 5000;
        
        `uvm_info("REG_TEST", "Register Block Detailed Test configured", UVM_MEDIUM)
        `uvm_info("REG_TEST", "Target: Comprehensive Register_Block.sv verification", UVM_MEDIUM)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        register_block_comprehensive_sequence reg_seq;
        
        phase.raise_objection(this);
        
        `uvm_info("REG_TEST", "=======================================================", UVM_LOW)
        `uvm_info("REG_TEST", "    REGISTER BLOCK DETAILED VERIFICATION TEST", UVM_LOW)
        `uvm_info("REG_TEST", "=======================================================", UVM_LOW)
        `uvm_info("REG_TEST", "Testing individual Register_Block.sv functions", UVM_LOW)
        `uvm_info("REG_TEST", "Gap filled: Current UVM only tests high-level protocols", UVM_LOW)
        
        // Wait for system initialization
        #(5us);
        `uvm_info("REG_TEST", "System initialization completed, starting register tests", UVM_MEDIUM)
        
        // Execute comprehensive register testing sequence
        reg_seq = register_block_comprehensive_sequence::type_id::create("reg_seq");
        reg_seq.start(env.uart_agt.sequencer);
        
        // Allow completion time for detailed analysis
        #(100us);
        
        `uvm_info("REG_TEST", "=== Register Block Detailed Test Completed ===", UVM_LOW)
        `uvm_info("REG_TEST", "Check detailed logs for register function verification", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        
        `uvm_info("REG_TEST", "=== REGISTER BLOCK VERIFICATION SUMMARY ===", UVM_LOW)
        `uvm_info("REG_TEST", "Tested: All individual register read/write operations", UVM_LOW)
        `uvm_info("REG_TEST", "Tested: Address validation functions", UVM_LOW)
        `uvm_info("REG_TEST", "Tested: Invalid address error handling", UVM_LOW)
        `uvm_info("REG_TEST", "Tested: AXI4-Lite signal-level compliance", UVM_LOW)
        `uvm_info("REG_TEST", "Tested: Register value accuracy", UVM_LOW)
        
        if (uvm_report_server::get_server().get_severity_count(UVM_ERROR) == 0) begin
            `uvm_info("REG_TEST", "笨・REGISTER BLOCK VERIFICATION PASSED", UVM_LOW)
        end else begin
            `uvm_error("REG_TEST", "笶・REGISTER BLOCK VERIFICATION FAILED")
        end
    endfunction
    
endclass : register_block_detailed_test
