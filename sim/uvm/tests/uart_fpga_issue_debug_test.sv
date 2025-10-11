`timescale 1ns / 1ps

// UVM Test for FPGA Hardware Issue Investigation
// Simplified test to match the existing structure

class uart_fpga_issue_debug_test extends enhanced_uart_axi4_base_test;

    // UVM factory registration macro
    `uvm_component_utils(uart_fpga_issue_debug_test)

    // Constructor
    function new(string name = "uart_fpga_issue_debug_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Build phase - configure test environment
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        configure_test_specific_reporting();
        
        // Configure environment for debugging
        cfg.enable_coverage = 1;
        cfg.enable_scoreboard = 1;
        cfg.enable_protocol_checking = 1;
        
        uvm_config_db#(uart_axi4_env_config)::set(this, "env", "config", cfg);
        `uvm_info("FPGA_DEBUG", "FPGA issue debug test configured", UVM_LOW)
    endfunction

    // Main test sequence
    virtual task main_phase(uvm_phase phase);
        simple_debug_write_sequence_20250923 debug_seq;
        fpga_register_read_sequence fpga_seq;
        
        phase.raise_objection(this);
        
        `uvm_info("FPGA_DEBUG", "=== FPGA Issue Investigation Test Started ===", UVM_LOW)
        
        // Wait for reset deassertion
        #1000ns;
        
        // Run basic debug sequence first
        debug_seq = simple_debug_write_sequence_20250923::type_id::create("debug_seq");
        debug_seq.start(env.uart_agent.sequencer);
        
        // Wait between sequences
        #5000ns;
        
        // Run FPGA-specific register read sequence
        fpga_seq = fpga_register_read_sequence::type_id::create("fpga_seq");
        fpga_seq.start(env.uart_agent.sequencer);
        
        // Wait for completion
        #10000ns;
        
        `uvm_info("FPGA_DEBUG", "=== FPGA Issue Investigation Test Completed ===", UVM_LOW)
        
        phase.drop_objection(this);
    endtask

endclass

// Specialized sequence to test FPGA register reads
class fpga_register_read_sequence extends uvm_sequence #(uart_axi4_transaction);
    `uvm_object_utils(fpga_register_read_sequence)
    
    function new(string name = "fpga_register_read_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_axi4_transaction req;
        
        `uvm_info("FPGA_SEQ", "Starting FPGA register read sequence", UVM_LOW)
        
        // Read REG_CONTROL (0x00001000) - This generated STATUS 0x80 in FPGA
        req = uart_axi4_transaction::type_id::create("req");
        req.cmd = 8'hA0;          // Read command
        req.address = 32'h00001000; // REG_CONTROL
        
        `uvm_info("FPGA_SEQ", $sformatf("Reading REG_CONTROL (0x%08X)", req.address), UVM_MEDIUM)
        
        start_item(req);
        finish_item(req);
        
        #2000ns;
        
        // Read REG_STATUS (0x00001004)
        req = uart_axi4_transaction::type_id::create("req");
        req.cmd = 8'hA0;
        req.address = 32'h00001004; // REG_STATUS
        
        `uvm_info("FPGA_SEQ", $sformatf("Reading REG_STATUS (0x%08X)", req.address), UVM_MEDIUM)
        
        start_item(req);
        finish_item(req);
        
        #2000ns;
        
        // Read REG_VERSION (0x0000101C)
        req = uart_axi4_transaction::type_id::create("req");
        req.cmd = 8'hA0;
        req.address = 32'h0000101C; // REG_VERSION
        
        `uvm_info("FPGA_SEQ", $sformatf("Reading REG_VERSION (0x%08X)", req.address), UVM_MEDIUM)
        
        start_item(req);
        finish_item(req);
        
        `uvm_info("FPGA_SEQ", "FPGA register read sequence completed", UVM_LOW)
        
    endtask
    
endclass
