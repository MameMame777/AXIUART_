`timescale 1ns / 1ps

`include "uvm_macros.svh"
import uvm_pkg::*;
import uart_axi4_test_pkg::*;

// Base test class for register block testing
class register_block_base_test extends uvm_test;
    `uvm_component_utils(register_block_base_test)
    
    uart_axi4_tb_env env;
    
    function new(string name = "register_block_base_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Create environment
        env = uart_axi4_tb_env::type_id::create("env", this);
        
        // Configure environment for register testing
        uvm_config_db#(uvm_bitstream_t)::set(this, "env.axi_agent*", "is_active", UVM_ACTIVE);
        uvm_config_db#(uvm_bitstream_t)::set(this, "env.uart_agt*", "is_active", UVM_ACTIVE);
        
        `uvm_info("REG_TEST", "Register block base test build_phase completed", UVM_MEDIUM)
    endfunction

    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        uvm_top.print_topology();
    endfunction
endclass

// Basic register read/write test
class register_block_basic_test extends register_block_base_test;
    `uvm_component_utils(register_block_basic_test)

    function new(string name = "register_block_basic_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        register_basic_rw_sequence reg_seq;
        int num_iterations = 10;
        
        phase.raise_objection(this, "Starting register basic test");
        
        `uvm_info("REG_TEST", "Starting register block basic test", UVM_MEDIUM)
        
        // Wait for reset to complete
        @(posedge env.axi_agent.vif.aresetn);
        #100ns;
        
        // Run multiple iterations of register R/W test
        for (int i = 0; i < num_iterations; i++) begin
            reg_seq = register_basic_rw_sequence::type_id::create("reg_seq");
            if (!reg_seq.randomize()) begin
                `uvm_error("REG_TEST", "Failed to randomize register sequence")
            end
            
            reg_seq.start(env.axi_agent.sequencer);
            
            // Small delay between transactions
            #1us;
        end
        
        `uvm_info("REG_TEST", "Register block basic test completed", UVM_MEDIUM)
        phase.drop_objection(this);
    endtask
endclass

// Register reset value test
class register_block_reset_test extends register_block_base_test;
    `uvm_component_utils(register_block_reset_test)

    function new(string name = "register_block_reset_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        register_reset_sequence reset_seq;
        
        phase.raise_objection(this, "Starting register reset test");
        
        `uvm_info("REG_TEST", "Starting register block reset test", UVM_MEDIUM)
        
        // Wait for reset to complete
        @(posedge env.axi_agent.vif.aresetn);
        #100ns;
        
        // Check all register reset values
        reset_seq = register_reset_sequence::type_id::create("reset_seq");
        reset_seq.start(env.axi_agent.sequencer);
        
        `uvm_info("REG_TEST", "Register block reset test completed", UVM_MEDIUM)
        phase.drop_objection(this);
    endtask
endclass

// Register access protection test
class register_block_access_test extends register_block_base_test;
    `uvm_component_utils(register_block_access_test)

    function new(string name = "register_block_access_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        register_access_test_sequence access_seq;
        
        phase.raise_objection(this, "Starting register access test");
        
        `uvm_info("REG_TEST", "Starting register block access protection test", UVM_MEDIUM)
        
        // Wait for reset to complete
        @(posedge env.axi_agent.vif.aresetn);
        #100ns;
        
        // Test register access protections
        access_seq = register_access_test_sequence::type_id::create("access_seq");
        access_seq.start(env.axi_agent.sequencer);
        
        `uvm_info("REG_TEST", "Register block access protection test completed", UVM_MEDIUM)
        phase.drop_objection(this);
    endtask
endclass

// Comprehensive register test combining all scenarios
class register_block_comprehensive_test extends register_block_base_test;
    `uvm_component_utils(register_block_comprehensive_test)

    function new(string name = "register_block_comprehensive_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        register_reset_sequence reset_seq;
        register_basic_rw_sequence rw_seq;
        register_access_test_sequence access_seq;
        
        phase.raise_objection(this, "Starting comprehensive register test");
        
        `uvm_info("REG_TEST", "Starting comprehensive register block test", UVM_MEDIUM)
        
        // Wait for reset to complete
        @(posedge env.axi_agent.vif.aresetn);
        #100ns;
        
        // Phase 1: Check reset values
        `uvm_info("REG_TEST", "Phase 1: Reset value verification", UVM_MEDIUM)
        reset_seq = register_reset_sequence::type_id::create("reset_seq");
        reset_seq.start(env.axi_agent.sequencer);
        #1us;
        
        // Phase 2: Basic read/write functionality
        `uvm_info("REG_TEST", "Phase 2: Basic read/write testing", UVM_MEDIUM)
        repeat(20) begin
            rw_seq = register_basic_rw_sequence::type_id::create("rw_seq");
            if (!rw_seq.randomize()) begin
                `uvm_error("REG_TEST", "Failed to randomize R/W sequence")
            end
            rw_seq.start(env.axi_agent.sequencer);
            #500ns;
        end
        
        // Phase 3: Access protection testing
        `uvm_info("REG_TEST", "Phase 3: Access protection testing", UVM_MEDIUM)
        access_seq = register_access_test_sequence::type_id::create("access_seq");
        access_seq.start(env.axi_agent.sequencer);
        #1us;
        
        // Phase 4: Register field interaction testing
        `uvm_info("REG_TEST", "Phase 4: Register field interaction testing", UVM_MEDIUM)
        test_control_register_behavior();
        test_config_register_behavior();
        
        `uvm_info("REG_TEST", "Comprehensive register block test completed", UVM_MEDIUM)
        phase.drop_objection(this);
    endtask
    
    // Test specific CONTROL register behavior
    task test_control_register_behavior();
        axi4_lite_transaction write_trans, read_trans;
        bit [31:0] REG_CONTROL = 32'h0000_1000;
        
        `uvm_info("REG_TEST", "Testing CONTROL register specific behavior", UVM_MEDIUM)
        
        // Test enable bit (bit 0)
        write_trans = axi4_lite_transaction::type_id::create("write_trans");
        write_trans.addr = REG_CONTROL;
        write_trans.data = 32'h0000_0001; // Set enable bit
        write_trans.trans_type = AXI_WRITE;
        write_trans.strb = 4'hF;
        write_trans.start_item(env.axi_agent.sequencer);
        write_trans.finish_item(env.axi_agent.sequencer);
        
        #100ns;
        
        // Read back and verify enable bit
        read_trans = axi4_lite_transaction::type_id::create("read_trans");
        read_trans.addr = REG_CONTROL;
        read_trans.trans_type = AXI_READ;
        read_trans.start_item(env.axi_agent.sequencer);
        read_trans.finish_item(env.axi_agent.sequencer);
        
        if (read_trans.data[0] !== 1'b1) begin
            `uvm_error("REG_TEST", $sformatf("CONTROL enable bit not set correctly: 0x%08X", read_trans.data))
        end
        
        // Test reset_stats bit (bit 1) - should be W1C (write 1 to clear, always reads 0)
        write_trans = axi4_lite_transaction::type_id::create("write_trans");
        write_trans.addr = REG_CONTROL;
        write_trans.data = 32'h0000_0003; // Set both enable and reset_stats
        write_trans.trans_type = AXI_WRITE;
        write_trans.strb = 4'hF;
        write_trans.start_item(env.axi_agent.sequencer);
        write_trans.finish_item(env.axi_agent.sequencer);
        
        #100ns;
        
        // Read back - reset_stats should always read as 0
        read_trans = axi4_lite_transaction::type_id::create("read_trans");
        read_trans.addr = REG_CONTROL;
        read_trans.trans_type = AXI_READ;
        read_trans.start_item(env.axi_agent.sequencer);
        read_trans.finish_item(env.axi_agent.sequencer);
        
        if (read_trans.data[1] !== 1'b0) begin
            `uvm_error("REG_TEST", $sformatf("CONTROL reset_stats bit should read as 0: 0x%08X", read_trans.data))
        end
        
        `uvm_info("REG_TEST", "CONTROL register behavior test completed", UVM_MEDIUM)
    endtask
    
    // Test specific CONFIG register behavior
    task test_config_register_behavior();
        axi4_lite_transaction write_trans, read_trans;
        bit [31:0] REG_CONFIG = 32'h0000_1008;
        bit [15:0] test_baud_config = 16'hA5C3;
        
        `uvm_info("REG_TEST", "Testing CONFIG register specific behavior", UVM_MEDIUM)
        
        // Write configuration values
        write_trans = axi4_lite_transaction::type_id::create("write_trans");
        write_trans.addr = REG_CONFIG;
        write_trans.data = {16'h0000, test_baud_config}; // Upper 16 bits should be ignored
        write_trans.trans_type = AXI_WRITE;
        write_trans.strb = 4'hF;
        write_trans.start_item(env.axi_agent.sequencer);
        write_trans.finish_item(env.axi_agent.sequencer);
        
        #100ns;
        
        // Read back and verify
        read_trans = axi4_lite_transaction::type_id::create("read_trans");
        read_trans.addr = REG_CONFIG;
        read_trans.trans_type = AXI_READ;
        read_trans.start_item(env.axi_agent.sequencer);
        read_trans.finish_item(env.axi_agent.sequencer);
        
        if (read_trans.data[15:0] !== test_baud_config || read_trans.data[31:16] !== 16'h0000) begin
            `uvm_error("REG_TEST", $sformatf("CONFIG register mismatch: Expected=0x%08X, Got=0x%08X", 
                       {16'h0000, test_baud_config}, read_trans.data))
        end
        
        `uvm_info("REG_TEST", "CONFIG register behavior test completed", UVM_MEDIUM)
    endtask
endclass
