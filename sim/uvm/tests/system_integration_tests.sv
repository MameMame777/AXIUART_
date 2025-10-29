`timescale 1ns / 1ps

`include "uvm_macros.svh"
import uvm_pkg::*;
import uart_axi4_test_pkg::*;

// System integration test combining UART and register functionality
class system_integration_test extends uvm_test;
    `uvm_component_utils(system_integration_test)
    
    uart_axi4_tb_env env;
    
    function new(string name = "system_integration_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        env = uart_axi4_tb_env::type_id::create("env", this);
        
        // Configure both agents as active
        uvm_config_db#(uvm_bitstream_t)::set(this, "env.axi_agent*", "is_active", UVM_ACTIVE);
        uvm_config_db#(uvm_bitstream_t)::set(this, "env.uart_agt*", "is_active", UVM_ACTIVE);
        
        `uvm_info("SYS_TEST", "System integration test build_phase completed", UVM_MEDIUM)
    endfunction

    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this, "Starting system integration test");
        
        `uvm_info("SYS_TEST", "Starting comprehensive system integration test", UVM_MEDIUM)
        
        // Wait for reset to complete
        @(posedge env.axi_agent.vif.aresetn);
        #1us;
        
        // Test sequence:
        // 1. Configure system through registers
        // 2. Send UART transactions and verify register counters
        // 3. Monitor system status during transactions
        // 4. Test error conditions and recovery
        
        fork
            configure_system_through_registers();
            monitor_system_status();
        join_none
        
        // Wait a bit for configuration
        #2us;
        
        fork
            send_uart_transactions_and_verify();
            test_error_conditions();
        join
        
        // Final status check
        check_final_system_state();
        
        `uvm_info("SYS_TEST", "System integration test completed", UVM_MEDIUM)
        phase.drop_objection(this);
    endtask
    
    // Configure system through register interface
    task configure_system_through_registers();
        axi4_lite_transaction reg_trans;
        
        `uvm_info("SYS_TEST", "Configuring system through registers", UVM_MEDIUM)
        
        // Enable the bridge
        reg_trans = axi4_lite_transaction::type_id::create("reg_trans");
        reg_trans.addr = 32'h0000_1000; // CONTROL register
        reg_trans.data = 32'h0000_0001; // Enable bridge
        reg_trans.trans_type = AXI_WRITE;
        reg_trans.strb = 4'hF;
        reg_trans.start_item(env.axi_agent.sequencer);
        reg_trans.finish_item(env.axi_agent.sequencer);
        
        #500ns;
        
        // Configure baud rate and timeout
        reg_trans = axi4_lite_transaction::type_id::create("reg_trans");
        reg_trans.addr = 32'h0000_1008; // CONFIG register
    const int unsigned timeout_cfg = 8'h5A;
    const int unsigned base_baud_div = UART_OVERSAMPLE; // Keep register programming aligned with DUT maximum rate
    reg_trans.data = (timeout_cfg << 8) | (base_baud_div & 8'hFF);
        reg_trans.trans_type = AXI_WRITE;
        reg_trans.strb = 4'hF;
        reg_trans.start_item(env.axi_agent.sequencer);
        reg_trans.finish_item(env.axi_agent.sequencer);
        
        #500ns;
        
        // Set debug mode
        reg_trans = axi4_lite_transaction::type_id::create("reg_trans");
        reg_trans.addr = 32'h0000_100C; // DEBUG register
        reg_trans.data = 32'h0000_0002; // Debug mode 2
        reg_trans.trans_type = AXI_WRITE;
        reg_trans.strb = 4'hF;
        reg_trans.start_item(env.axi_agent.sequencer);
        reg_trans.finish_item(env.axi_agent.sequencer);
        
        `uvm_info("SYS_TEST", "System configuration completed", UVM_MEDIUM)
    endtask
    
    // Send UART transactions and verify register counters
    task send_uart_transactions_and_verify();
        uart_transaction uart_trans;
        axi4_lite_transaction reg_read;
        bit [31:0] tx_count_before, rx_count_before;
        bit [31:0] tx_count_after, rx_count_after;
        int expected_tx_transactions = 5;
        int expected_rx_transactions = 3;
        
        `uvm_info("SYS_TEST", "Starting UART transaction test with counter verification", UVM_MEDIUM)
        
        // Read initial counter values
        read_register(32'h0000_1010, tx_count_before); // TX_COUNT
        read_register(32'h0000_1014, rx_count_before); // RX_COUNT
        
        `uvm_info("SYS_TEST", $sformatf("Initial counters: TX=%0d, RX=%0d", 
                  tx_count_before[15:0], rx_count_before[15:0]), UVM_MEDIUM)
        
        // Send write transactions (should increment TX counter)
        for (int i = 0; i < expected_tx_transactions; i++) begin
            uart_trans = uart_transaction::type_id::create("uart_trans");
            uart_trans.trans_type = UART_WRITE;
            uart_trans.address = 32'h1000_0000 + (i * 4);
            uart_trans.data = new[1];
            uart_trans.data[0] = 8'hA0 + i;
            
            uart_trans.start_item(env.uart_agt.sequencer);
            uart_trans.finish_item(env.uart_agt.sequencer);
            
            // Wait for transaction to complete
            #10us;
        end
        
        // Send read transactions (should increment RX counter)
        for (int i = 0; i < expected_rx_transactions; i++) begin
            uart_trans = uart_transaction::type_id::create("uart_trans");
            uart_trans.trans_type = UART_READ;
            uart_trans.address = 32'h1000_0100 + (i * 4);
            uart_trans.data = new[1]; // Will be filled by response
            
            uart_trans.start_item(env.uart_agt.sequencer);
            uart_trans.finish_item(env.uart_agt.sequencer);
            
            // Wait for transaction to complete
            #10us;
        end
        
        // Wait additional time for all transactions to complete
        #5us;
        
        // Read final counter values
        read_register(32'h0000_1010, tx_count_after); // TX_COUNT
        read_register(32'h0000_1014, rx_count_after); // RX_COUNT
        
        `uvm_info("SYS_TEST", $sformatf("Final counters: TX=%0d, RX=%0d", 
                  tx_count_after[15:0], rx_count_after[15:0]), UVM_MEDIUM)
        
        // Verify counter increments
        if ((tx_count_after[15:0] - tx_count_before[15:0]) != expected_tx_transactions) begin
            `uvm_error("SYS_TEST", $sformatf("TX counter mismatch: Expected increment=%0d, Actual increment=%0d",
                       expected_tx_transactions, (tx_count_after[15:0] - tx_count_before[15:0])))
        end else begin
            `uvm_info("SYS_TEST", "TX counter verification passed", UVM_MEDIUM)
        end
        
        if ((rx_count_after[15:0] - rx_count_before[15:0]) != expected_rx_transactions) begin
            `uvm_error("SYS_TEST", $sformatf("RX counter mismatch: Expected increment=%0d, Actual increment=%0d",
                       expected_rx_transactions, (rx_count_after[15:0] - rx_count_before[15:0])))
        end else begin
            `uvm_info("SYS_TEST", "RX counter verification passed", UVM_MEDIUM)
        end
    endtask
    
    // Monitor system status during operation
    task monitor_system_status();
        bit [31:0] status_reg;
        bit [31:0] fifo_stat_reg;
        
        `uvm_info("SYS_TEST", "Starting system status monitoring", UVM_MEDIUM)
        
        forever begin
            #1us;
            
            // Read status register
            read_register(32'h0000_1004, status_reg); // STATUS
            
            if (status_reg[0]) begin // bridge_busy
                `uvm_info("SYS_TEST", "Bridge is busy - transaction in progress", UVM_DEBUG)
            end
            
            if (status_reg[8:1] != 8'h00) begin // error_code
                `uvm_info("SYS_TEST", $sformatf("Error detected: code=0x%02X", status_reg[8:1]), UVM_MEDIUM)
            end
            
            // Read FIFO status
            read_register(32'h0000_1018, fifo_stat_reg); // FIFO_STAT
            
            if (fifo_stat_reg[0] || fifo_stat_reg[2]) begin // FIFO full flags
                `uvm_warning("SYS_TEST", $sformatf("FIFO full condition detected: 0x%02X", fifo_stat_reg[7:0]))
            end
        end
    endtask
    
    // Test error conditions and recovery
    task test_error_conditions();
        axi4_lite_transaction reg_trans;
        bit [31:0] status_before, status_after;
        bit [31:0] tx_count_reset, rx_count_reset;
        
        `uvm_info("SYS_TEST", "Testing error conditions and recovery", UVM_MEDIUM)
        
        // Wait for system to be idle
        #20us;
        
        // Read initial status
        read_register(32'h0000_1004, status_before);
        
        // Test invalid register access (should generate SLVERR)
        reg_trans = axi4_lite_transaction::type_id::create("reg_trans");
        reg_trans.addr = 32'h0000_1020; // Invalid register address
        reg_trans.data = 32'hDEADBEEF;
        reg_trans.trans_type = AXI_WRITE;
        reg_trans.strb = 4'hF;
        reg_trans.start_item(env.axi_agent.sequencer);
        reg_trans.finish_item(env.axi_agent.sequencer);
        
        if (reg_trans.resp != 2'b10) begin // Should be SLVERR
            `uvm_error("SYS_TEST", $sformatf("Invalid register access should return SLVERR, got 0x%02X", reg_trans.resp))
        end else begin
            `uvm_info("SYS_TEST", "Invalid register access correctly returned SLVERR", UVM_MEDIUM)
        end
        
        // Test statistics reset
        reg_trans = axi4_lite_transaction::type_id::create("reg_trans");
        reg_trans.addr = 32'h0000_1000; // CONTROL register
        reg_trans.data = 32'h0000_0003; // Enable + reset_stats
        reg_trans.trans_type = AXI_WRITE;
        reg_trans.strb = 4'hF;
        reg_trans.start_item(env.axi_agent.sequencer);
        reg_trans.finish_item(env.axi_agent.sequencer);
        
        #1us;
        
        // Verify counters were reset
        read_register(32'h0000_1010, tx_count_reset); // TX_COUNT
        read_register(32'h0000_1014, rx_count_reset); // RX_COUNT
        
        if (tx_count_reset[15:0] != 16'h0000 || rx_count_reset[15:0] != 16'h0000) begin
            `uvm_error("SYS_TEST", $sformatf("Statistics reset failed: TX=%0d, RX=%0d", 
                       tx_count_reset[15:0], rx_count_reset[15:0]))
        end else begin
            `uvm_info("SYS_TEST", "Statistics reset successful", UVM_MEDIUM)
        end
    endtask
    
    // Check final system state
    task check_final_system_state();
        bit [31:0] control_reg, status_reg, config_reg, version_reg;
        
        `uvm_info("SYS_TEST", "Performing final system state check", UVM_MEDIUM)
        
        read_register(32'h0000_1000, control_reg); // CONTROL
        read_register(32'h0000_1004, status_reg);  // STATUS
        read_register(32'h0000_1008, config_reg);  // CONFIG
        read_register(32'h0000_101C, version_reg); // VERSION
        
        `uvm_info("SYS_TEST", $sformatf("Final system state:"), UVM_MEDIUM)
        `uvm_info("SYS_TEST", $sformatf("  CONTROL: 0x%08X", control_reg), UVM_MEDIUM)
        `uvm_info("SYS_TEST", $sformatf("  STATUS:  0x%08X", status_reg), UVM_MEDIUM)
        `uvm_info("SYS_TEST", $sformatf("  CONFIG:  0x%08X", config_reg), UVM_MEDIUM)
        `uvm_info("SYS_TEST", $sformatf("  VERSION: 0x%08X", version_reg), UVM_MEDIUM)
        
        // Verify version register
        if (version_reg != 32'h0001_0000) begin
            `uvm_error("SYS_TEST", $sformatf("Version register mismatch: Expected=0x00010000, Got=0x%08X", version_reg))
        end
        
        // Verify system is still enabled
        if (control_reg[0] != 1'b1) begin
            `uvm_error("SYS_TEST", "System should still be enabled")
        end
    endtask
    
    // Helper function to read register
    task read_register(input bit [31:0] addr, output bit [31:0] data);
        axi4_lite_transaction reg_read;
        
        reg_read = axi4_lite_transaction::type_id::create("reg_read");
        reg_read.addr = addr;
        reg_read.trans_type = AXI_READ;
        reg_read.start_item(env.axi_agent.sequencer);
        reg_read.finish_item(env.axi_agent.sequencer);
        
        data = reg_read.data;
    endtask
endclass

// UART-Register concurrent access test
class uart_register_concurrent_test extends uvm_test;
    `uvm_component_utils(uart_register_concurrent_test)
    
    uart_axi4_tb_env env;
    
    function new(string name = "uart_register_concurrent_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = uart_axi4_tb_env::type_id::create("env", this);
        
        uvm_config_db#(uvm_bitstream_t)::set(this, "env.axi_agent*", "is_active", UVM_ACTIVE);
        uvm_config_db#(uvm_bitstream_t)::set(this, "env.uart_agt*", "is_active", UVM_ACTIVE);
    endfunction

    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this, "Starting concurrent access test");
        
        `uvm_info("CONCURRENT_TEST", "Starting UART-Register concurrent access test", UVM_MEDIUM)
        
        // Wait for reset
        @(posedge env.axi_agent.vif.aresetn);
        #1us;
        
        // Configure system
        configure_system();
        #2us;
        
        // Run concurrent UART and register operations
        fork
            continuous_uart_transactions();
            continuous_register_monitoring();
            periodic_configuration_changes();
        join_any
        
        // Wait for operations to complete
        #50us;
        
        `uvm_info("CONCURRENT_TEST", "Concurrent access test completed", UVM_MEDIUM)
        phase.drop_objection(this);
    endtask
    
    task configure_system();
        axi4_lite_transaction reg_trans;
        
        reg_trans = axi4_lite_transaction::type_id::create("reg_trans");
        reg_trans.addr = 32'h0000_1000; // CONTROL
        reg_trans.data = 32'h0000_0001; // Enable
        reg_trans.trans_type = AXI_WRITE;
        reg_trans.strb = 4'hF;
        reg_trans.start_item(env.axi_agent.sequencer);
        reg_trans.finish_item(env.axi_agent.sequencer);
    endtask
    
    task continuous_uart_transactions();
        uart_transaction uart_trans;
        
        for (int i = 0; i < 20; i++) begin
            uart_trans = uart_transaction::type_id::create("uart_trans");
            uart_trans.trans_type = (i % 2) ? UART_READ : UART_WRITE;
            uart_trans.address = 32'h2000_0000 + (i * 4);
            uart_trans.data = new[1];
            uart_trans.data[0] = 8'hB0 + i;
            
            uart_trans.start_item(env.uart_agt.sequencer);
            uart_trans.finish_item(env.uart_agt.sequencer);
            
            #($urandom_range(5000, 15000)); // Random delay
        end
    endtask
    
    task continuous_register_monitoring();
        bit [31:0] status_data, counter_data;
        
        repeat (100) begin
            // Read status register
            read_register(32'h0000_1004, status_data);
            
            // Read counters
            read_register(32'h0000_1010, counter_data);
            read_register(32'h0000_1014, counter_data);
            
            #($urandom_range(1000, 3000)); // Random monitoring interval
        end
    endtask
    
    task periodic_configuration_changes();
        axi4_lite_transaction reg_trans;
        bit [3:0] debug_mode = 0;
        
        repeat (10) begin
            #10us;
            
            // Change debug mode
            debug_mode = (debug_mode + 1) % 4;
            reg_trans = axi4_lite_transaction::type_id::create("reg_trans");
            reg_trans.addr = 32'h0000_100C; // DEBUG
            reg_trans.data = {28'h0, debug_mode};
            reg_trans.trans_type = AXI_WRITE;
            reg_trans.strb = 4'hF;
            reg_trans.start_item(env.axi_agent.sequencer);
            reg_trans.finish_item(env.axi_agent.sequencer);
        end
    endtask
    
    task read_register(input bit [31:0] addr, output bit [31:0] data);
        axi4_lite_transaction reg_read;
        
        reg_read = axi4_lite_transaction::type_id::create("reg_read");
        reg_read.addr = addr;
        reg_read.trans_type = AXI_READ;
        reg_read.start_item(env.axi_agent.sequencer);
        reg_read.finish_item(env.axi_agent.sequencer);
        
        data = reg_read.data;
    endtask
endclass
