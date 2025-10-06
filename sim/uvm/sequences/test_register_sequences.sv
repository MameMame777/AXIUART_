`timescale 1ns / 1ps

`include "uvm_macros.svh"
import uvm_pkg::*;
import uart_axi4_test_pkg::*;

// Test register address definitions (newly added in Register_Block.sv)
// Using REG_BASE_ADDR from register_sequences.sv
localparam bit [31:0] REG_TEST_0    = REG_BASE_ADDR + 32'h020; // 0x1020
localparam bit [31:0] REG_TEST_1    = REG_BASE_ADDR + 32'h024; // 0x1024
localparam bit [31:0] REG_TEST_2    = REG_BASE_ADDR + 32'h028; // 0x1028
localparam bit [31:0] REG_TEST_3    = REG_BASE_ADDR + 32'h02C; // 0x102C

// Base class for test register sequences
virtual class test_register_sequence_base extends uvm_sequence #(uart_frame_transaction);
    
    function new(string name = "test_register_sequence_base");
        super.new(name);
    endfunction

    // Helper function to create write transaction
    protected task automatic write_test_register(bit [31:0] addr, 
                                                  bit [31:0] data,
                                                  string label = "test_reg_write");
        uart_frame_transaction req;
        req = uart_frame_transaction::type_id::create(label);
        start_item(req);
        
        req.is_write = 1;
        req.auto_increment = 0;
        req.size = 2'b10; // 4 bytes
        req.length = 4'h0;
        req.addr = addr;
        req.sof = SOF_HOST_TO_DEVICE;
        req.direction = UART_RX;
        req.error_inject = 0;
        req.expect_error = 0;
        
        // Set 4-byte data
        req.data = new[4];
        req.data[0] = data[7:0];
        req.data[1] = data[15:8];
        req.data[2] = data[23:16];
        req.data[3] = data[31:24];
        
        req.build_cmd();
        req.calculate_crc();
        
        finish_item(req);
        
        `uvm_info(get_type_name(), 
                  $sformatf("Write 0x%08X to test register 0x%08X", data, addr), 
                  UVM_MEDIUM)
    endtask

    // Helper function to create read transaction
    protected task automatic read_test_register(bit [31:0] addr,
                                                 string label = "test_reg_read");
        uart_frame_transaction req;
        req = uart_frame_transaction::type_id::create(label);
        start_item(req);
        
        req.is_write = 0;
        req.auto_increment = 0;
        req.size = 2'b10; // 4 bytes
        req.length = 4'h0;
        req.addr = addr;
        req.sof = SOF_HOST_TO_DEVICE;
        req.direction = UART_RX;
        req.error_inject = 0;
        req.expect_error = 0;
        req.data = new[0];
        
        req.build_cmd();
        req.calculate_crc();
        
        finish_item(req);
        
        `uvm_info(get_type_name(), 
                  $sformatf("Read from test register 0x%08X", addr), 
                  UVM_MEDIUM)
    endtask

    // Add settling time between operations
    protected task automatic wait_cycles(int cycles = 10);
        repeat(cycles) @(posedge uart_axi4_tb_top.clk);
    endtask

endclass

// Comprehensive test register validation sequence
class test_register_comprehensive_sequence extends test_register_sequence_base;
    `uvm_object_utils(test_register_comprehensive_sequence)
    
    function new(string name = "test_register_comprehensive_sequence");
        super.new(name);
    endfunction

    virtual task body();
        `uvm_info(get_type_name(), "Starting test register comprehensive validation", UVM_LOW)
        
        // Test each register with different data patterns
        test_register_basic_rw();
        test_register_data_patterns();
        test_register_independence();
        test_register_reset_values();
        
        `uvm_info(get_type_name(), "Test register comprehensive validation completed", UVM_LOW)
    endtask

    // Basic read/write functionality for all test registers
    task test_register_basic_rw();
        bit [31:0] test_data[4] = '{32'hDEADBEEF, 32'h12345678, 32'hA5A5A5A5, 32'h5A5A5A5A};
        bit [31:0] reg_addrs[4] = '{REG_TEST_0, REG_TEST_1, REG_TEST_2, REG_TEST_3};
        
        `uvm_info(get_type_name(), "Testing basic read/write functionality", UVM_MEDIUM)
        
        // Write test data to each register
        for (int i = 0; i < 4; i++) begin
            write_test_register(reg_addrs[i], test_data[i], 
                               $sformatf("basic_write_reg_%0d", i));
            wait_cycles(20);
        end
        
        // Read back from each register
        for (int i = 0; i < 4; i++) begin
            read_test_register(reg_addrs[i], 
                              $sformatf("basic_read_reg_%0d", i));
            wait_cycles(20);
        end
    endtask

    // Test various data patterns
    task test_register_data_patterns();
        bit [31:0] patterns[8] = '{
            32'h00000000, 32'hFFFFFFFF, 32'hAAAAAAAA, 32'h55555555,
            32'h01234567, 32'h89ABCDEF, 32'hF0F0F0F0, 32'h0F0F0F0F
        };
        
        `uvm_info(get_type_name(), "Testing data patterns", UVM_MEDIUM)
        
        // Test patterns on REG_TEST_0
        for (int i = 0; i < 8; i++) begin
            write_test_register(REG_TEST_0, patterns[i], 
                               $sformatf("pattern_write_%0d", i));
            wait_cycles(15);
            read_test_register(REG_TEST_0, 
                              $sformatf("pattern_read_%0d", i));
            wait_cycles(15);
        end
    endtask

    // Test register independence
    task test_register_independence();
        `uvm_info(get_type_name(), "Testing register independence", UVM_MEDIUM)
        
        // Write unique values to all registers
        write_test_register(REG_TEST_0, 32'h11111111, "indep_write_0");
        wait_cycles(10);
        write_test_register(REG_TEST_1, 32'h22222222, "indep_write_1");
        wait_cycles(10);
        write_test_register(REG_TEST_2, 32'h33333333, "indep_write_2");
        wait_cycles(10);
        write_test_register(REG_TEST_3, 32'h44444444, "indep_write_3");
        wait_cycles(10);
        
        // Read all registers to verify independence
        read_test_register(REG_TEST_0, "indep_read_0");
        wait_cycles(10);
        read_test_register(REG_TEST_1, "indep_read_1");
        wait_cycles(10);
        read_test_register(REG_TEST_2, "indep_read_2");
        wait_cycles(10);
        read_test_register(REG_TEST_3, "indep_read_3");
        wait_cycles(10);
    endtask

    // Test reset values (should be initialized values from RTL)
    task test_register_reset_values();
        `uvm_info(get_type_name(), "Testing reset values", UVM_MEDIUM)
        
        // Note: Reset values are defined in Register_Block.sv as:
        // REG_TEST_0: 32'hTEST_0000 (0x54455354_00000000)
        // REG_TEST_1: 32'hTEST_1111 (0x54455354_11111111)
        // REG_TEST_2: 32'hTEST_2222 (0x54455354_22222222)
        // REG_TEST_3: 32'hTEST_3333 (0x54455354_33333333)
        
        read_test_register(REG_TEST_0, "reset_read_0");
        wait_cycles(10);
        read_test_register(REG_TEST_1, "reset_read_1");
        wait_cycles(10);
        read_test_register(REG_TEST_2, "reset_read_2");
        wait_cycles(10);
        read_test_register(REG_TEST_3, "reset_read_3");
        wait_cycles(10);
    endtask

endclass

// Quick test register validation sequence (for faster testing)
class test_register_quick_sequence extends test_register_sequence_base;
    `uvm_object_utils(test_register_quick_sequence)
    
    function new(string name = "test_register_quick_sequence");
        super.new(name);
    endfunction

    virtual task body();
        `uvm_info(get_type_name(), "Starting quick test register validation", UVM_LOW)
        
        // Quick test: Write and read one value per register
        write_test_register(REG_TEST_0, 32'hABCD1234, "quick_write_0");
        wait_cycles(10);
        read_test_register(REG_TEST_0, "quick_read_0");
        wait_cycles(10);
        
        write_test_register(REG_TEST_1, 32'h5678EFAB, "quick_write_1");
        wait_cycles(10);
        read_test_register(REG_TEST_1, "quick_read_1");
        wait_cycles(10);
        
        write_test_register(REG_TEST_2, 32'h9999AAAA, "quick_write_2");
        wait_cycles(10);
        read_test_register(REG_TEST_2, "quick_read_2");
        wait_cycles(10);
        
        write_test_register(REG_TEST_3, 32'hBBBBCCCC, "quick_write_3");
        wait_cycles(10);
        read_test_register(REG_TEST_3, "quick_read_3");
        wait_cycles(10);
        
        `uvm_info(get_type_name(), "Quick test register validation completed", UVM_LOW)
    endtask

endclass

// Walking bit pattern test sequence
class test_register_walking_bits_sequence extends test_register_sequence_base;
    `uvm_object_utils(test_register_walking_bits_sequence)
    
    function new(string name = "test_register_walking_bits_sequence");
        super.new(name);
    endfunction

    virtual task body();
        bit [31:0] walking_pattern;
        
        `uvm_info(get_type_name(), "Starting walking bits test", UVM_LOW)
        
        // Test walking 1s pattern on REG_TEST_0
        for (int i = 0; i < 32; i++) begin
            walking_pattern = 1 << i;
            write_test_register(REG_TEST_0, walking_pattern, 
                               $sformatf("walk1_write_%0d", i));
            wait_cycles(5);
            read_test_register(REG_TEST_0, 
                              $sformatf("walk1_read_%0d", i));
            wait_cycles(5);
        end
        
        // Test walking 0s pattern on REG_TEST_1
        for (int i = 0; i < 32; i++) begin
            walking_pattern = ~(1 << i);
            write_test_register(REG_TEST_1, walking_pattern, 
                               $sformatf("walk0_write_%0d", i));
            wait_cycles(5);
            read_test_register(REG_TEST_1, 
                              $sformatf("walk0_read_%0d", i));
            wait_cycles(5);
        end
        
        `uvm_info(get_type_name(), "Walking bits test completed", UVM_LOW)
    endtask

endclass

// Stress test sequence (rapid read/write operations)
class test_register_stress_sequence extends test_register_sequence_base;
    `uvm_object_utils(test_register_stress_sequence)
    
    function new(string name = "test_register_stress_sequence");
        super.new(name);
    endfunction

    virtual task body();
        bit [31:0] random_data;
        bit [31:0] reg_addrs[4] = '{REG_TEST_0, REG_TEST_1, REG_TEST_2, REG_TEST_3};
        
        `uvm_info(get_type_name(), "Starting stress test", UVM_LOW)
        
        // Rapid write/read cycles
        for (int cycle = 0; cycle < 50; cycle++) begin
            for (int reg_idx = 0; reg_idx < 4; reg_idx++) begin
                random_data = $urandom();
                write_test_register(reg_addrs[reg_idx], random_data, 
                                   $sformatf("stress_write_c%0d_r%0d", cycle, reg_idx));
                wait_cycles(2);
                read_test_register(reg_addrs[reg_idx], 
                                  $sformatf("stress_read_c%0d_r%0d", cycle, reg_idx));
                wait_cycles(2);
            end
        end
        
        `uvm_info(get_type_name(), "Stress test completed", UVM_LOW)
    endtask

endclass