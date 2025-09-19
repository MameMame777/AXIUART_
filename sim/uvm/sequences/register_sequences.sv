`timescale 1ns / 1ps

`include "uvm_macros.svh"
import uvm_pkg::*;
import uart_axi4_test_pkg::*;

// Register address definitions
localparam bit [31:0] REG_BASE_ADDR = 32'h0000_1000;
localparam bit [31:0] REG_CONTROL   = REG_BASE_ADDR + 32'h000;
localparam bit [31:0] REG_STATUS    = REG_BASE_ADDR + 32'h004;
localparam bit [31:0] REG_CONFIG    = REG_BASE_ADDR + 32'h008;
localparam bit [31:0] REG_DEBUG     = REG_BASE_ADDR + 32'h00C;
localparam bit [31:0] REG_TX_COUNT  = REG_BASE_ADDR + 32'h010;
localparam bit [31:0] REG_RX_COUNT  = REG_BASE_ADDR + 32'h014;
localparam bit [31:0] REG_FIFO_STAT = REG_BASE_ADDR + 32'h018;
localparam bit [31:0] REG_VERSION   = REG_BASE_ADDR + 32'h01C;

// Basic register read/write sequence
class register_basic_rw_sequence extends uvm_sequence #(axi4_lite_transaction);
    `uvm_object_utils(register_basic_rw_sequence)

    function new(string name = "register_basic_rw_sequence");
        super.new(name);
    endfunction

    rand bit [31:0] test_addr;
    rand bit [31:0] test_data;

    constraint c_addr_valid { 
        test_addr inside {REG_CONTROL, REG_CONFIG, REG_DEBUG}; 
    }
    
    constraint c_data_valid {
        test_data[31:16] == 16'h0000; // Upper bits should be 0 for most registers
    }

    virtual task body();
        axi4_lite_transaction write_trans, read_trans;
        bit [31:0] read_data;
        
        `uvm_info("REG_SEQ", $sformatf("Starting register R/W test at addr=0x%08X, data=0x%08X", test_addr, test_data), UVM_MEDIUM)
        
        // Write to register
        `uvm_do_with(write_trans, {
            write_trans.addr == test_addr;
            write_trans.data == test_data;
            write_trans.trans_type == AXI4_LITE_WRITE;
            write_trans.strb == 4'hF;
        })
        
        // Read back from register
        `uvm_do_with(read_trans, {
            read_trans.addr == test_addr;
            read_trans.trans_type == AXI4_LITE_READ;
        })
        
        read_data = read_trans.data;
        
        // Check write/read consistency for writable registers
        case (test_addr)
            REG_CONTROL: begin
                // Only bit 0 is writable, bit 1 is W1C (always reads 0)
                if (read_data[0] !== test_data[0] || read_data[31:1] !== 31'b0) begin
                    `uvm_error("REG_SEQ", $sformatf("CONTROL register mismatch: W=0x%08X, R=0x%08X", test_data, read_data))
                end else begin
                    `uvm_info("REG_SEQ", $sformatf("CONTROL register OK: R=0x%08X", read_data), UVM_MEDIUM)
                end
            end
            
            REG_CONFIG: begin
                // Bits 15:0 are writable
                bit [15:0] expected_config = test_data[15:0];
                if (read_data[15:0] !== expected_config || read_data[31:16] !== 16'b0) begin
                    `uvm_error("REG_SEQ", $sformatf("CONFIG register mismatch: W=0x%08X, R=0x%08X", test_data, read_data))
                end else begin
                    `uvm_info("REG_SEQ", $sformatf("CONFIG register OK: R=0x%08X", read_data), UVM_MEDIUM)
                end
            end
            
            REG_DEBUG: begin
                // Bits 3:0 are writable
                bit [3:0] expected_debug = test_data[3:0];
                if (read_data[3:0] !== expected_debug || read_data[31:4] !== 28'b0) begin
                    `uvm_error("REG_SEQ", $sformatf("DEBUG register mismatch: W=0x%08X, R=0x%08X", test_data, read_data))
                end else begin
                    `uvm_info("REG_SEQ", $sformatf("DEBUG register OK: R=0x%08X", read_data), UVM_MEDIUM)
                end
            end
            
            default: begin
                `uvm_warning("REG_SEQ", $sformatf("Unexpected register address: 0x%08X", test_addr))
            end
        endcase
    endtask
endclass

// Register reset test sequence
class register_reset_sequence extends uvm_sequence #(axi4_lite_transaction);
    `uvm_object_utils(register_reset_sequence)

    function new(string name = "register_reset_sequence");
        super.new(name);
    endfunction

    virtual task body();
        axi4_lite_transaction read_trans;
        
        `uvm_info("REG_SEQ", "Starting register reset value test", UVM_MEDIUM)
        
        // Check reset values of all registers
        check_register_reset_value(REG_CONTROL, 32'h0000_0000, "CONTROL");
        check_register_reset_value(REG_STATUS, 32'h0000_0000, "STATUS");
        check_register_reset_value(REG_CONFIG, 32'h0000_0000, "CONFIG");
        check_register_reset_value(REG_DEBUG, 32'h0000_0000, "DEBUG");
        check_register_reset_value(REG_TX_COUNT, 32'h0000_0000, "TX_COUNT");
        check_register_reset_value(REG_RX_COUNT, 32'h0000_0000, "RX_COUNT");
        check_register_reset_value(REG_FIFO_STAT, 32'h0000_0000, "FIFO_STAT");
        check_register_reset_value(REG_VERSION, 32'h0001_0000, "VERSION");
    endtask
    
    task check_register_reset_value(bit [31:0] addr, bit [31:0] expected, string name);
        axi4_lite_transaction read_trans;
        
        `uvm_do_with(read_trans, {
            read_trans.addr == addr;
            read_trans.trans_type == AXI4_LITE_READ;
        })
        
        if (read_trans.data !== expected) begin
            `uvm_error("REG_SEQ", $sformatf("%s reset value mismatch: Expected=0x%08X, Actual=0x%08X", 
                       name, expected, read_trans.data))
        end else begin
            `uvm_info("REG_SEQ", $sformatf("%s reset value OK: 0x%08X", name, read_trans.data), UVM_MEDIUM)
        end
    endtask
endclass

// Register access protection test sequence
class register_access_test_sequence extends uvm_sequence #(axi4_lite_transaction);
    `uvm_object_utils(register_access_test_sequence)

    function new(string name = "register_access_test_sequence");
        super.new(name);
    endfunction

    virtual task body();
        `uvm_info("REG_SEQ", "Starting register access protection test", UVM_MEDIUM)
        
        // Test read-only registers (writes should be ignored)
        test_read_only_register(REG_STATUS, "STATUS");
        test_read_only_register(REG_TX_COUNT, "TX_COUNT");
        test_read_only_register(REG_RX_COUNT, "RX_COUNT");
        test_read_only_register(REG_FIFO_STAT, "FIFO_STAT");
        test_read_only_register(REG_VERSION, "VERSION");
        
        // Test invalid addresses (should return SLVERR)
        test_invalid_address(REG_BASE_ADDR + 32'h020);
        test_invalid_address(REG_BASE_ADDR + 32'hFFC);
        test_invalid_address(REG_BASE_ADDR + 32'h1000);
        
        // Test unaligned addresses (should return SLVERR)
        test_unaligned_address(REG_CONTROL + 1);
        test_unaligned_address(REG_CONFIG + 2);
        test_unaligned_address(REG_DEBUG + 3);
    endtask
    
    task test_read_only_register(bit [31:0] addr, string name);
        axi4_lite_transaction write_trans, read_trans;
        bit [31:0] original_value, test_value, final_value;
        
        // Read original value
        `uvm_do_with(read_trans, {
            read_trans.addr == addr;
            read_trans.trans_type == AXI4_LITE_READ;
        })
        original_value = read_trans.data;
        
        // Try to write different value
        test_value = ~original_value;
        `uvm_do_with(write_trans, {
            write_trans.addr == addr;
            write_trans.data == test_value;
            write_trans.trans_type == AXI4_LITE_WRITE;
            write_trans.strb == 4'hF;
        })
        
        // Read final value
        `uvm_do_with(read_trans, {
            read_trans.addr == addr;
            read_trans.trans_type == AXI4_LITE_READ;
        })
        final_value = read_trans.data;
        
        if (final_value !== original_value) begin
            `uvm_error("REG_SEQ", $sformatf("%s register is not read-only: Original=0x%08X, Final=0x%08X", 
                       name, original_value, final_value))
        end else begin
            `uvm_info("REG_SEQ", $sformatf("%s register correctly read-only", name), UVM_MEDIUM)
        end
    endtask
    
    task test_invalid_address(bit [31:0] addr);
        axi4_lite_transaction read_trans, write_trans;
        
        // Test invalid read
        `uvm_do_with(read_trans, {
            read_trans.addr == addr;
            read_trans.trans_type == AXI4_LITE_READ;
        })
        
        if (read_trans.resp !== 2'b10) begin // SLVERR expected
            `uvm_error("REG_SEQ", $sformatf("Invalid read address 0x%08X should return SLVERR, got 0x%02X", 
                       addr, read_trans.resp))
        end else begin
            `uvm_info("REG_SEQ", $sformatf("Invalid read address 0x%08X correctly returned SLVERR", addr), UVM_MEDIUM)
        end
        
        // Test invalid write
        `uvm_do_with(write_trans, {
            write_trans.addr == addr;
            write_trans.data == 32'hDEADBEEF;
            write_trans.trans_type == AXI4_LITE_WRITE;
            write_trans.strb == 4'hF;
        })
        
        if (write_trans.resp !== 2'b10) begin // SLVERR expected
            `uvm_error("REG_SEQ", $sformatf("Invalid write address 0x%08X should return SLVERR, got 0x%02X", 
                       addr, write_trans.resp))
        end else begin
            `uvm_info("REG_SEQ", $sformatf("Invalid write address 0x%08X correctly returned SLVERR", addr), UVM_MEDIUM)
        end
    endtask
    
    task test_unaligned_address(bit [31:0] addr);
        axi4_lite_transaction read_trans;
        
        `uvm_do_with(read_trans, {
            read_trans.addr == addr;
            read_trans.trans_type == AXI4_LITE_READ;
        })
        
        if (read_trans.resp !== 2'b10) begin // SLVERR expected
            `uvm_error("REG_SEQ", $sformatf("Unaligned address 0x%08X should return SLVERR, got 0x%02X", 
                       addr, read_trans.resp))
        end else begin
            `uvm_info("REG_SEQ", $sformatf("Unaligned address 0x%08X correctly returned SLVERR", addr), UVM_MEDIUM)
        end
    endtask
endclass