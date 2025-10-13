`timescale 1ns / 1ps

// UART Transaction Class for Phase 4
// Created: October 13, 2025
// Purpose: Basic UART transaction for protocol testing

`ifndef UART_TRANSACTION_SV
`define UART_TRANSACTION_SV

// Import UVM package
import uvm_pkg::*;
`include "uvm_macros.svh"

// Transaction type enumeration
typedef enum bit { READ = 1'b1, WRITE = 1'b0 } transaction_type_e;

// Protocol operation types for testing
typedef enum {
    BASIC_OPERATION,
    BURST_WRITE,
    PROTOCOL_VERIFY,
    PROTOCOL_VIOLATION,
    TIMEOUT_TEST,
    ERROR_RECOVERY
} protocol_operation_e;

class uart_transaction extends uvm_sequence_item;
    
    // Transaction fields
    rand bit [31:0] address;
    rand bit [31:0] data;
    rand transaction_type_e transaction_type;
    rand bit [7:0] frame_data[];
    rand int frame_length;
    
    // Protocol control fields
    bit enable_bridge_awareness = 1'b1;
    bit enable_protocol_checking = 1'b1;
    bit enable_crc_checking = 1'b1;
    bit enable_error_injection = 1'b0;
    bit enable_recovery_testing = 1'b0;
    bit enable_timing_checks = 1'b1;
    
    // Burst and alignment fields
    rand int burst_length = 1;
    bit expect_alignment_error = 1'b0;
    bit expect_address_error = 1'b0;
    bit expect_protocol_error = 1'b0;
    bit expect_timeout_error = 1'b0;
    
    // Status fields
    bit transaction_completed = 1'b0;
    bit has_error = 1'b0;
    string error_message = "";
    
    // UVM registration
    `uvm_object_utils_begin(uart_transaction)
        `uvm_field_int(address, UVM_ALL_ON)
        `uvm_field_int(data, UVM_ALL_ON)
        `uvm_field_enum(transaction_type_e, transaction_type, UVM_ALL_ON)
        `uvm_field_array_int(frame_data, UVM_ALL_ON)
        `uvm_field_int(frame_length, UVM_ALL_ON)
        `uvm_field_int(enable_bridge_awareness, UVM_ALL_ON)
        `uvm_field_int(enable_protocol_checking, UVM_ALL_ON)
        `uvm_field_int(enable_crc_checking, UVM_ALL_ON)
        `uvm_field_int(enable_error_injection, UVM_ALL_ON)
        `uvm_field_int(enable_recovery_testing, UVM_ALL_ON)
        `uvm_field_int(enable_timing_checks, UVM_ALL_ON)
        `uvm_field_int(burst_length, UVM_ALL_ON)
        `uvm_field_int(expect_alignment_error, UVM_ALL_ON)
        `uvm_field_int(expect_address_error, UVM_ALL_ON)
        `uvm_field_int(expect_protocol_error, UVM_ALL_ON)
        `uvm_field_int(expect_timeout_error, UVM_ALL_ON)
        `uvm_field_int(transaction_completed, UVM_ALL_ON)
        `uvm_field_int(has_error, UVM_ALL_ON)
        `uvm_field_string(error_message, UVM_ALL_ON)
    `uvm_object_utils_end
    
    // Constructor
    function new(string name = "uart_transaction");
        super.new(name);
        frame_length = 8; // Default frame size
    endfunction
    
    // Constraints
    constraint valid_address_c {
        address inside {[32'h00000000:32'h0000FFFF]}; // Valid register range
    }
    
    constraint valid_frame_length_c {
        frame_length inside {[4:16]}; // Valid frame sizes
        frame_data.size() == frame_length;
    }
    
    constraint protocol_frame_c {
        if (transaction_type == WRITE) {
            frame_length >= 8; // Minimum write frame size
        }
        if (transaction_type == READ) {
            frame_length >= 4; // Minimum read frame size
        }
    }
    
    // Utility functions
    virtual function string convert2string();
        string s;
        s = $sformatf("UART Transaction:\n");
        s = {s, $sformatf("  Type: %s\n", transaction_type.name())};
        s = {s, $sformatf("  Address: 0x%08x\n", address)};
        s = {s, $sformatf("  Data: 0x%08x\n", data)};
        s = {s, $sformatf("  Frame Length: %0d\n", frame_length)};
        s = {s, $sformatf("  Bridge Aware: %0b\n", enable_bridge_awareness)};
        s = {s, $sformatf("  Completed: %0b\n", transaction_completed)};
        if (has_error) begin
            s = {s, $sformatf("  Error: %s\n", error_message)};
        end
        return s;
    endfunction
    
    virtual function void do_copy(uvm_object rhs);
        uart_transaction rhs_;
        if (!$cast(rhs_, rhs)) begin
            `uvm_fatal(get_type_name(), "Failed to cast rhs to uart_transaction")
        end
        super.do_copy(rhs);
        this.address = rhs_.address;
        this.data = rhs_.data;
        this.transaction_type = rhs_.transaction_type;
        this.frame_data = rhs_.frame_data;
        this.frame_length = rhs_.frame_length;
        this.enable_bridge_awareness = rhs_.enable_bridge_awareness;
        this.enable_protocol_checking = rhs_.enable_protocol_checking;
        this.enable_crc_checking = rhs_.enable_crc_checking;
    endfunction
    
    virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        uart_transaction rhs_;
        if (!$cast(rhs_, rhs)) begin
            return 0;
        end
        return (super.do_compare(rhs, comparer) &&
                (this.address == rhs_.address) &&
                (this.data == rhs_.data) &&
                (this.transaction_type == rhs_.transaction_type) &&
                (this.frame_length == rhs_.frame_length));
    endfunction
    
endclass : uart_transaction

`endif // UART_TRANSACTION_SV