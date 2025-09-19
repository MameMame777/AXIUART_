`timescale 1ns / 1ps

// Test Package containing all sequences and tests
package sequence_lib_pkg;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // Define uart_frame_transaction locally to avoid circular dependency
    class uart_frame_transaction extends uvm_sequence_item;
        // Basic frame fields
        rand bit [7:0] sof;
        rand bit [7:0] cmd;
        rand bit [31:0] addr;
        rand bit [7:0] len;
        rand bit [7:0] data[];
        rand bit [7:0] crc;
        
        // Error injection fields based on the error messages
        rand bit force_crc_error;
        rand bit force_timeout;
        rand bit corrupt_frame_format;
        rand bit truncate_frame;
        rand bit wrong_sof;
        
        `uvm_object_utils_begin(uart_frame_transaction)
            `uvm_field_int(sof, UVM_DEFAULT)
            `uvm_field_int(cmd, UVM_DEFAULT)
            `uvm_field_int(addr, UVM_DEFAULT)
            `uvm_field_int(len, UVM_DEFAULT)
            `uvm_field_array_int(data, UVM_DEFAULT)
            `uvm_field_int(crc, UVM_DEFAULT)
            `uvm_field_int(force_crc_error, UVM_DEFAULT)
            `uvm_field_int(force_timeout, UVM_DEFAULT)
            `uvm_field_int(corrupt_frame_format, UVM_DEFAULT)
            `uvm_field_int(truncate_frame, UVM_DEFAULT)
            `uvm_field_int(wrong_sof, UVM_DEFAULT)
        `uvm_object_utils_end
        
        function new(string name = "uart_frame_transaction");
            super.new(name);
        endfunction
    endclass
    
    // Define basic env config to avoid circular dependency  
    class uart_axi4_env_config extends uvm_object;
        `uvm_object_utils(uart_axi4_env_config)
        
        function new(string name = "uart_axi4_env_config");
            super.new(name);
        endfunction
    endclass
    
    // Include sequence files
    
    // Include sequence files
    `include "sequences/basic_func_sequence.sv"
    `include "sequences/error_injection_sequence.sv" 
    `include "sequences/performance_test_sequence.sv"
    
endpackage