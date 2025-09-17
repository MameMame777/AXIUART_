/*
 * UART-AXI4 Bridge RTL Verification Test Sequences
 * Purpose: Real RTL register access and data transfer sequences
 * Guidelines: Must use actual RTL DUT - no simulation mockups
 */

`timescale 1ns / 1ps

`include "uvm_macros.svh"
import uvm_pkg::*;
import axi4_lite_pkg::*;

`include "axi4_lite_transaction.sv"

`ifndef UART_AXI_SEQUENCES_SV
`define UART_AXI_SEQUENCES_SV

// Base sequence class
class uart_axi_sequence extends uvm_sequence #(axi4_lite_transaction);
    `uvm_object_utils(uart_axi_sequence)
    
    function new(string name = "uart_axi_sequence");
        super.new(name);
    endfunction
endclass

// Basic register access sequence - Tests actual RTL registers
class uart_axi_basic_sequence extends uart_axi_sequence;
    `uvm_object_utils(uart_axi_basic_sequence)
    
    function new(string name = "uart_axi_basic_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        axi4_lite_transaction txn;
        
        `uvm_info(get_type_name(), "Starting RTL register access test", UVM_LOW)
        
        // Test 1: Read control register (Address 0x00)
        txn = axi4_lite_transaction::type_id::create("read_control");
        start_item(txn);
        txn.addr = 32'h00;
        txn.trans_type = READ;
        finish_item(txn);
        `uvm_info(get_type_name(), $sformatf("Control register read: 0x%08x", txn.data), UVM_LOW)
        
        // Test 2: Read status register (Address 0x04) 
        txn = axi4_lite_transaction::type_id::create("read_status");
        start_item(txn);
        txn.addr = 32'h04;
        txn.trans_type = READ;
        finish_item(txn);
        `uvm_info(get_type_name(), $sformatf("Status register read: 0x%08x", txn.data), UVM_LOW)
        
        // Test 3: Enable UART (Write to control register)
        txn = axi4_lite_transaction::type_id::create("enable_uart");
        start_item(txn);
        txn.addr = 32'h00;
        txn.trans_type = WRITE;
        txn.data = 32'h00000007; // Enable UART, TX, RX
        finish_item(txn);
        `uvm_info(get_type_name(), "UART enabled via control register", UVM_LOW)
        
        // Test 4: Verify UART enable (Read back control register)
        txn = axi4_lite_transaction::type_id::create("verify_enable");
        start_item(txn);
        txn.addr = 32'h00;
        txn.trans_type = READ;
        finish_item(txn);
        `uvm_info(get_type_name(), $sformatf("Control register verification: 0x%08x", txn.data), UVM_LOW)
        
        `uvm_info(get_type_name(), "RTL register access test completed", UVM_LOW)
    endtask
endclass

// TX data sequence - Tests actual RTL TX path
class uart_axi_tx_sequence extends uart_axi_sequence;
    `uvm_object_utils(uart_axi_tx_sequence)
    
    function new(string name = "uart_axi_tx_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        axi4_lite_transaction txn;
        
        `uvm_info(get_type_name(), "Starting RTL TX data test", UVM_LOW)
        
        // Enable UART first
        txn = axi4_lite_transaction::type_id::create("enable_uart_tx");
        start_item(txn);
        txn.addr = 32'h00;
        txn.trans_type = WRITE;
        txn.data = 32'h00000007; // Enable UART, TX, RX
        finish_item(txn);
        
        // Write test data to TX register (Address 0x08)
        for (int i = 0; i < 5; i++) begin
            txn = axi4_lite_transaction::type_id::create($sformatf("tx_data_%0d", i));
            start_item(txn);
            txn.addr = 32'h08;
            txn.trans_type = WRITE;
            txn.data = 32'h41 + i; // ASCII 'A', 'B', 'C', etc.
            finish_item(txn);
            `uvm_info(get_type_name(), $sformatf("TX data written: 0x%02x", txn.data[7:0]), UVM_LOW)
            
            // Small delay between transmissions
            #1000ns;
        end
        
        `uvm_info(get_type_name(), "RTL TX data test completed", UVM_LOW)
    endtask
endclass

// RX data sequence - Tests actual RTL RX path
class uart_axi_rx_sequence extends uart_axi_sequence;
    `uvm_object_utils(uart_axi_rx_sequence)
    
    function new(string name = "uart_axi_rx_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        axi4_lite_transaction txn;
        
        `uvm_info(get_type_name(), "Starting RTL RX data test", UVM_LOW)
        
        // Enable UART for RX
        txn = axi4_lite_transaction::type_id::create("enable_uart_rx");
        start_item(txn);
        txn.addr = 32'h00;
        txn.trans_type = WRITE;
        txn.data = 32'h00000007; // Enable UART, TX, RX
        finish_item(txn);
        
        // Poll for RX data (Address 0x0C)
        for (int i = 0; i < 10; i++) begin
            txn = axi4_lite_transaction::type_id::create($sformatf("poll_rx_%0d", i));
            start_item(txn);
            txn.addr = 32'h0C;
            txn.trans_type = READ;
            finish_item(txn);
            
            if (txn.data != 0) begin
                `uvm_info(get_type_name(), $sformatf("RX data received: 0x%02x", txn.data[7:0]), UVM_LOW)
            end
            
            #2000ns; // Polling interval
        end
        
        `uvm_info(get_type_name(), "RTL RX data test completed", UVM_LOW)
    endtask
endclass

// Error handling sequence - Tests actual RTL error conditions
class uart_axi_error_sequence extends uart_axi_sequence;
    `uvm_object_utils(uart_axi_error_sequence)
    
    function new(string name = "uart_axi_error_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        axi4_lite_transaction txn;
        
        `uvm_info(get_type_name(), "Starting RTL error condition test", UVM_LOW)
        
        // Test invalid address access
        txn = axi4_lite_transaction::type_id::create("invalid_addr");
        start_item(txn);
        txn.addr = 32'hFF; // Invalid address
        txn.trans_type = READ;
        finish_item(txn);
        `uvm_info(get_type_name(), $sformatf("Invalid address response: 0x%08x", txn.resp), UVM_LOW)
        
        // Read error status register (Address 0x10)
        txn = axi4_lite_transaction::type_id::create("read_error_status");
        start_item(txn);
        txn.addr = 32'h10;
        txn.trans_type = READ;
        finish_item(txn);
        `uvm_info(get_type_name(), $sformatf("Error status: 0x%08x", txn.data), UVM_LOW)
        
        `uvm_info(get_type_name(), "RTL error condition test completed", UVM_LOW)
    endtask
endclass

// Comprehensive sequence - Full RTL verification test
class uart_axi_comprehensive_sequence extends uart_axi_sequence;
    `uvm_object_utils(uart_axi_comprehensive_sequence)
    
    function new(string name = "uart_axi_comprehensive_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_axi_basic_sequence basic_seq;
        uart_axi_tx_sequence tx_seq;
        uart_axi_rx_sequence rx_seq;
        uart_axi_error_sequence error_seq;
        
        `uvm_info(get_type_name(), "Starting comprehensive RTL verification", UVM_LOW)
        
        // Execute all test sequences
        basic_seq = uart_axi_basic_sequence::type_id::create("basic_seq");
        basic_seq.start(m_sequencer);
        
        tx_seq = uart_axi_tx_sequence::type_id::create("tx_seq");
        tx_seq.start(m_sequencer);
        
        rx_seq = uart_axi_rx_sequence::type_id::create("rx_seq");
        rx_seq.start(m_sequencer);
        
        error_seq = uart_axi_error_sequence::type_id::create("error_seq");
        error_seq.start(m_sequencer);
        
        `uvm_info(get_type_name(), "Comprehensive RTL verification completed", UVM_LOW)
    endtask
endclass

`endif // UART_AXI_SEQUENCES_SV
