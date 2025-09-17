/*
 * UVM Compliant UART Protocol Testing Environment - Phase 2
 * Purpose: Best practices compliant UART communication protocol verification
 * Features: Full UVM hierarchy with Driver/Monitor/Agent/Scoreboard
 * Guidelines: Follows UVM-1.2 methodology and best practices
 */

`timescale 1ns / 1ps

`include "uvm_macros.svh"
import uvm_pkg::*;
import axi4_lite_pkg::*;

// Transaction item for UART Protocol testing
class uart_protocol_transaction extends uvm_sequence_item;
    
    // Transaction fields
    rand logic [7:0]  data;
    rand logic [7:0]  address;
    rand bit          write;
    rand logic [31:0] axi_data;
    logic [31:0]      response_data;
    bit               error;
    
    // UVM field automation macros
    `uvm_object_utils_begin(uart_protocol_transaction)
        `uvm_field_int(data, UVM_ALL_ON)
        `uvm_field_int(address, UVM_ALL_ON)
        `uvm_field_int(write, UVM_ALL_ON)
        `uvm_field_int(axi_data, UVM_ALL_ON)
        `uvm_field_int(response_data, UVM_ALL_ON)
        `uvm_field_int(error, UVM_ALL_ON)
    `uvm_object_utils_end
    
    // Constructor
    function new(string name = "uart_protocol_transaction");
        super.new(name);
    endfunction
    
    // Constraints
    constraint valid_address_c {
        address inside {8'h00, 8'h04, 8'h08, 8'h0C, 8'h10, 8'h14, 8'h18, 8'h1C};
    }
    
    constraint valid_data_c {
        data inside {[8'h00:8'hFF]};
    }
    
endclass

// Base sequence class
class uart_protocol_base_sequence extends uvm_sequence #(uart_protocol_transaction);
    `uvm_object_utils(uart_protocol_base_sequence)
    
    function new(string name = "uart_protocol_base_sequence");
        super.new(name);
    endfunction
    
endclass

// Basic test sequence
class uart_basic_test_sequence extends uart_protocol_base_sequence;
    `uvm_object_utils(uart_basic_test_sequence)
    
    function new(string name = "uart_basic_test_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_protocol_transaction tx;
        
        `uvm_info(get_type_name(), "Starting basic UART protocol test sequence", UVM_MEDIUM)
        
        repeat(10) begin
            tx = uart_protocol_transaction::type_id::create("tx");
            start_item(tx);
            assert(tx.randomize());
            finish_item(tx);
            `uvm_info(get_type_name(), $sformatf("Sent transaction: addr=0x%02X, data=0x%02X, write=%0d", 
                     tx.address, tx.data, tx.write), UVM_HIGH)
        end
        
        `uvm_info(get_type_name(), "Basic UART protocol test sequence completed", UVM_MEDIUM)
    endtask
    
endclass

// UART Protocol Driver
class uart_protocol_driver extends uvm_driver #(uart_protocol_transaction);
    `uvm_component_utils(uart_protocol_driver)
    
    // Virtual interfaces
    virtual axi4_lite_if axi_vif;
    virtual uart_if uart_vif;
    
    // Constructor
    function new(string name = "uart_protocol_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if (!uvm_config_db#(virtual axi4_lite_if)::get(this, "", "axi_vif", axi_vif)) begin
            `uvm_fatal("DRIVER", "Cannot get axi_vif from config_db")
        end
        
        if (!uvm_config_db#(virtual uart_if)::get(this, "", "uart_vif", uart_vif)) begin
            `uvm_fatal("DRIVER", "Cannot get uart_vif from config_db")
        end
    endfunction
    
    // Run phase
    virtual task run_phase(uvm_phase phase);
        uart_protocol_transaction tx;
        
        forever begin
            seq_item_port.get_next_item(tx);
            drive_transaction(tx);
            seq_item_port.item_done();
        end
    endtask
    
    // Drive transaction
    virtual task drive_transaction(uart_protocol_transaction tx);
        `uvm_info(get_type_name(), $sformatf("Driving transaction: addr=0x%02X, data=0x%02X, write=%0d", 
                 tx.address, tx.data, tx.write), UVM_HIGH)
        
        if (tx.write) begin
            axi_write(tx.address, tx.axi_data);
        end else begin
            axi_read(tx.address, tx.response_data);
        end
        
        // Small delay between transactions
        repeat(5) @(posedge axi_vif.aclk);
    endtask
    
    // AXI write task
    virtual task axi_write(logic [7:0] addr, logic [31:0] data);
        @(posedge axi_vif.aclk);
        
        // Write address phase
        axi_vif.awaddr  <= addr;
        axi_vif.awprot  <= 3'b000;
        axi_vif.awvalid <= 1'b1;
        
        // Write data phase
        axi_vif.wdata  <= data;
        axi_vif.wstrb  <= 4'hF;
        axi_vif.wvalid <= 1'b1;
        axi_vif.bready <= 1'b1;
        
        // Wait for ready signals
        while (!axi_vif.awready) @(posedge axi_vif.aclk);
        while (!axi_vif.wready)  @(posedge axi_vif.aclk);
        
        @(posedge axi_vif.aclk);
        axi_vif.awvalid <= 1'b0;
        axi_vif.wvalid  <= 1'b0;
        
        // Wait for write response
        while (!axi_vif.bvalid) @(posedge axi_vif.aclk);
        
        @(posedge axi_vif.aclk);
        axi_vif.bready <= 1'b0;
    endtask
    
    // AXI read task
    virtual task axi_read(logic [7:0] addr, output logic [31:0] data);
        @(posedge axi_vif.aclk);
        
        // Read address phase
        axi_vif.araddr  <= addr;
        axi_vif.arprot  <= 3'b000;
        axi_vif.arvalid <= 1'b1;
        axi_vif.rready  <= 1'b1;
        
        // Wait for address ready
        while (!axi_vif.arready) @(posedge axi_vif.aclk);
        
        @(posedge axi_vif.aclk);
        axi_vif.arvalid <= 1'b0;
        
        // Wait for read data
        while (!axi_vif.rvalid) @(posedge axi_vif.aclk);
        
        data = axi_vif.rdata;
        
        @(posedge axi_vif.aclk);
        axi_vif.rready <= 1'b0;
    endtask
    
endclass

// UART Protocol Monitor
class uart_protocol_monitor extends uvm_monitor;
    `uvm_component_utils(uart_protocol_monitor)
    
    // Analysis port
    uvm_analysis_port #(uart_protocol_transaction) ap;
    
    // Virtual interfaces
    virtual axi4_lite_if axi_vif;
    virtual uart_if uart_vif;
    
    // Constructor
    function new(string name = "uart_protocol_monitor", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        ap = new("ap", this);
        
        if (!uvm_config_db#(virtual axi4_lite_if)::get(this, "", "axi_vif", axi_vif)) begin
            `uvm_fatal("MONITOR", "Cannot get axi_vif from config_db")
        end
        
        if (!uvm_config_db#(virtual uart_if)::get(this, "", "uart_vif", uart_vif)) begin
            `uvm_fatal("MONITOR", "Cannot get uart_vif from config_db")
        end
    endfunction
    
    // Run phase
    virtual task run_phase(uvm_phase phase);
        uart_protocol_transaction tx;
        
        forever begin
            tx = uart_protocol_transaction::type_id::create("monitored_tx");
            monitor_transaction(tx);
            ap.write(tx);
        end
    endtask
    
    // Monitor transaction
    virtual task monitor_transaction(uart_protocol_transaction tx);
        // Monitor AXI transactions
        @(posedge axi_vif.aclk);
        
        if (axi_vif.awvalid && axi_vif.awready) begin
            // Write transaction detected
            tx.write = 1;
            tx.address = axi_vif.awaddr;
            wait(axi_vif.wvalid && axi_vif.wready);
            tx.axi_data = axi_vif.wdata;
            
            `uvm_info(get_type_name(), $sformatf("Monitored write: addr=0x%02X, data=0x%08X", 
                     tx.address, tx.axi_data), UVM_HIGH)
        end else if (axi_vif.arvalid && axi_vif.arready) begin
            // Read transaction detected
            tx.write = 0;
            tx.address = axi_vif.araddr;
            wait(axi_vif.rvalid && axi_vif.rready);
            tx.response_data = axi_vif.rdata;
            
            `uvm_info(get_type_name(), $sformatf("Monitored read: addr=0x%02X, data=0x%08X", 
                     tx.address, tx.response_data), UVM_HIGH)
        end else begin
            // No transaction, wait for next clock
            repeat(10) @(posedge axi_vif.aclk);
            return; // Skip this iteration
        end
    endtask
    
endclass

// UART Protocol Scoreboard
class uart_protocol_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(uart_protocol_scoreboard)
    
    // Analysis export
    uvm_analysis_export #(uart_protocol_transaction) sb_export;
    uvm_tlm_analysis_fifo #(uart_protocol_transaction) sb_fifo;
    
    // Statistics
    int transactions_received;
    int write_transactions;
    int read_transactions;
    int errors;
    
    // Constructor
    function new(string name = "uart_protocol_scoreboard", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        sb_export = new("sb_export", this);
        sb_fifo = new("sb_fifo", this);
    endfunction
    
    // Connect phase
    virtual function void connect_phase(uvm_phase phase);
        sb_export.connect(sb_fifo.analysis_export);
    endfunction
    
    // Run phase
    virtual task run_phase(uvm_phase phase);
        uart_protocol_transaction tx;
        
        forever begin
            sb_fifo.get(tx);
            check_transaction(tx);
        end
    endtask
    
    // Check transaction
    virtual function void check_transaction(uart_protocol_transaction tx);
        transactions_received++;
        
        if (tx.write) begin
            write_transactions++;
            `uvm_info(get_type_name(), $sformatf("Write transaction checked: addr=0x%02X, data=0x%08X", 
                     tx.address, tx.axi_data), UVM_HIGH)
        end else begin
            read_transactions++;
            `uvm_info(get_type_name(), $sformatf("Read transaction checked: addr=0x%02X, data=0x%08X", 
                     tx.address, tx.response_data), UVM_HIGH)
        end
        
        // Add specific checks here based on protocol requirements
        if (tx.error) begin
            errors++;
            `uvm_error(get_type_name(), $sformatf("Error detected in transaction: addr=0x%02X", tx.address))
        end
    endfunction
    
    // Report phase
    virtual function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "=== UART Protocol Scoreboard Report ===", UVM_MEDIUM)
        `uvm_info(get_type_name(), $sformatf("Total transactions: %0d", transactions_received), UVM_MEDIUM)
        `uvm_info(get_type_name(), $sformatf("Write transactions: %0d", write_transactions), UVM_MEDIUM)
        `uvm_info(get_type_name(), $sformatf("Read transactions: %0d", read_transactions), UVM_MEDIUM)
        `uvm_info(get_type_name(), $sformatf("Errors detected: %0d", errors), UVM_MEDIUM)
        
        if (errors > 0) begin
            `uvm_error(get_type_name(), $sformatf("Test FAILED with %0d errors", errors))
        end else begin
            `uvm_info(get_type_name(), "Test PASSED - No errors detected", UVM_MEDIUM)
        end
    endfunction
    
endclass
