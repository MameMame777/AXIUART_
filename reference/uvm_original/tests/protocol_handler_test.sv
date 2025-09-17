// Protocol Handler UVM Test
// Target Board: Zybo Z7-20
// Date: August 1, 2025
// Description: UVM test for Protocol_Handler debugging with UART communication

`timescale 1ns / 1ps

`include "uvm_macros.svh"

package protocol_handler_test_pkg;
    import uvm_pkg::*;
    import axi4_lite_pkg::*;
    
    // Protocol Handler Test Configuration
    class protocol_handler_test_config extends uvm_object;
        `uvm_object_utils(protocol_handler_test_config)
        
        // Test configuration parameters
        bit enable_uart_debug = 1;
        bit enable_register_debug = 1;
        bit enable_protocol_debug = 1;
        
        // Timing parameters
        int uart_bit_period_ns = 8680;  // 115200 baud (1/115200 * 1e9)
        int system_clock_period_ns = 8; // 125MHz system clock
        
        function new(string name = "protocol_handler_test_config");
            super.new(name);
        endfunction
    endclass
    
    // Protocol Handler Sequence Item
    class protocol_handler_seq_item extends uvm_sequence_item;
        `uvm_object_utils(protocol_handler_seq_item)
        
        // UART transaction fields
        rand bit [7:0] uart_data;
        rand bit is_read_cmd;
        rand bit [7:0] reg_addr;
        rand bit [31:0] reg_data;
        
        // Transaction type
        typedef enum {
            UART_CHAR,
            READ_CMD,
            WRITE_CMD,
            RESET_SEQUENCE
        } transaction_type_e;
        
        rand transaction_type_e transaction_type;
        
        // Constraints
        constraint valid_commands {
            if (transaction_type == READ_CMD) {
                uart_data inside {8'h52, 8'h72}; // 'R' or 'r'
            }
            if (transaction_type == WRITE_CMD) {
                uart_data inside {8'h57, 8'h77}; // 'W' or 'w'
            }
            reg_addr < 8'h20; // Valid register addresses
        }
        
        function new(string name = "protocol_handler_seq_item");
            super.new(name);
        endfunction
        
        function string convert2string();
            return $sformatf("Type: %s, UART: 0x%02x (%c), Addr: 0x%02x, Data: 0x%08x", 
                           transaction_type.name(), uart_data, uart_data, reg_addr, reg_data);
        endfunction
    endclass
    
    // Protocol Handler Sequencer
    class protocol_handler_sequencer extends uvm_sequencer #(protocol_handler_seq_item);
        `uvm_component_utils(protocol_handler_sequencer)
        
        function new(string name = "protocol_handler_sequencer", uvm_component parent = null);
            super.new(name, parent);
        endfunction
    endclass
    
    // Protocol Handler Driver
    class protocol_handler_driver extends uvm_driver #(protocol_handler_seq_item);
        `uvm_component_utils(protocol_handler_driver)
        
        virtual protocol_handler_if vif;
        protocol_handler_test_config cfg;
        
        function new(string name = "protocol_handler_driver", uvm_component parent = null);
            super.new(name, parent);
        endfunction
        
        function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            if (!uvm_config_db#(virtual protocol_handler_if)::get(this, "", "vif", vif))
                `uvm_fatal("NOVIF", "Virtual interface not found")
            if (!uvm_config_db#(protocol_handler_test_config)::get(this, "", "cfg", cfg))
                `uvm_fatal("NOCFG", "Configuration not found")
        endfunction
        
        task run_phase(uvm_phase phase);
            protocol_handler_seq_item item;
            
            // Initialize interface
            vif.uart_rx_data = 8'h00;
            vif.uart_rx_valid = 1'b0;
            vif.uart_tx_ready = 1'b1;
            vif.reg_rdata = 32'h00000000;
            vif.reg_ready = 1'b1;
            vif.reg_error = 1'b0;
            
            forever begin
                seq_item_port.get_next_item(item);
                drive_item(item);
                seq_item_port.item_done();
            end
        endtask
        
        task drive_item(protocol_handler_seq_item item);
            case (item.transaction_type)
                protocol_handler_seq_item::UART_CHAR: begin
                    drive_uart_char(item.uart_data);
                end
                protocol_handler_seq_item::READ_CMD: begin
                    drive_read_command(item.reg_addr);
                end
                protocol_handler_seq_item::WRITE_CMD: begin
                    drive_write_command(item.reg_addr, item.reg_data);
                end
                protocol_handler_seq_item::RESET_SEQUENCE: begin
                    drive_reset_sequence();
                end
            endcase
        endtask
        
        task drive_uart_char(bit [7:0] data);
            `uvm_info("DRIVER", $sformatf("Driving UART char: 0x%02x (%c)", data, data), UVM_MEDIUM)
            
            @(posedge vif.clk);
            vif.uart_rx_data <= data;
            vif.uart_rx_valid <= 1'b1;
            
            @(posedge vif.clk);
            wait(vif.uart_rx_ready);
            
            @(posedge vif.clk);
            vif.uart_rx_valid <= 1'b0;
            
            // Wait for protocol processing
            repeat(10) @(posedge vif.clk);
        endtask
        
        task drive_read_command(bit [7:0] addr);
            `uvm_info("DRIVER", $sformatf("Driving READ command for address: 0x%02x", addr), UVM_MEDIUM)
            
            // Send 'R' command
            drive_uart_char(8'h52); // 'R'
            
            // Send address high nibble
            drive_uart_char(nibble_to_ascii(addr[7:4]));
            
            // Send address low nibble  
            drive_uart_char(nibble_to_ascii(addr[3:0]));
            
            // Simulate register response
            @(posedge vif.clk);
            vif.reg_rdata <= get_simulated_reg_data(addr);
            vif.reg_ready <= 1'b1;
            
            repeat(50) @(posedge vif.clk); // Wait for response
        endtask
        
        task drive_write_command(bit [7:0] addr, bit [31:0] data);
            `uvm_info("DRIVER", $sformatf("Driving WRITE command for address: 0x%02x, data: 0x%08x", addr, data), UVM_MEDIUM)
            
            // Send 'W' command
            drive_uart_char(8'h57); // 'W'
            
            // Send address high nibble
            drive_uart_char(nibble_to_ascii(addr[7:4]));
            
            // Send address low nibble
            drive_uart_char(nibble_to_ascii(addr[3:0]));
            
            // Send data (8 hex characters)
            for (int i = 7; i >= 0; i--) begin
                drive_uart_char(nibble_to_ascii(data[i*4 +: 4]));
            end
            
            repeat(50) @(posedge vif.clk); // Wait for completion
        endtask
        
        task drive_reset_sequence();
            `uvm_info("DRIVER", "Driving reset sequence", UVM_MEDIUM)
            
            @(posedge vif.clk);
            vif.rst <= 1'b1;
            
            repeat(10) @(posedge vif.clk);
            vif.rst <= 1'b0;
            
            repeat(10) @(posedge vif.clk);
        endtask
        
        function bit [7:0] nibble_to_ascii(bit [3:0] nibble);
            if (nibble < 4'hA)
                return 8'h30 + nibble; // '0'-'9'
            else
                return 8'h41 + (nibble - 4'hA); // 'A'-'F'
        endfunction
        
        function bit [31:0] get_simulated_reg_data(bit [7:0] addr);
            case (addr)
                8'h00: return 32'h00000007; // Control register with UART enabled
                8'h01: return 32'h00000018; // Status register
                8'h02: return 32'h00000000; // TX data register
                8'h03: return 32'h00000000; // RX data register
                8'h04: return 32'h00003C3C; // FIFO status
                8'h05: return 32'h00000000; // Error status
                8'h06: return 32'h3C043C04; // FIFO thresholds
                default: return 32'hDEADBEEF; // Invalid address
            endcase
        endfunction
    endclass
    
    // Protocol Handler Monitor
    class protocol_handler_monitor extends uvm_monitor;
        `uvm_component_utils(protocol_handler_monitor)
        
        virtual protocol_handler_if vif;
        protocol_handler_test_config cfg;
        uvm_analysis_port #(protocol_handler_seq_item) ap;
        
        function new(string name = "protocol_handler_monitor", uvm_component parent = null);
            super.new(name, parent);
        endfunction
        
        function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            ap = new("ap", this);
            if (!uvm_config_db#(virtual protocol_handler_if)::get(this, "", "vif", vif))
                `uvm_fatal("NOVIF", "Virtual interface not found")
            if (!uvm_config_db#(protocol_handler_test_config)::get(this, "", "cfg", cfg))
                `uvm_fatal("NOCFG", "Configuration not found")
        endfunction
        
        task run_phase(uvm_phase phase);
            protocol_handler_seq_item item;
            
            forever begin
                @(posedge vif.clk);
                
                // Monitor UART RX
                if (vif.uart_rx_valid && vif.uart_rx_ready) begin
                    item = protocol_handler_seq_item::type_id::create("item");
                    item.uart_data = vif.uart_rx_data;
                    item.transaction_type = protocol_handler_seq_item::UART_CHAR;
                    
                    `uvm_info("MONITOR", $sformatf("UART RX: 0x%02x (%c)", 
                             vif.uart_rx_data, vif.uart_rx_data), UVM_MEDIUM)
                    ap.write(item);
                end
                
                // Monitor UART TX
                if (vif.uart_tx_valid && vif.uart_tx_ready) begin
                    `uvm_info("MONITOR", $sformatf("UART TX: 0x%02x (%c)", 
                             vif.uart_tx_data, vif.uart_tx_data), UVM_MEDIUM)
                end
                
                // Monitor Register Access
                if (vif.reg_write || vif.reg_read) begin
                    `uvm_info("MONITOR", $sformatf("Register %s: Addr=0x%02x, Data=0x%08x", 
                             vif.reg_write ? "WRITE" : "READ", vif.reg_addr, 
                             vif.reg_write ? vif.reg_wdata : vif.reg_rdata), UVM_MEDIUM)
                end
            end
        endtask
    endclass
    
    // Protocol Handler Agent
    class protocol_handler_agent extends uvm_agent;
        `uvm_component_utils(protocol_handler_agent)
        
        protocol_handler_driver driver;
        protocol_handler_sequencer sequencer;
        protocol_handler_monitor monitor;
        
        function new(string name = "protocol_handler_agent", uvm_component parent = null);
            super.new(name, parent);
        endfunction
        
        function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            
            driver = protocol_handler_driver::type_id::create("driver", this);
            sequencer = protocol_handler_sequencer::type_id::create("sequencer", this);
            monitor = protocol_handler_monitor::type_id::create("monitor", this);
        endfunction
        
        function void connect_phase(uvm_phase phase);
            super.connect_phase(phase);
            driver.seq_item_port.connect(sequencer.seq_item_export);
        endfunction
    endclass
    
endpackage

// Protocol Handler Interface
interface protocol_handler_if(input logic clk);
    logic rst;
    logic enable;
    
    // UART interface
    logic [7:0] uart_rx_data;
    logic uart_rx_valid;
    logic uart_rx_ready;
    logic [7:0] uart_tx_data;
    logic uart_tx_valid;
    logic uart_tx_ready;
    
    // Register interface
    logic [7:0] reg_addr;
    logic [31:0] reg_wdata;
    logic reg_write;
    logic reg_read;
    logic [31:0] reg_rdata;
    logic reg_ready;
    logic reg_error;
    
endinterface
