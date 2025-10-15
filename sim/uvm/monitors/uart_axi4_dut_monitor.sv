`timescale 1ns / 1ps

import uvm_pkg::*;
import uart_axi4_test_pkg::*;
`include "uvm_macros.svh"

// Enhanced DUT Internal State Monitor for QA-2.1
// Monitors internal DUT signals for comprehensive verification

class uart_axi4_dut_monitor extends uvm_monitor;
    `uvm_component_utils(uart_axi4_dut_monitor)
    
    // Virtual interface handle
    virtual uart_if uart_vif;
    virtual axi4_lite_if axi_vif;
    virtual bridge_status_if bridge_vif;
    
    // Analysis ports for communication with scoreboard
    uvm_analysis_port #(uart_axi4_dut_transaction) dut_state_port;
    uvm_analysis_port #(uart_frame_transaction) frame_analysis_port;
    
    // Configuration and control
    uart_axi4_config cfg;
    bit enable_monitoring = 1;
    
    // Internal monitoring variables
    uart_frame_transaction current_frame;
    time last_activity_time;
    
    function new(string name = "uart_axi4_dut_monitor", uvm_component parent = null);
        super.new(name, parent);
        dut_state_port = new("dut_state_port", this);
        frame_analysis_port = new("frame_analysis_port", this);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        if (!uvm_config_db#(uart_axi4_config)::get(this, "", "config", cfg)) begin
            `uvm_warning("NO_CFG", "Configuration not found, using defaults")
            cfg = uart_axi4_config::type_id::create("cfg");
        end
        
        // Get virtual interfaces
        if (!uvm_config_db#(virtual uart_if)::get(this, "", "uart_vif", uart_vif)) begin
            `uvm_fatal("NO_VIF", "Failed to get UART virtual interface")
        end
        
        if (!uvm_config_db#(virtual axi4_lite_if)::get(this, "", "axi_vif", axi_vif)) begin
            `uvm_fatal("NO_VIF", "Failed to get AXI4-Lite virtual interface")
        end
        
        if (!uvm_config_db#(virtual bridge_status_if)::get(this, "", "bridge_vif", bridge_vif)) begin
            `uvm_warning("NO_VIF", "Bridge status interface not available")
        end
    endfunction
    
    task run_phase(uvm_phase phase);
        fork
            monitor_uart_rx_activity();
            monitor_axi_activity();
            monitor_dut_internal_state();
            monitor_frame_processing();
        join_none
    endtask
    
    // Monitor UART RX activity and frame detection
    task monitor_uart_rx_activity();
        uart_axi4_dut_transaction dut_trans;
        
        forever begin
            @(posedge uart_vif.clk);
            
            if (!enable_monitoring) continue;
            
            // Monitor UART RX data reception
            if (uart_vif.rx_valid) begin
                dut_trans = uart_axi4_dut_transaction::type_id::create("dut_trans");
                dut_trans.transaction_type = UART_RX_DATA;
                dut_trans.data_value = uart_vif.rx_data;
                dut_trans.timestamp = $time;
                
                `uvm_info("DUT_MON", $sformatf("UART RX Data: 0x%02h at %0t", 
                    uart_vif.rx_data, $time), UVM_HIGH)
                
                dut_state_port.write(dut_trans);
                last_activity_time = $time;
            end
            
            // Monitor frame start detection
            if (uart_vif.frame_start) begin
                dut_trans = uart_axi4_dut_transaction::type_id::create("dut_trans");
                dut_trans.transaction_type = FRAME_START_DETECTED;
                dut_trans.timestamp = $time;
                
                `uvm_info("DUT_MON", $sformatf("Frame start detected at %0t", $time), UVM_MEDIUM)
                dut_state_port.write(dut_trans);
            end
            
            // Monitor frame completion
            if (uart_vif.frame_complete) begin
                dut_trans = uart_axi4_dut_transaction::type_id::create("dut_trans");
                dut_trans.transaction_type = FRAME_COMPLETE;
                dut_trans.timestamp = $time;
                
                `uvm_info("DUT_MON", $sformatf("Frame complete at %0t", $time), UVM_MEDIUM)
                dut_state_port.write(dut_trans);
            end
        end
    endtask
    
    // Monitor AXI4-Lite bus activity
    task monitor_axi_activity();
        uart_axi4_dut_transaction dut_trans;
        
        forever begin
            @(posedge axi_vif.aclk);
            
            if (!enable_monitoring) continue;
            
            // Monitor AXI write address phase
            if (axi_vif.awvalid && axi_vif.awready) begin
                dut_trans = uart_axi4_dut_transaction::type_id::create("dut_trans");
                dut_trans.transaction_type = AXI_WRITE_ADDR;
                dut_trans.address = axi_vif.awaddr;
                dut_trans.timestamp = $time;
                
                `uvm_info("DUT_MON", $sformatf("AXI Write Addr: 0x%08h at %0t", 
                    axi_vif.awaddr, $time), UVM_HIGH)
                
                dut_state_port.write(dut_trans);
                last_activity_time = $time;
            end
            
            // Monitor AXI write data phase
            if (axi_vif.wvalid && axi_vif.wready) begin
                dut_trans = uart_axi4_dut_transaction::type_id::create("dut_trans");
                dut_trans.transaction_type = AXI_WRITE_DATA;
                dut_trans.data_value = axi_vif.wdata;
                dut_trans.timestamp = $time;
                
                `uvm_info("DUT_MON", $sformatf("AXI Write Data: 0x%08h at %0t", 
                    axi_vif.wdata, $time), UVM_HIGH)
                
                dut_state_port.write(dut_trans);
            end
            
            // Monitor AXI write response
            if (axi_vif.bvalid && axi_vif.bready) begin
                dut_trans = uart_axi4_dut_transaction::type_id::create("dut_trans");
                dut_trans.transaction_type = AXI_WRITE_RESP;
                dut_trans.response = axi_response_t'(axi_vif.bresp);
                dut_trans.timestamp = $time;
                
                `uvm_info("DUT_MON", $sformatf("AXI Write Response: %s at %0t", 
                    (axi_vif.bresp == 0) ? "OKAY" : "ERROR", $time), UVM_MEDIUM)
                
                dut_state_port.write(dut_trans);
            end
            
            // Monitor AXI read address phase
            if (axi_vif.arvalid && axi_vif.arready) begin
                dut_trans = uart_axi4_dut_transaction::type_id::create("dut_trans");
                dut_trans.transaction_type = AXI_READ_ADDR;
                dut_trans.address = axi_vif.araddr;
                dut_trans.timestamp = $time;
                
                `uvm_info("DUT_MON", $sformatf("AXI Read Addr: 0x%08h at %0t", 
                    axi_vif.araddr, $time), UVM_HIGH)
                
                dut_state_port.write(dut_trans);
            end
            
            // Monitor AXI read data phase
            if (axi_vif.rvalid && axi_vif.rready) begin
                dut_trans = uart_axi4_dut_transaction::type_id::create("dut_trans");
                dut_trans.transaction_type = AXI_READ_DATA;
                dut_trans.data_value = axi_vif.rdata;
                dut_trans.response = axi_response_t'(axi_vif.rresp);
                dut_trans.timestamp = $time;
                
                `uvm_info("DUT_MON", $sformatf("AXI Read Data: 0x%08h, Resp: %s at %0t", 
                    axi_vif.rdata, (axi_vif.rresp == 0) ? "OKAY" : "ERROR", $time), UVM_MEDIUM)
                
                dut_state_port.write(dut_trans);
            end
        end
    endtask
    
    // Monitor internal DUT state changes
    task monitor_dut_internal_state();
        uart_axi4_dut_transaction dut_trans;
        
        forever begin
            @(posedge uart_vif.clk);
            
            if (!enable_monitoring) continue;
            
            // Monitor bridge status if available
            if (bridge_vif != null) begin
                // Monitor frame parser state changes
                if (bridge_vif.frame_parser_state_changed) begin
                    dut_trans = uart_axi4_dut_transaction::type_id::create("dut_trans");
                    dut_trans.transaction_type = INTERNAL_STATE_CHANGE;
                    dut_trans.state_info = $sformatf("Frame Parser State: %s", 
                        bridge_vif.get_frame_parser_state_name());
                    dut_trans.timestamp = $time;
                    
                    `uvm_info("DUT_MON", $sformatf("Internal state change: %s at %0t", 
                        dut_trans.state_info, $time), UVM_HIGH)
                    
                    dut_state_port.write(dut_trans);
                end
                
                // Monitor FIFO status
                if (bridge_vif.fifo_status_changed) begin
                    dut_trans = uart_axi4_dut_transaction::type_id::create("dut_trans");
                    dut_trans.transaction_type = FIFO_STATUS_CHANGE;
                    dut_trans.state_info = $sformatf("FIFO Status - RX: %0d/%0d, TX: %0d/%0d", 
                        bridge_vif.rx_fifo_count, bridge_vif.rx_fifo_depth,
                        bridge_vif.tx_fifo_count, bridge_vif.tx_fifo_depth);
                    dut_trans.timestamp = $time;
                    
                    `uvm_info("DUT_MON", $sformatf("FIFO status: %s at %0t", 
                        dut_trans.state_info, $time), UVM_HIGH)
                    
                    dut_state_port.write(dut_trans);
                end
            end
        end
    endtask
    
    // Monitor frame processing pipeline
    task monitor_frame_processing();
        uart_frame_transaction frame_trans;
        
        forever begin
            @(posedge uart_vif.clk);
            
            if (!enable_monitoring) continue;
            
            // Detect frame processing events
            if (uart_vif.frame_processing_active) begin
                int payload_len;
                frame_trans = uart_frame_transaction::type_id::create("frame_trans");

                frame_trans.sof = SOF_HOST_TO_DEVICE;
                frame_trans.start_delimiter = SOF_HOST_TO_DEVICE;
                frame_trans.cmd = uart_vif.current_command;
                frame_trans.addr = uart_vif.current_address;
                frame_trans.target_addr = uart_vif.current_address;

                payload_len = int'(uart_vif.current_data_length);
                if (payload_len < 0) begin
                    payload_len = 0;
                end else if (payload_len > 8) begin
                    payload_len = 8; // uart_if exposes up to 8 payload bytes
                end

                frame_trans.len = payload_len[7:0];
                frame_trans.data_length = payload_len;

                frame_trans.data = new[payload_len];
                frame_trans.payload_data = new[payload_len];
                frame_trans.frame_data = new[payload_len];
                frame_trans.frame_length = payload_len;

                for (int idx = 0; idx < payload_len; idx++) begin
                    logic [7:0] byte_val;
                    byte_val = (uart_vif.current_payload >> (idx * 8)) & 8'hFF;
                    frame_trans.data[idx] = byte_val;
                    frame_trans.payload_data[idx] = byte_val;
                    frame_trans.frame_data[idx] = byte_val;
                end

                frame_trans.crc = uart_vif.current_crc;
                frame_trans.crc_received = uart_vif.current_crc;
                frame_trans.crc_calculated = uart_vif.current_crc;
                frame_trans.timestamp = $realtime;
                frame_trans.direction = UART_RX;

                `uvm_info("DUT_MON", $sformatf("Frame processing: Cmd=0x%02h, Addr=0x%08h, Len=%0d at %0t",
                    frame_trans.cmd, frame_trans.addr, payload_len, $time), UVM_MEDIUM)

                frame_analysis_port.write(frame_trans);
            end
        end
    endtask
    
    // Function to check for activity timeout
    function bit check_activity_timeout(time timeout_ns = 1000000);
        if (last_activity_time == 0) return 0; // No activity recorded yet
        return (($time - last_activity_time) > timeout_ns);
    endfunction
    
    // Function to get monitor statistics
    function string get_monitor_statistics();
        return $sformatf("DUT Monitor Stats - Last Activity: %0t, Status: %s", 
            last_activity_time, enable_monitoring ? "Active" : "Disabled");
    endfunction
    
endclass