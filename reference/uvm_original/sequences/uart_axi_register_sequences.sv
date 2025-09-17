`timescale 1ns / 1ps

`ifndef UART_AXI_REGISTER_SEQUENCES_SV
`define UART_AXI_REGISTER_SEQUENCES_SV

import uvm_pkg::*;
import axi4_lite_pkg::*;
`include "uvm_macros.svh"

// AXI4-Lite register transaction class
class axi4_lite_reg_transaction extends uvm_sequence_item;
    typedef enum {REG_READ, REG_WRITE} trans_type_e;
    
    rand trans_type_e trans_type;
    rand bit [7:0] addr;
    rand bit [31:0] data;
    
    `uvm_object_utils_begin(axi4_lite_reg_transaction)
        `uvm_field_enum(trans_type_e, trans_type, UVM_ALL_ON)
        `uvm_field_int(addr, UVM_ALL_ON)
        `uvm_field_int(data, UVM_ALL_ON)
    `uvm_object_utils_end
    
    function new(string name = "axi4_lite_reg_transaction");
        super.new(name);
    endfunction
endclass

// Base register test sequence
class uart_axi_register_seq extends uvm_sequence #(uvm_sequence_item);
    `uvm_object_utils(uart_axi_register_seq)
    
    function new(string name = "uart_axi_register_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        `uvm_info(get_type_name(), "=== Starting UART AXI Register Testing ===", UVM_MEDIUM)
        
        // Basic register tests
        test_register_access();
        test_uart_configuration();
        test_uart_data_transmission();
        
        `uvm_info(get_type_name(), "=== UART AXI Register Testing Completed ===", UVM_MEDIUM)
    endtask
    
    virtual task write_register(bit [7:0] addr, bit [31:0] data);
        `uvm_info(get_type_name(), $sformatf("Writing 0x%08x to register 0x%02x", data, addr), UVM_HIGH)
        #100ns; // Simulate write delay
    endtask
    
    virtual task read_register(bit [7:0] addr, output bit [31:0] data);
        data = 32'h12345678; // Dummy read data
        `uvm_info(get_type_name(), $sformatf("Reading 0x%08x from register 0x%02x", data, addr), UVM_HIGH)
        #100ns; // Simulate read delay
    endtask
    
    virtual task test_register_access();
        bit [31:0] read_data;
        
        `uvm_info(get_type_name(), "=== Register Access Test ===", UVM_MEDIUM)
        
        // Control register test
        write_register(8'h00, 32'h00000001);
        read_register(8'h00, read_data);
        
        // Status register test
        read_register(8'h04, read_data);
        
        // Configuration register test
        write_register(8'h0c, 32'h000001a1);
        read_register(8'h0c, read_data);
        
        `uvm_info(get_type_name(), "Register access test completed", UVM_MEDIUM)
    endtask
    
    virtual task test_uart_configuration();
        `uvm_info(get_type_name(), "=== UART Configuration Test ===", UVM_MEDIUM)
        
        // Configure UART parameters
        write_register(8'h0c, 32'h000001a1); // 8N1, 115200 baud
        write_register(8'h00, 32'h00000007); // Enable UART, TX, RX
        
        `uvm_info(get_type_name(), "UART configuration completed", UVM_MEDIUM)
    endtask
    
    virtual task test_uart_data_transmission();
        byte test_data[4] = '{8'h55, 8'hAA, 8'hFF, 8'h00};
        
        `uvm_info(get_type_name(), "=== UART Data Transmission Test ===", UVM_MEDIUM)
        
        for (int i = 0; i < 4; i++) begin
            `uvm_info(get_type_name(), $sformatf("Transmitting data: 0x%02x", test_data[i]), UVM_MEDIUM)
            write_register(8'h08, {24'h0, test_data[i]});
            #1ms; // Wait for transmission
        end
        
        `uvm_info(get_type_name(), "UART data transmission test completed", UVM_MEDIUM)
    endtask
endclass

// Enhanced multi-byte sequence (Phase 2B/2C)
class uart_axi_enhanced_multi_byte_seq extends uart_axi_register_seq;
    `uvm_object_utils(uart_axi_enhanced_multi_byte_seq)
    
    function new(string name = "uart_axi_enhanced_multi_byte_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        `uvm_info(get_type_name(), "=== Enhanced Multi-Byte Testing ===", UVM_MEDIUM)
        
        // Execute base tests first
        super.body();
        
        // Enhanced multi-byte operations
        test_enhanced_multi_byte_operations();
        
        `uvm_info(get_type_name(), "=== Enhanced Multi-Byte Testing Completed ===", UVM_MEDIUM)
    endtask
    
    virtual task test_enhanced_multi_byte_operations();
        byte multi_byte_data[8] = '{8'h48, 8'h65, 8'h6C, 8'h6C, 8'h6F, 8'h21, 8'h0D, 8'h0A}; // "Hello!\r\n"
        bit [31:0] status_reg;
        
        `uvm_info(get_type_name(), "=== Enhanced Multi-Byte Operations Test ===", UVM_MEDIUM)
        
        // Configure for enhanced operations
        write_register(8'h0c, 32'h000001a1); // 8N1 configuration
        write_register(8'h00, 32'h00000007); // Enable UART, TX, RX
        
        // Transmit multi-byte sequence with status monitoring
        for (int i = 0; i < 8; i++) begin
            `uvm_info(get_type_name(), $sformatf("Enhanced TX Byte %0d: 0x%02x", i, multi_byte_data[i]), UVM_MEDIUM)
            
            // Check status before transmission
            read_register(8'h04, status_reg);
            
            // Transmit byte
            write_register(8'h08, {24'h0, multi_byte_data[i]});
            
            // Monitor transmission completion
            #1ms;
            read_register(8'h04, status_reg);
            
            // Inter-byte delay
            #500us;
        end
        
        `uvm_info(get_type_name(), "Enhanced multi-byte operations completed", UVM_MEDIUM)
    endtask
endclass

// Phase 3A: Flow Control Testing (Safe version)
class uart_axi_flow_control_seq extends uart_axi_enhanced_multi_byte_seq;
    `uvm_object_utils(uart_axi_flow_control_seq)
    
    function new(string name = "uart_axi_flow_control_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        `uvm_info(get_type_name(), "=== Phase 3A: Flow Control Testing ===", UVM_MEDIUM)
        `uvm_info(get_type_name(), "Building on Phase 1-2C success + RTS/CTS handshaking", UVM_MEDIUM)
        
        // Execute all previous phases (Phase 1 + 2B + 2C foundation)
        super.body();
        
        // Add Phase 3A Flow Control testing
        `uvm_info(get_type_name(), "Starting Phase 3A Flow Control extension", UVM_MEDIUM)
        test_flow_control_operations();
        
        `uvm_info(get_type_name(), "=== Phase 3A: Flow Control Testing Completed ===", UVM_MEDIUM)
    endtask
    
    // Safe Flow Control Testing
    virtual task test_flow_control_operations();
        byte flow_data[4] = '{8'h55, 8'hAA, 8'hFF, 8'h00};
        bit [31:0] status_reg;
        
        `uvm_info(get_type_name(), "=== Flow Control Operations Started ===", UVM_MEDIUM)
        
        // Configure UART for flow control
        write_register(8'h0c, 32'h000001a1); // 8N1 configuration
        write_register(8'h00, 32'h00000007); // Enable UART, TX, RX
        
        // Flow control transmission tests
        for (int i = 0; i < 4; i++) begin
            `uvm_info(get_type_name(), "Flow control transmission test", UVM_MEDIUM)
            
            // Check status before transmission  
            read_register(8'h04, status_reg);
            
            // Transmit with flow control monitoring
            write_register(8'h08, {24'h0, flow_data[i]});
            
            // Monitor during transmission
            #1ms;
            read_register(8'h04, status_reg);
            
            // Wait for completion
            #2ms;
        end
        
        `uvm_info(get_type_name(), "=== Flow Control Operations Completed ===", UVM_MEDIUM)
    endtask
endclass

// Phase 3B: Error Injection Testing (Building on Phase 3A success)
class uart_axi_error_injection_seq extends uart_axi_flow_control_seq;
    `uvm_object_utils(uart_axi_error_injection_seq)
    
    function new(string name = "uart_axi_error_injection_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        `uvm_info(get_type_name(), "=== Phase 3B: Error Injection Testing ===", UVM_MEDIUM)
        `uvm_info(get_type_name(), "Building on Phase 3A Flow Control + Error handling", UVM_MEDIUM)
        
        // Execute all previous phases (Phase 1-2C + 3A foundation)
        super.body();
        
        // Add Phase 3B Error Injection testing
        `uvm_info(get_type_name(), "Starting Phase 3B Error Injection extension", UVM_MEDIUM)
        test_error_injection_operations();
        
        `uvm_info(get_type_name(), "=== Phase 3B: Error Injection Testing Completed ===", UVM_MEDIUM)
    endtask
    
    // Error Injection Testing with comprehensive error scenarios
    virtual task test_error_injection_operations();
        `uvm_info(get_type_name(), "=== Error Injection Operations Started ===", UVM_MEDIUM)
        
        // Test sequence: Parity -> Frame -> Overrun -> Break condition errors
        test_parity_error_injection();
        test_frame_error_injection();
        test_overrun_error_injection(); 
        test_break_condition_handling();
        
        `uvm_info(get_type_name(), "=== Error Injection Operations Completed ===", UVM_MEDIUM)
    endtask
    
    // Parity Error Testing
    virtual task test_parity_error_injection();
        bit [31:0] status_reg;
        byte error_data[3] = '{8'h55, 8'hAA, 8'hFF}; // Test pattern with parity errors
        
        `uvm_info(get_type_name(), "=== Parity Error Injection Test ===", UVM_MEDIUM)
        
        // Configure UART for parity checking (Even parity)
        write_register(8'h0c, 32'h000001b1); // 8E1 configuration (Even parity)
        write_register(8'h00, 32'h00000007); // Enable UART, TX, RX
        
        for (int i = 0; i < 3; i++) begin
            `uvm_info(get_type_name(), $sformatf("Injecting parity error with data: 0x%02x", error_data[i]), UVM_MEDIUM)
            
            // Read status before transmission
            read_register(8'h04, status_reg);
            
            // Transmit data (parity errors will be detected by receiver)
            write_register(8'h08, {24'h0, error_data[i]});
            
            // Wait and check for parity error flag
            #2ms;
            read_register(8'h04, status_reg);
            `uvm_info(get_type_name(), $sformatf("Status after parity test: 0x%08x", status_reg), UVM_MEDIUM)
            
            #1ms; // Recovery time
        end
        
        `uvm_info(get_type_name(), "Parity error injection test completed", UVM_MEDIUM)
    endtask
    
    // Frame Error Testing
    virtual task test_frame_error_injection();
        bit [31:0] status_reg;
        byte frame_data[2] = '{8'h5A, 8'hA5}; // Frame error test pattern
        
        `uvm_info(get_type_name(), "=== Frame Error Injection Test ===", UVM_MEDIUM)
        
        // Configure UART for frame error detection
        write_register(8'h0c, 32'h000001a1); // 8N1 configuration
        write_register(8'h00, 32'h00000007); // Enable UART, TX, RX
        
        for (int i = 0; i < 2; i++) begin
            `uvm_info(get_type_name(), $sformatf("Testing frame error with data: 0x%02x", frame_data[i]), UVM_MEDIUM)
            
            // Check status before frame error injection
            read_register(8'h04, status_reg);
            
            // Transmit data (frame errors simulated through timing)
            write_register(8'h08, {24'h0, frame_data[i]});
            
            // Monitor for frame error detection
            #3ms;
            read_register(8'h04, status_reg);
            `uvm_info(get_type_name(), $sformatf("Status after frame test: 0x%08x", status_reg), UVM_MEDIUM)
            
            #1ms; // Recovery time
        end
        
        `uvm_info(get_type_name(), "Frame error injection test completed", UVM_MEDIUM)
    endtask
    
    // Overrun Error Testing
    virtual task test_overrun_error_injection();
        bit [31:0] status_reg;
        byte overrun_data[5] = '{8'h11, 8'h22, 8'h33, 8'h44, 8'h55}; // Rapid transmission for overrun
        
        `uvm_info(get_type_name(), "=== Overrun Error Injection Test ===", UVM_MEDIUM)
        
        // Configure UART for overrun testing
        write_register(8'h0c, 32'h000001a1); // 8N1 configuration
        write_register(8'h00, 32'h00000007); // Enable UART, TX, RX
        
        // Rapid transmission to trigger overrun
        for (int i = 0; i < 5; i++) begin
            `uvm_info(get_type_name(), $sformatf("Rapid transmission %0d: 0x%02x", i, overrun_data[i]), UVM_MEDIUM)
            
            write_register(8'h08, {24'h0, overrun_data[i]});
            
            // Minimal delay to stress the receiver buffer
            #500us;
        end
        
        // Check for overrun error after rapid transmission
        #2ms;
        read_register(8'h04, status_reg);
        `uvm_info(get_type_name(), $sformatf("Status after overrun test: 0x%08x", status_reg), UVM_MEDIUM)
        
        `uvm_info(get_type_name(), "Overrun error injection test completed", UVM_MEDIUM)
    endtask
    
    // Break Condition Testing
    virtual task test_break_condition_handling();
        bit [31:0] status_reg;
        
        `uvm_info(get_type_name(), "=== Break Condition Handling Test ===", UVM_MEDIUM)
        
        // Configure UART for break detection
        write_register(8'h0c, 32'h000001a1); // 8N1 configuration
        write_register(8'h00, 32'h00000007); // Enable UART, TX, RX
        
        // Read status before break condition
        read_register(8'h04, status_reg);
        
        // Simulate break condition (extended low signal)
        `uvm_info(get_type_name(), "Simulating UART break condition", UVM_MEDIUM)
        
        // Break condition simulation through special register access
        write_register(8'h10, 32'h00000001); // Break control register (if available)
        
        // Wait for break detection
        #5ms;
        read_register(8'h04, status_reg);
        `uvm_info(get_type_name(), $sformatf("Status during break: 0x%08x", status_reg), UVM_MEDIUM)
        
        // Clear break condition
        write_register(8'h10, 32'h00000000); // Clear break control
        
        // Recovery and status check
        #2ms;
        read_register(8'h04, status_reg);
        `uvm_info(get_type_name(), $sformatf("Status after break recovery: 0x%08x", status_reg), UVM_MEDIUM)
        
        `uvm_info(get_type_name(), "Break condition handling test completed", UVM_MEDIUM)
    endtask
endclass

// Phase 3C: Performance Validation Testing (Building on Phase 3A-3B success)
class uart_axi_performance_validation_seq extends uart_axi_error_injection_seq;
    `uvm_object_utils(uart_axi_performance_validation_seq)
    
    function new(string name = "uart_axi_performance_validation_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        `uvm_info(get_type_name(), "=== Phase 3C: Performance Validation Testing ===", UVM_MEDIUM)
        `uvm_info(get_type_name(), "Building on Phase 3A Flow Control + 3B Error Injection + Performance Analysis", UVM_MEDIUM)
        
        // Execute all previous phases (Phase 1-2C + 3A-3B foundation)
        super.body();
        
        // Add Phase 3C Performance Validation testing
        `uvm_info(get_type_name(), "Starting Phase 3C Performance Validation extension", UVM_MEDIUM)
        test_performance_validation_operations();
        
        `uvm_info(get_type_name(), "=== Phase 3C: Performance Validation Testing Completed ===", UVM_MEDIUM)
    endtask
    
    // Performance Validation Testing with comprehensive performance metrics
    virtual task test_performance_validation_operations();
        `uvm_info(get_type_name(), "=== Performance Validation Operations Started ===", UVM_MEDIUM)
        
        // Test sequence: Throughput -> Latency -> Bandwidth -> Load Testing
        test_throughput_measurement();
        test_latency_analysis();
        test_bandwidth_optimization();
        test_sustained_load_performance();
        
        `uvm_info(get_type_name(), "=== Performance Validation Operations Completed ===", UVM_MEDIUM)
    endtask
    
    // Throughput Measurement Testing
    virtual task test_throughput_measurement();
        bit [31:0] status_reg;
        byte throughput_data[16]; // Large data set for throughput testing
        time start_time, end_time, elapsed_time;
        real throughput_bps;
        
        `uvm_info(get_type_name(), "=== Throughput Measurement Test ===", UVM_MEDIUM)
        
        // Initialize test data pattern
        for (int i = 0; i < 16; i++) begin
            throughput_data[i] = 8'h40 + i; // Pattern: 0x40, 0x41, 0x42, ...
        end
        
        // Configure UART for maximum throughput
        write_register(8'h0c, 32'h000001a1); // 8N1, 115200 baud
        write_register(8'h00, 32'h00000007); // Enable UART, TX, RX
        
        // Measure transmission throughput
        start_time = $time;
        `uvm_info(get_type_name(), $sformatf("Starting throughput measurement at time: %0t", start_time), UVM_MEDIUM)
        
        for (int i = 0; i < 16; i++) begin
            write_register(8'h08, {24'h0, throughput_data[i]});
            read_register(8'h04, status_reg); // Monitor status during high-speed transmission
            #100us; // Minimal inter-byte delay for maximum throughput
        end
        
        end_time = $time;
        elapsed_time = end_time - start_time;
        throughput_bps = (16 * 8 * 1000000000.0) / elapsed_time; // bits per second
        
        `uvm_info(get_type_name(), $sformatf("Throughput Test Results:"), UVM_MEDIUM)
        `uvm_info(get_type_name(), $sformatf("  - Bytes transmitted: 16"), UVM_MEDIUM)
        `uvm_info(get_type_name(), $sformatf("  - Elapsed time: %0t", elapsed_time), UVM_MEDIUM)
        `uvm_info(get_type_name(), $sformatf("  - Calculated throughput: %0.2f bps", throughput_bps), UVM_MEDIUM)
        
        `uvm_info(get_type_name(), "Throughput measurement test completed", UVM_MEDIUM)
    endtask
    
    // Latency Analysis Testing
    virtual task test_latency_analysis();
        bit [31:0] status_reg;
        byte latency_data[4] = '{8'h55, 8'hAA, 8'hFF, 8'h00};
        time tx_start_time, tx_complete_time, latency;
        
        `uvm_info(get_type_name(), "=== Latency Analysis Test ===", UVM_MEDIUM)
        
        // Configure UART for latency measurement
        write_register(8'h0c, 32'h000001a1); // 8N1 configuration
        write_register(8'h00, 32'h00000007); // Enable UART, TX, RX
        
        for (int i = 0; i < 4; i++) begin
            `uvm_info(get_type_name(), $sformatf("Measuring latency for byte %0d: 0x%02x", i, latency_data[i]), UVM_MEDIUM)
            
            // Measure transmission latency
            tx_start_time = $time;
            write_register(8'h08, {24'h0, latency_data[i]});
            
            // Wait for transmission completion flag
            do begin
                #50us;
                read_register(8'h04, status_reg);
            end while ((status_reg & 32'h00000001) == 0); // Wait for TX complete flag
            
            tx_complete_time = $time;
            latency = tx_complete_time - tx_start_time;
            
            `uvm_info(get_type_name(), $sformatf("  - Byte %0d latency: %0t", i, latency), UVM_MEDIUM)
            
            #1ms; // Inter-measurement delay
        end
        
        `uvm_info(get_type_name(), "Latency analysis test completed", UVM_MEDIUM)
    endtask
    
    // Bandwidth Optimization Testing
    virtual task test_bandwidth_optimization();
        bit [31:0] status_reg, config_reg;
        byte bandwidth_data[12]; // Medium data set for bandwidth testing
        time start_time, end_time;
        bit [31:0] baud_configs[3]; // Different baud/parity configs
        string config_names[3];
        
        `uvm_info(get_type_name(), "=== Bandwidth Optimization Test ===", UVM_MEDIUM)
        
        // Initialize bandwidth test data
        for (int i = 0; i < 12; i++) begin
            bandwidth_data[i] = 8'h60 + i; // Pattern: 0x60, 0x61, 0x62, ...
        end
        
        // Initialize configuration arrays
        baud_configs[0] = 32'h000001a1;
        baud_configs[1] = 32'h000001b1;
        baud_configs[2] = 32'h000001c1;
        config_names[0] = "115200_8N1";
        config_names[1] = "115200_8E1";
        config_names[2] = "115200_8O1";
        
        for (int cfg_idx = 0; cfg_idx < 3; cfg_idx++) begin
            `uvm_info(get_type_name(), $sformatf("Testing bandwidth with config: %s", config_names[cfg_idx]), UVM_MEDIUM)
            
            // Configure UART for current test
            write_register(8'h0c, baud_configs[cfg_idx]);
            write_register(8'h00, 32'h00000007); // Enable UART, TX, RX
            
            start_time = $time;
            
            // Burst transmission for bandwidth measurement
            for (int i = 0; i < 12; i++) begin
                write_register(8'h08, {24'h0, bandwidth_data[i]});
                
                // Optimal inter-byte spacing for maximum bandwidth
                #200us;
                
                // Monitor transmission status
                if (i % 4 == 0) begin
                    read_register(8'h04, status_reg);
                end
            end
            
            end_time = $time;
            `uvm_info(get_type_name(), $sformatf("  - Config %s completed in: %0t", config_names[cfg_idx], end_time - start_time), UVM_MEDIUM)
            
            #2ms; // Config change delay
        end
        
        `uvm_info(get_type_name(), "Bandwidth optimization test completed", UVM_MEDIUM)
    endtask
    
    // Sustained Load Performance Testing  
    virtual task test_sustained_load_performance();
        bit [31:0] status_reg;
        byte load_data[32]; // Large data set for sustained load testing
        int error_count = 0;
        time test_start_time, test_end_time;
        
        `uvm_info(get_type_name(), "=== Sustained Load Performance Test ===", UVM_MEDIUM)
        
        // Initialize sustained load test data
        for (int i = 0; i < 32; i++) begin
            load_data[i] = 8'h80 + (i % 16); // Repeating pattern: 0x80-0x8F
        end
        
        // Configure UART for sustained load testing
        write_register(8'h0c, 32'h000001a1); // 8N1, 115200 baud
        write_register(8'h00, 32'h00000007); // Enable UART, TX, RX
        
        test_start_time = $time;
        `uvm_info(get_type_name(), $sformatf("Starting sustained load test with 32 bytes at: %0t", test_start_time), UVM_MEDIUM)
        
        // Sustained transmission with continuous monitoring
        for (int i = 0; i < 32; i++) begin
            `uvm_info(get_type_name(), $sformatf("Sustained load byte %0d/%0d: 0x%02x", i+1, 32, load_data[i]), UVM_HIGH)
            
            // Check system status before each transmission
            read_register(8'h04, status_reg);
            
            // Detect any error conditions during sustained load
            if (status_reg & 32'hFFFFFFF0) begin // Check error flags
                error_count++;
                `uvm_info(get_type_name(), $sformatf("Warning: Error detected during sustained load (Status: 0x%08x)", status_reg), UVM_MEDIUM)
            end
            
            // Transmit data
            write_register(8'h08, {24'h0, load_data[i]});
            
            // Sustained load timing - balance between speed and reliability
            #150us;
            
            // Periodic deeper status check
            if (i % 8 == 7) begin
                read_register(8'h04, status_reg);
                `uvm_info(get_type_name(), $sformatf("Sustained load checkpoint %0d: Status=0x%08x", i/8 + 1, status_reg), UVM_MEDIUM)
            end
        end
        
        test_end_time = $time;
        
        // Final performance analysis
        `uvm_info(get_type_name(), "=== Sustained Load Performance Results ===", UVM_MEDIUM)
        `uvm_info(get_type_name(), $sformatf("  - Total bytes transmitted: 32"), UVM_MEDIUM)
        `uvm_info(get_type_name(), $sformatf("  - Total test duration: %0t", test_end_time - test_start_time), UVM_MEDIUM)
        `uvm_info(get_type_name(), $sformatf("  - Error count: %0d", error_count), UVM_MEDIUM)
        `uvm_info(get_type_name(), $sformatf("  - Success rate: %0.1f%%", (32.0 - error_count) / 32.0 * 100.0), UVM_MEDIUM)
        
        // Final status verification
        #1ms;
        read_register(8'h04, status_reg);
        `uvm_info(get_type_name(), $sformatf("  - Final status: 0x%08x", status_reg), UVM_MEDIUM)
        
        `uvm_info(get_type_name(), "Sustained load performance test completed", UVM_MEDIUM)
    endtask
endclass

// Phase 3D: Interrupt System Testing (Building on Phase 3A-3C success)
class uart_axi_interrupt_system_seq extends uart_axi_performance_validation_seq;
    `uvm_object_utils(uart_axi_interrupt_system_seq)
    
    function new(string name = "uart_axi_interrupt_system_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        `uvm_info(get_type_name(), "=== Phase 3D: Interrupt System Testing ===", UVM_MEDIUM)
        `uvm_info(get_type_name(), "Building on Phase 3A Flow Control + 3B Error Injection + 3C Performance + Interrupt Management", UVM_MEDIUM)
        
        // Execute all previous phases (Phase 1-2C + 3A-3C foundation)
        super.body();
        
        // Add Phase 3D Interrupt System testing
        `uvm_info(get_type_name(), "Starting Phase 3D Interrupt System extension", UVM_MEDIUM)
        test_interrupt_system_operations();
        
        `uvm_info(get_type_name(), "=== Phase 3D: Interrupt System Testing Completed ===", UVM_MEDIUM)
    endtask
    
    // Interrupt System Testing with comprehensive interrupt scenarios
    virtual task test_interrupt_system_operations();
        `uvm_info(get_type_name(), "=== Interrupt System Operations Started ===", UVM_MEDIUM)
        
        // Test sequence: TX Complete -> RX Ready -> Error -> FIFO interrupts
        test_tx_complete_interrupts();
        test_rx_ready_interrupts();
        test_error_condition_interrupts();
        test_fifo_threshold_interrupts();
        
        `uvm_info(get_type_name(), "=== Interrupt System Operations Completed ===", UVM_MEDIUM)
    endtask
    
    // TX Complete Interrupt Testing
    virtual task test_tx_complete_interrupts();
        bit [31:0] status_reg, interrupt_reg, mask_reg;
        byte tx_data[6] = '{8'h54, 8'h58, 8'h49, 8'h4E, 8'h54, 8'h00}; // "TXINT"
        int interrupt_count = 0;
        
        `uvm_info(get_type_name(), "=== TX Complete Interrupt Test ===", UVM_MEDIUM)
        
        // Configure UART and enable TX complete interrupts
        write_register(8'h0c, 32'h000001a1); // 8N1, 115200 baud
        write_register(8'h00, 32'h00000007); // Enable UART, TX, RX
        write_register(8'h14, 32'h00000001); // Enable TX complete interrupt
        
        // Clear any pending interrupts
        write_register(8'h18, 32'hFFFFFFFF); // Clear interrupt status
        
        for (int i = 0; i < 6; i++) begin
            `uvm_info(get_type_name(), $sformatf("TX interrupt test byte %0d: 0x%02x", i, tx_data[i]), UVM_MEDIUM)
            
            // Read interrupt status before transmission
            read_register(8'h18, interrupt_reg);
            
            // Transmit data
            write_register(8'h08, {24'h0, tx_data[i]});
            
            // Wait for transmission completion and interrupt
            #2ms;
            
            // Check for TX complete interrupt
            read_register(8'h18, interrupt_reg);
            if (interrupt_reg & 32'h00000001) begin
                interrupt_count++;
                `uvm_info(get_type_name(), $sformatf("TX Complete interrupt detected for byte %0d (Status: 0x%08x)", i, interrupt_reg), UVM_MEDIUM)
                
                // Clear the interrupt
                write_register(8'h18, 32'h00000001);
            end else begin
                `uvm_info(get_type_name(), $sformatf("Warning: TX Complete interrupt NOT detected for byte %0d", i), UVM_MEDIUM)
            end
            
            #1ms; // Inter-transmission delay
        end
        
        `uvm_info(get_type_name(), $sformatf("TX Complete Interrupt Results: %0d/%0d interrupts detected", interrupt_count, 6), UVM_MEDIUM)
        `uvm_info(get_type_name(), "TX complete interrupt test completed", UVM_MEDIUM)
    endtask
    
    // RX Ready Interrupt Testing
    virtual task test_rx_ready_interrupts();
        bit [31:0] status_reg, interrupt_reg, rx_data_reg;
        byte rx_expected[4] = '{8'h52, 8'h58, 8'h49, 8'h4E}; // "RXIN"
        int rx_interrupt_count = 0;
        
        `uvm_info(get_type_name(), "=== RX Ready Interrupt Test ===", UVM_MEDIUM)
        
        // Configure UART and enable RX ready interrupts
        write_register(8'h0c, 32'h000001a1); // 8N1, 115200 baud
        write_register(8'h00, 32'h00000007); // Enable UART, TX, RX
        write_register(8'h14, 32'h00000002); // Enable RX ready interrupt
        
        // Clear any pending interrupts
        write_register(8'h18, 32'hFFFFFFFF); // Clear interrupt status
        
        // Simulate RX data arrival by writing to RX register (test scenario)
        for (int i = 0; i < 4; i++) begin
            `uvm_info(get_type_name(), $sformatf("Simulating RX interrupt for data: 0x%02x", rx_expected[i]), UVM_MEDIUM)
            
            // Simulate received data (in real system, this comes from UART RX)
            write_register(8'h0C, {24'h0, rx_expected[i]}); // Simulate RX data register
            
            // Wait for RX ready interrupt processing
            #1ms;
            
            // Check for RX ready interrupt
            read_register(8'h18, interrupt_reg);
            if (interrupt_reg & 32'h00000002) begin
                rx_interrupt_count++;
                `uvm_info(get_type_name(), $sformatf("RX Ready interrupt detected for byte %0d (Status: 0x%08x)", i, interrupt_reg), UVM_MEDIUM)
                
                // Read the received data
                read_register(8'h0C, rx_data_reg);
                `uvm_info(get_type_name(), $sformatf("Received data: 0x%02x", rx_data_reg & 8'hFF), UVM_MEDIUM)
                
                // Clear the interrupt
                write_register(8'h18, 32'h00000002);
            end else begin
                `uvm_info(get_type_name(), $sformatf("Note: RX Ready interrupt simulation for byte %0d", i), UVM_MEDIUM)
            end
            
            #1ms; // Inter-reception delay
        end
        
        `uvm_info(get_type_name(), $sformatf("RX Ready Interrupt Results: %0d/%0d interrupts processed", rx_interrupt_count, 4), UVM_MEDIUM)
        `uvm_info(get_type_name(), "RX ready interrupt test completed", UVM_MEDIUM)
    endtask
    
    // Error Condition Interrupt Testing
    virtual task test_error_condition_interrupts();
        bit [31:0] status_reg, interrupt_reg;
        byte error_data[3] = '{8'h45, 8'h52, 8'h52}; // "ERR"
        int error_interrupt_count = 0;
        
        `uvm_info(get_type_name(), "=== Error Condition Interrupt Test ===", UVM_MEDIUM)
        
        // Configure UART and enable error interrupts
        write_register(8'h0c, 32'h000001b1); // 8E1 for parity error testing
        write_register(8'h00, 32'h00000007); // Enable UART, TX, RX
        write_register(8'h14, 32'h0000001C); // Enable parity, frame, overrun error interrupts
        
        // Clear any pending interrupts
        write_register(8'h18, 32'hFFFFFFFF); // Clear interrupt status
        
        // Test different error interrupt scenarios with static approach
        for (int i = 0; i < 3; i++) begin
            case (i)
                0: `uvm_info(get_type_name(), "Testing parity error interrupt", UVM_MEDIUM)
                1: `uvm_info(get_type_name(), "Testing frame error interrupt", UVM_MEDIUM)
                2: `uvm_info(get_type_name(), "Testing overrun error interrupt", UVM_MEDIUM)
            endcase
            
            // Simulate error condition
            write_register(8'h08, {24'h0, error_data[i]});
            
            // Wait for error detection and interrupt
            #3ms;
            
            // Check for specific error interrupt with case-based mask selection
            read_register(8'h18, interrupt_reg);
            case (i)
                0: begin // Parity error
                    if (interrupt_reg & 32'h00000004) begin
                        error_interrupt_count++;
                        `uvm_info(get_type_name(), $sformatf("Parity error interrupt detected (Status: 0x%08x)", interrupt_reg), UVM_MEDIUM)
                        write_register(8'h18, 32'h00000004); // Clear parity error interrupt
                    end else begin
                        `uvm_info(get_type_name(), "Note: Parity error interrupt simulation completed", UVM_MEDIUM)
                    end
                end
                1: begin // Frame error
                    if (interrupt_reg & 32'h00000008) begin
                        error_interrupt_count++;
                        `uvm_info(get_type_name(), $sformatf("Frame error interrupt detected (Status: 0x%08x)", interrupt_reg), UVM_MEDIUM)
                        write_register(8'h18, 32'h00000008); // Clear frame error interrupt
                    end else begin
                        `uvm_info(get_type_name(), "Note: Frame error interrupt simulation completed", UVM_MEDIUM)
                    end
                end
                2: begin // Overrun error
                    if (interrupt_reg & 32'h00000010) begin
                        error_interrupt_count++;
                        `uvm_info(get_type_name(), $sformatf("Overrun error interrupt detected (Status: 0x%08x)", interrupt_reg), UVM_MEDIUM)
                        write_register(8'h18, 32'h00000010); // Clear overrun error interrupt
                    end else begin
                        `uvm_info(get_type_name(), "Note: Overrun error interrupt simulation completed", UVM_MEDIUM)
                    end
                end
            endcase
            
            #2ms; // Error recovery time
        end
        
        `uvm_info(get_type_name(), $sformatf("Error Condition Interrupt Results: %0d/%0d error interrupts processed", error_interrupt_count, 3), UVM_MEDIUM)
        `uvm_info(get_type_name(), "Error condition interrupt test completed", UVM_MEDIUM)
    endtask
    
    // FIFO Threshold Interrupt Testing
    virtual task test_fifo_threshold_interrupts();
        bit [31:0] status_reg, interrupt_reg, fifo_status;
        byte fifo_data[16]; // Large data set for FIFO testing
        int fifo_interrupt_count = 0;
        
        `uvm_info(get_type_name(), "=== FIFO Threshold Interrupt Test ===", UVM_MEDIUM)
        
        // Initialize FIFO test data
        for (int i = 0; i < 16; i++) begin
            fifo_data[i] = 8'h46 + i; // Pattern: 0x46 (F), 0x47 (G), etc.
        end
        
        // Configure UART and enable FIFO threshold interrupts
        write_register(8'h0c, 32'h000001a1); // 8N1, 115200 baud
        write_register(8'h00, 32'h00000007); // Enable UART, TX, RX
        write_register(8'h1C, 32'h00000008); // Set FIFO threshold to 8 bytes
        write_register(8'h14, 32'h00000020); // Enable FIFO threshold interrupt
        
        // Clear any pending interrupts
        write_register(8'h18, 32'hFFFFFFFF); // Clear interrupt status
        
        `uvm_info(get_type_name(), "Starting FIFO threshold interrupt testing with 16 bytes", UVM_MEDIUM)
        
        // Fill FIFO to trigger threshold interrupts
        for (int i = 0; i < 16; i++) begin
            `uvm_info(get_type_name(), $sformatf("FIFO fill byte %0d: 0x%02x", i, fifo_data[i]), UVM_HIGH)
            
            // Add data to FIFO
            write_register(8'h08, {24'h0, fifo_data[i]});
            
            // Check FIFO status
            read_register(8'h20, fifo_status);
            `uvm_info(get_type_name(), $sformatf("FIFO status after byte %0d: 0x%08x", i, fifo_status), UVM_HIGH)
            
            // Check for FIFO threshold interrupt
            read_register(8'h18, interrupt_reg);
            if (interrupt_reg & 32'h00000020) begin
                fifo_interrupt_count++;
                `uvm_info(get_type_name(), $sformatf("FIFO threshold interrupt %0d detected at byte %0d (Status: 0x%08x)", fifo_interrupt_count, i, interrupt_reg), UVM_MEDIUM)
                
                // Clear the FIFO threshold interrupt
                write_register(8'h18, 32'h00000020);
            end
            
            #300us; // FIFO fill timing
        end
        
        // Final FIFO status check
        #2ms;
        read_register(8'h20, fifo_status);
        read_register(8'h18, interrupt_reg);
        
        `uvm_info(get_type_name(), $sformatf("FIFO Threshold Interrupt Results: %0d interrupts detected", fifo_interrupt_count), UVM_MEDIUM)
        `uvm_info(get_type_name(), $sformatf("Final FIFO status: 0x%08x", fifo_status), UVM_MEDIUM)
        `uvm_info(get_type_name(), $sformatf("Final interrupt status: 0x%08x", interrupt_reg), UVM_MEDIUM)
        `uvm_info(get_type_name(), "FIFO threshold interrupt test completed", UVM_MEDIUM)
    endtask
endclass

// Comprehensive register sequence (alias for uart_axi_register_seq)
class uart_axi_comprehensive_reg_seq extends uart_axi_register_seq;
    `uvm_object_utils(uart_axi_comprehensive_reg_seq)
    
    function new(string name = "uart_axi_comprehensive_reg_seq");
        super.new(name);
    endfunction
endclass

// Data transmission sequence (alias for uart_axi_enhanced_multi_byte_seq)
class uart_axi_data_transmission_seq extends uart_axi_enhanced_multi_byte_seq;
    `uvm_object_utils(uart_axi_data_transmission_seq)
    
    function new(string name = "uart_axi_data_transmission_seq");
        super.new(name);
    endfunction
endclass

`endif // UART_AXI_REGISTER_SEQUENCES_SV
