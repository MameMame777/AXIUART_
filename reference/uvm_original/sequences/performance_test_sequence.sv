// Performance Test Sequence
// Target Board: Zybo Z7-20
// Date: July 26, 2025
// Description: Performance and throughput test

`ifndef PERFORMANCE_TEST_SEQUENCE_SV
`define PERFORMANCE_TEST_SEQUENCE_SV

class performance_test_sequence extends axi4_lite_base_sequence;
    
    // Performance metrics
    time start_time, end_time;
    int bytes_transmitted;
    int transactions_completed;
    
    // UVM registration
    `uvm_object_utils(performance_test_sequence)
    
    // Constructor
    function new(string name = "performance_test_sequence");
        super.new(name);
        bytes_transmitted = 0;
        transactions_completed = 0;
    endfunction
    
    // Main sequence body
    virtual task body();
        `uvm_info("PERF_TEST", "Starting performance test", UVM_LOW)
        
        // Step 1: Setup for performance testing
        setup_performance_test();
        
        // Step 2: Maximum throughput test
        test_max_throughput();
        
        // Step 3: Sustained load test
        test_sustained_load();
        
        // Step 4: Burst performance test
        test_burst_performance();
        
        // Step 5: Mixed access pattern test
        test_mixed_access_patterns();
        
        // Step 6: Generate performance report
        generate_performance_report();
        
        `uvm_info("PERF_TEST", "Performance test completed", UVM_LOW)
    endtask
    
    // Setup for performance testing
    task setup_performance_test();
        `uvm_info("PERF_TEST", "Configuring for performance test", UVM_MEDIUM)
        
        // Enable UART with optimal settings
        write_register(ADDR_CONTROL_REG, 32'h00000001);
        
        // Set FIFO thresholds for maximum performance
        write_register(ADDR_FIFO_THRESH, 32'h00300020); // TX=48, RX=32
        
        // Clear any existing errors
        write_register(ADDR_ERROR_STATUS, 32'hFFFFFFFF);
        
        // Reset counters
        bytes_transmitted = 0;
        transactions_completed = 0;
        
        #100ns;
    endtask
    
    // Test maximum throughput
    task test_max_throughput();
        bit [31:0] status;
        bit [1:0] resp;
        int fifo_check_interval = 10;
        
        `uvm_info("PERF_TEST", "Testing maximum throughput", UVM_MEDIUM)
        
        start_time = $time;
        
        // Continuous transmission test
        for (int i = 0; i < 1000; i++) begin
            // Check FIFO status periodically to avoid overflow
            if (i % fifo_check_interval == 0) begin
                read_register(ADDR_FIFO_STATUS, status, resp);
                if (resp == AXI_RESP_OKAY && status[9:8] != 2'b00) begin // TX FIFO not empty
                    // Wait for some space in FIFO
                    wait_for_fifo_space();
                end
            end
            
            // Send data
            write_register(ADDR_TX_DATA_REG, 32'h00000030 + (i % 10)); // '0'-'9'
            bytes_transmitted++;
            transactions_completed++;
            
            // Minimal delay for realistic timing
            #5ns;
        end
        
        // Wait for all transmissions to complete
        wait_for_tx_completion();
        
        end_time = $time;
        
        calculate_throughput("Maximum Throughput Test");
    endtask
    
    // Test sustained load
    task test_sustained_load();
        bit [31:0] pattern_data[] = {
            32'h48656C6C, // "Hell"
            32'h6F20576F, // "o Wo"
            32'h726C6421  // "rld!"
        };
        
        `uvm_info("PERF_TEST", "Testing sustained load", UVM_MEDIUM)
        
        start_time = $time;
        bytes_transmitted = 0;
        transactions_completed = 0;
        
        // Sustained transmission over longer period
        for (int cycle = 0; cycle < 50; cycle++) begin
            foreach (pattern_data[i]) begin
                // Write 32-bit data (4 bytes)
                write_register(ADDR_TX_DATA_REG, pattern_data[i]);
                bytes_transmitted += 4;
                transactions_completed++;
                
                // Realistic inter-transaction delay
                #50ns;
                
                // Periodic FIFO management
                if (transactions_completed % 20 == 0) begin
                    manage_fifo_flow();
                end
            end
            
            // Inter-cycle delay
            #1us;
        end
        
        wait_for_tx_completion();
        end_time = $time;
        
        calculate_throughput("Sustained Load Test");
    endtask
    
    // Test burst performance
    task test_burst_performance();
        bit [7:0] burst_sizes[] = {1, 4, 8, 16, 32};
        time burst_start, burst_end;
        
        `uvm_info("PERF_TEST", "Testing burst performance", UVM_MEDIUM)
        
        foreach (burst_sizes[i]) begin
            int burst_size = burst_sizes[i];
            
            `uvm_info("PERF_TEST", $sformatf("Testing burst size: %0d", burst_size), UVM_MEDIUM)
            
            burst_start = $time;
            
            // Execute burst
            for (int j = 0; j < burst_size; j++) begin
                write_register(ADDR_TX_DATA_REG, 32'h00000041 + j); // 'A', 'B', 'C'...
                bytes_transmitted++;
                transactions_completed++;
            end
            
            wait_for_tx_completion();
            burst_end = $time;
            
            // Calculate burst metrics (simplified for compilation)
            // int burst_time_ns = burst_end - burst_start;
            // int burst_throughput_x1000 = (burst_size * 8 * 1000000) / burst_time_ns; // Mbps * 1000
            
            `uvm_info("PERF_TEST", $sformatf("Burst size %0d completed", burst_size), UVM_MEDIUM)
            
            #500ns; // Inter-burst delay
        end
    endtask
    
    // Test mixed access patterns
    task test_mixed_access_patterns();
        bit [31:0] rdata;
        bit [1:0] resp;
        
        `uvm_info("PERF_TEST", "Testing mixed access patterns", UVM_MEDIUM)
        
        start_time = $time;
        bytes_transmitted = 0;
        transactions_completed = 0;
        
        // Mixed read/write pattern
        for (int i = 0; i < 100; i++) begin
            // Write operation
            write_register(ADDR_TX_DATA_REG, 32'h00000060 + (i % 26)); // 'a'-'z'
            bytes_transmitted++;
            transactions_completed++;
            
            // Status read
            read_register(ADDR_FIFO_STATUS, rdata, resp);
            transactions_completed++;
            
            // Control register read/modify/write
            if (i % 10 == 0) begin
                read_modify_write(ADDR_CONTROL_REG, 32'h00000002, (i % 2) ? 32'h00000002 : 32'h00000000);
                transactions_completed += 2; // RMW counts as 2 transactions
            end
            
            // Variable delay
            #(20ns + (i % 5) * 10ns);
        end
        
        wait_for_tx_completion();
        end_time = $time;
        
        calculate_throughput("Mixed Access Pattern Test");
    endtask
    
    // Wait for FIFO space
    task wait_for_fifo_space();
        bit [31:0] status;
        bit [1:0] resp;
        int timeout = 0;
        
        do begin
            #50ns;
            read_register(ADDR_FIFO_STATUS, status, resp);
            timeout++;
            if (timeout > 100) begin
                `uvm_warning("PERF_TEST", "Timeout waiting for FIFO space")
                return;
            end
        end while (resp == AXI_RESP_OKAY && status[11:8] > 4'h0C); // Wait for FIFO to have space
    endtask
    
    // Manage FIFO flow
    task manage_fifo_flow();
        bit [31:0] status;
        bit [1:0] resp;
        
        read_register(ADDR_FIFO_STATUS, status, resp);
        if (resp == AXI_RESP_OKAY) begin
            int tx_level = status[15:8];
            int rx_level = status[7:0];
            
            if (tx_level > 50) begin
                `uvm_info("PERF_TEST", $sformatf("TX FIFO level high: %0d", tx_level), UVM_HIGH)
                #200ns; // Allow some drainage
            end
        end
    endtask
    
    // Wait for transmission completion
    task wait_for_tx_completion();
        bit [31:0] status;
        bit [1:0] resp;
        int timeout = 0;
        
        do begin
            #100ns;
            read_register(ADDR_FIFO_STATUS, status, resp);
            timeout++;
            if (timeout > 10000) begin
                `uvm_warning("PERF_TEST", "Timeout waiting for TX completion")
                return;
            end
        end while (resp == AXI_RESP_OKAY && status[8] == 1'b0); // Wait for TX FIFO empty
    endtask
    
    // Calculate and report throughput
    task calculate_throughput(string test_name);
        real test_time_ns = end_time - start_time;
        real throughput_mbps = (bytes_transmitted * 8.0 * 1000.0) / test_time_ns;
        real transaction_rate = (transactions_completed * 1000000000.0) / test_time_ns;
        
        `uvm_info("PERF_TEST", $sformatf("%s Results:", test_name), UVM_LOW)
        `uvm_info("PERF_TEST", $sformatf("  Test time: %0.1f us", test_time_ns / 1000.0), UVM_LOW)
        `uvm_info("PERF_TEST", $sformatf("  Bytes transmitted: %0d", bytes_transmitted), UVM_LOW)
        `uvm_info("PERF_TEST", $sformatf("  Transactions: %0d", transactions_completed), UVM_LOW)
        `uvm_info("PERF_TEST", $sformatf("  Throughput: %0.2f Mbps", throughput_mbps), UVM_LOW)
        `uvm_info("PERF_TEST", $sformatf("  Transaction rate: %0.1f transactions/sec", transaction_rate), UVM_LOW)
    endtask
    
    // Generate comprehensive performance report
    task generate_performance_report();
        bit [31:0] final_status, error_status;
        bit [1:0] resp;
        
        `uvm_info("PERF_TEST", "=== PERFORMANCE TEST SUMMARY ===", UVM_LOW)
        
        // Final system status
        read_register(ADDR_STATUS_REG, final_status, resp);
        read_register(ADDR_ERROR_STATUS, error_status, resp);
        
        `uvm_info("PERF_TEST", $sformatf("Final system status: 0x%08h", final_status), UVM_LOW)
        `uvm_info("PERF_TEST", $sformatf("Final error status: 0x%08h", error_status), UVM_LOW)
        
        if (error_status != 0) begin
            `uvm_warning("PERF_TEST", "Errors detected during performance test")
        end else begin
            `uvm_info("PERF_TEST", "Performance test completed without errors", UVM_LOW)
        end
        
        `uvm_info("PERF_TEST", "================================", UVM_LOW)
    endtask

endclass

`endif // PERFORMANCE_TEST_SEQUENCE_SV
