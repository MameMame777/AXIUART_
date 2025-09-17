`timescale 1ns / 1ps

// Performance Test Sequence for UART-AXI4 Bridge Testing
class uart_axi4_performance_sequence extends uvm_sequence #(uart_frame_transaction);
    
    `uvm_object_utils(uart_axi4_performance_sequence)
    
    // Performance test parameters
    int burst_length = 50;
    int back_to_back_count = 20;
    real target_throughput_mbps = 1.0; // Target throughput in Mbps
    
    function new(string name = "uart_axi4_performance_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        `uvm_info("PERF_SEQ", "Starting performance test sequence", UVM_LOW)
        
        fork
            burst_write_test();
            burst_read_test();
            back_to_back_transaction_test();
            throughput_measurement_test();
        join
        
        `uvm_info("PERF_SEQ", "Performance test sequence completed", UVM_LOW)
    endtask
    
    // Burst write performance test
    virtual task burst_write_test();
        uart_frame_transaction req;
        realtime start_time, end_time;
        real elapsed_ms, throughput_mbps;
        int total_bytes = 0;
        
        `uvm_info("PERF_SEQ", $sformatf("Starting burst write test with %0d transactions", burst_length), UVM_MEDIUM)
        
        start_time = $realtime;
        
        for (int i = 0; i < burst_length; i++) begin
            `uvm_do_with(req, {
                cmd == 8'h40; // 4-byte write for maximum throughput
                addr == 32'h10000 + (i * 4);
                data.size() == 4;
                data[0] == i[7:0];
                data[1] == i[15:8];
                data[2] == i[23:16];
                data[3] == i[31:24];
            })
            
            total_bytes += 4;
        end
        
        end_time = $realtime;
        elapsed_ms = (end_time - start_time) / 1000000.0; // Convert to ms
        throughput_mbps = (total_bytes * 8.0) / (elapsed_ms * 1000.0); // Mbps
        
        `uvm_info("PERF_SEQ", $sformatf("Burst write completed: %0d bytes in %.2f ms = %.2f Mbps", 
                  total_bytes, elapsed_ms, throughput_mbps), UVM_LOW)
    endtask
    
    // Burst read performance test
    virtual task burst_read_test();
        uart_frame_transaction req;
        realtime start_time, end_time;
        real elapsed_ms, throughput_mbps;
        int total_bytes = 0;
        
        `uvm_info("PERF_SEQ", $sformatf("Starting burst read test with %0d transactions", burst_length), UVM_MEDIUM)
        
        start_time = $realtime;
        
        for (int i = 0; i < burst_length; i++) begin
            `uvm_do_with(req, {
                cmd == 8'hC0; // 4-byte read for maximum throughput
                addr == 32'h10000 + (i * 4);
            })
            
            total_bytes += 4;
        end
        
        end_time = $realtime;
        elapsed_ms = (end_time - start_time) / 1000000.0;
        throughput_mbps = (total_bytes * 8.0) / (elapsed_ms * 1000.0);
        
        `uvm_info("PERF_SEQ", $sformatf("Burst read completed: %0d bytes in %.2f ms = %.2f Mbps", 
                  total_bytes, elapsed_ms, throughput_mbps), UVM_LOW)
    endtask
    
    // Back-to-back transaction test
    virtual task back_to_back_transaction_test();
        uart_frame_transaction req;
        realtime start_time, end_time;
        real average_latency_ns;
        
        `uvm_info("PERF_SEQ", $sformatf("Starting back-to-back transaction test with %0d transactions", 
                  back_to_back_count), UVM_MEDIUM)
        
        start_time = $realtime;
        
        for (int i = 0; i < back_to_back_count; i++) begin
            // Alternate between writes and reads for realistic traffic
            if (i % 2 == 0) begin
                `uvm_do_with(req, {
                    cmd == 8'h20; // 2-byte write
                    addr == 32'h20000 + (i * 2);
                    data.size() == 2;
                    data[0] == i[7:0];
                    data[1] == i[15:8];
                })
            end else begin
                `uvm_do_with(req, {
                    cmd == 8'hA0; // 2-byte read
                    addr == 32'h20000 + ((i-1) * 2);
                })
            end
        end
        
        end_time = $realtime;
        average_latency_ns = (end_time - start_time) / back_to_back_count;
        
        `uvm_info("PERF_SEQ", $sformatf("Back-to-back test completed: Average latency = %.2f ns", 
                  average_latency_ns), UVM_LOW)
    endtask
    
    // Throughput measurement with detailed statistics
    virtual task throughput_measurement_test();
        uart_frame_transaction req;
        realtime transaction_times[];
        realtime start_time, end_time;
        real min_latency, max_latency, avg_latency, total_latency;
        int measurement_count = 25;
        
        `uvm_info("PERF_SEQ", $sformatf("Starting throughput measurement with %0d samples", 
                  measurement_count), UVM_MEDIUM)
        
        transaction_times = new[measurement_count];
        
        for (int i = 0; i < measurement_count; i++) begin
            start_time = $realtime;
            
            `uvm_do_with(req, {
                cmd == 8'h40; // 4-byte write
                addr == 32'h30000 + (i * 4);
                data.size() == 4;
                foreach(data[j]) data[j] == (i + j) & 8'hFF;
            })
            
            end_time = $realtime;
            transaction_times[i] = end_time - start_time;
        end
        
        // Calculate statistics
        min_latency = transaction_times[0];
        max_latency = transaction_times[0];
        total_latency = 0;
        
        foreach (transaction_times[i]) begin
            total_latency += transaction_times[i];
            if (transaction_times[i] < min_latency) min_latency = transaction_times[i];
            if (transaction_times[i] > max_latency) max_latency = transaction_times[i];
        end
        
        avg_latency = total_latency / measurement_count;
        
        `uvm_info("PERF_SEQ", $sformatf("Latency statistics: Min=%.2f ns, Max=%.2f ns, Avg=%.2f ns", 
                  min_latency, max_latency, avg_latency), UVM_LOW)
    endtask
    
endclass

// Stress Test Sequence
class uart_axi4_stress_sequence extends uvm_sequence #(uart_frame_transaction);
    
    `uvm_object_utils(uart_axi4_stress_sequence)
    
    int stress_duration_cycles = 10000;
    int max_concurrent_transactions = 5;
    
    function new(string name = "uart_axi4_stress_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        `uvm_info("STRESS_SEQ", $sformatf("Starting stress test for %0d cycles", stress_duration_cycles), UVM_LOW)
        
        fork
            continuous_write_stress();
            continuous_read_stress();
            mixed_pattern_stress();
            error_recovery_stress();
        join_any
        
        `uvm_info("STRESS_SEQ", "Stress test sequence completed", UVM_LOW)
    endtask
    
    virtual task continuous_write_stress();
        uart_frame_transaction req;
        int transaction_count = 0;
        realtime start_time = $realtime;
        
        while (($realtime - start_time) < (stress_duration_cycles * 20)) begin // 20ns per cycle estimate
            `uvm_do_with(req, {
                cmd inside {8'h10, 8'h20, 8'h40}; // Random write sizes
                addr inside {[32'h40000:32'h40FFF]}; // 4KB region
                if (cmd == 8'h10) data.size() == 1;
                else if (cmd == 8'h20) data.size() == 2;
                else data.size() == 4;
                foreach(data[i]) data[i] == (transaction_count + i) & 8'hFF;
            })
            
            transaction_count++;
            
            // Random delay between transactions
            #($urandom_range(100, 1000));
        end
        
        `uvm_info("STRESS_SEQ", $sformatf("Continuous write stress completed: %0d transactions", 
                  transaction_count), UVM_MEDIUM)
    endtask
    
    virtual task continuous_read_stress();
        uart_frame_transaction req;
        int transaction_count = 0;
        realtime start_time = $realtime;
        
        while (($realtime - start_time) < (stress_duration_cycles * 20)) begin
            `uvm_do_with(req, {
                cmd inside {8'h90, 8'hA0, 8'hC0}; // Random read sizes
                addr inside {[32'h40000:32'h40FFF]}; // Same region as writes
            })
            
            transaction_count++;
            
            // Random delay
            #($urandom_range(50, 500));
        end
        
        `uvm_info("STRESS_SEQ", $sformatf("Continuous read stress completed: %0d transactions", 
                  transaction_count), UVM_MEDIUM)
    endtask
    
    virtual task mixed_pattern_stress();
        uart_frame_transaction req;
        int pattern_count = 0;
        realtime start_time = $realtime;
        
        while (($realtime - start_time) < (stress_duration_cycles * 20)) begin
            // Write-read-write-read pattern
            for (int i = 0; i < 4 && (($realtime - start_time) < (stress_duration_cycles * 20)); i++) begin
                `uvm_do_with(req, {
                    cmd == (i % 2 == 0) ? 8'h20 : 8'hA0; // Alternate write/read
                    addr == 32'h50000 + (pattern_count * 8) + (i * 2);
                    if (!cmd[7]) { // Write
                        data.size() == 2;
                        data[0] == pattern_count[7:0];
                        data[1] == pattern_count[15:8];
                    }
                })
            end
            
            pattern_count++;
            
            // Brief pause between patterns
            #($urandom_range(200, 800));
        end
        
        `uvm_info("STRESS_SEQ", $sformatf("Mixed pattern stress completed: %0d patterns", 
                  pattern_count), UVM_MEDIUM)
    endtask
    
    virtual task error_recovery_stress();
        uart_frame_transaction req;
        int error_count = 0;
        realtime start_time = $realtime;
        
        while (($realtime - start_time) < (stress_duration_cycles * 20)) begin
            // Inject periodic errors
            if ($urandom_range(1, 10) == 1) begin // 10% error rate
                `uvm_do_with(req, {
                    cmd inside {8'h10, 8'h90}; // Simple transactions
                    addr == 32'h60000 + (error_count * 4);
                    if (!cmd[7]) data.size() == 1;
                    force_crc_error == 1; // Inject CRC error
                })
                error_count++;
            end else begin
                // Normal transaction
                `uvm_do_with(req, {
                    cmd inside {8'h10, 8'h20, 8'h40, 8'h90, 8'hA0, 8'hC0};
                    addr == 32'h60000 + ($urandom % 1024);
                    if (!cmd[7]) {
                        data.size() == (1 << (cmd[6:4] - 1));
                        foreach(data[i]) data[i] == $urandom;
                    }
                })
            end
            
            #($urandom_range(500, 2000));
        end
        
        `uvm_info("STRESS_SEQ", $sformatf("Error recovery stress completed: %0d errors injected", 
                  error_count), UVM_MEDIUM)
    endtask
    
endclass