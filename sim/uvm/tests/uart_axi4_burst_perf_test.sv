`timescale 1ns / 1ps

`include "uvm_macros.svh"
import uvm_pkg::*;
import uart_axi4_test_pkg::*;

// Performance and Burst Testing for UART-AXI4 Bridge
class uart_axi4_burst_perf_test extends enhanced_uart_axi4_base_test;
    
    `uvm_component_utils(uart_axi4_burst_perf_test)
    
    function new(string name = "uart_axi4_burst_perf_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        configure_test_specific_reporting();
        
        // Configure for performance testing
        uvm_config_db#(int)::set(this, "*", "recording_detail", UVM_MEDIUM);
        
        // Reduce idle time for maximum throughput testing
        cfg.min_idle_cycles = 1;
        cfg.max_idle_cycles = 3;
        
        // Optimize AXI timing
        cfg.min_axi_response_delay = 1;
        cfg.max_axi_response_delay = 2;
        
        uvm_config_db#(uart_axi4_env_config)::set(this, "*", "cfg", cfg);
        
        `uvm_info("PERF_TEST", "Performance test configured", UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        uart_axi4_performance_sequence perf_seq;
        uart_axi4_stress_sequence stress_seq;
        
        phase.raise_objection(this, "Starting performance test");
        
        `uvm_info("PERF_TEST", "=== Starting Performance Test ===", UVM_LOW)
        
        // Wait for reset to complete
        wait (uart_axi4_tb_top.dut.rst_n == 1'b1);
        repeat (10) @(posedge uart_axi4_tb_top.dut.clk);
        
        // Run performance measurement sequence
        `uvm_info("PERF_TEST", "Running performance measurement sequence", UVM_MEDIUM)
        perf_seq = uart_axi4_performance_sequence::type_id::create("perf_seq");
        perf_seq.burst_length = 100;
        perf_seq.back_to_back_count = 50;
        perf_seq.target_throughput_mbps = 0.8; // 80% of theoretical max
        perf_seq.start(env.uart_agt.sequencer);
        
        // Wait between major test phases
        repeat (200) @(posedge uart_axi4_tb_top.dut.clk);
        
        // Run stress test sequence
        `uvm_info("PERF_TEST", "Running stress test sequence", UVM_MEDIUM)
        stress_seq = uart_axi4_stress_sequence::type_id::create("stress_seq");
        stress_seq.stress_duration_cycles = 20000;
        stress_seq.max_concurrent_transactions = 3;
        
        // Run stress test with fork to allow early termination
        fork
            stress_seq.start(env.uart_agt.sequencer);
            begin
                // Monitor for critical errors during stress test
                repeat (25000) begin
                    @(posedge uart_axi4_tb_top.dut.clk);
                    if (env.scoreboard.critical_error_count > 5) begin
                        `uvm_error("PERF_TEST", "Too many critical errors during stress test")
                        break;
                    end
                end
            end
        join_any
        disable fork;
        
        // Final settling time
        repeat (100) @(posedge uart_axi4_tb_top.dut.clk);
        
        `uvm_info("PERF_TEST", "=== Performance Test Completed ===", UVM_LOW)
        
        phase.drop_objection(this, "Performance test completed");
    endtask
    
    virtual function void final_phase(uvm_phase phase);
        real actual_throughput_mbps;
        super.final_phase(phase);
        
        // Calculate performance metrics
        if (env.scoreboard.total_test_time > 0) begin
            actual_throughput_mbps = (env.scoreboard.total_bytes_transferred * 8.0) / 
                                   (env.scoreboard.total_test_time / 1000000.0); // Convert to Mbps
        end
        
        // Print performance summary
        `uvm_info("PERF_TEST", "=== PERFORMANCE TEST SUMMARY ===", UVM_LOW)
        `uvm_info("PERF_TEST", $sformatf("Total Transactions: %0d", env.scoreboard.transaction_count), UVM_LOW)
        `uvm_info("PERF_TEST", $sformatf("Total Bytes Transferred: %0d", env.scoreboard.total_bytes_transferred), UVM_LOW)
        `uvm_info("PERF_TEST", $sformatf("Total Test Time: %.2f ms", env.scoreboard.total_test_time / 1000000.0), UVM_LOW)
        `uvm_info("PERF_TEST", $sformatf("Actual Throughput: %.3f Mbps", actual_throughput_mbps), UVM_LOW)
        `uvm_info("PERF_TEST", $sformatf("Average Latency: %.2f ns", env.scoreboard.average_latency_ns), UVM_LOW)
        `uvm_info("PERF_TEST", $sformatf("Peak Latency: %.2f ns", env.scoreboard.peak_latency_ns), UVM_LOW)
        
        // Performance criteria check
        if (actual_throughput_mbps >= 0.5 && env.scoreboard.critical_error_count == 0) begin
            `uvm_info("PERF_TEST", "*** PERFORMANCE TEST PASSED ***", UVM_LOW)
        end else begin
            if (actual_throughput_mbps < 0.5) begin
                `uvm_error("PERF_TEST", $sformatf("Throughput too low: %.3f Mbps < 0.5 Mbps", actual_throughput_mbps))
            end
            if (env.scoreboard.critical_error_count > 0) begin
                `uvm_error("PERF_TEST", $sformatf("Critical errors detected: %0d", env.scoreboard.critical_error_count))
            end
            `uvm_error("PERF_TEST", "*** PERFORMANCE TEST FAILED ***")
        end
    endfunction
    
endclass

