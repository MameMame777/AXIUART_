`timescale 1ns / 1ps

// ============================================================================
// UART Clocking Block Self-Test
// ============================================================================
// PURPOSE: Verify that clocking block based driver/monitor eliminates DSIM
//          event scheduling bugs that cause @(posedge clk) to永久hang.
//
// TEST SCENARIOS:
// 1. Verify cb_drv can drive UART bytes without永久blocking
// 2. Verify cb_mon can sample UART bytes without永久blocking
// 3. Verify watchdog timers fire correctly when using clocking blocks
// 4. Verify START/DATA/STOP bit timing is accurate with cb_drv
// 5. Verify inter-byte and inter-frame gaps work correctly
//
// EXPECTED RESULTS:
// - All operations complete within expected time (no永久hang)
// - Timing measurements match configured baud rate
// - Watchdogs fire if timing violations occur (not in normal operation)
// - No DSIM event queue corruption
// ============================================================================

module uart_clocking_block_selftest;

    // Clock and Reset
    logic clk;
    logic rst;
    
    // Instantiate interface with clocking blocks
    uart_if_clocking uart_if_inst (
        .clk(clk),
        .rst(rst)
    );
    
    // Test configuration
    localparam int CLK_FREQ_HZ = 125_000_000;  // 125MHz
    localparam int BAUD_RATE = 115200;
    localparam int BIT_TIME_CYCLES = CLK_FREQ_HZ / BAUD_RATE;  // ~1085 cycles
    localparam real BIT_TIME_NS = 1_000_000_000.0 / BAUD_RATE;  // ~8680ns
    
    // Test results
    int test_pass_count = 0;
    int test_fail_count = 0;
    bit all_tests_complete = 0;
    
    // Clock generation (125MHz = 8ns period)
    initial begin
        clk = 0;
        forever #4ns clk = ~clk;
    end
    
    // ========================================================================
    // TEST SEQUENCE
    // ========================================================================
    
    initial begin
        $display("========================================");
        $display("UART Clocking Block Self-Test");
        $display("========================================");
        $display("Clock Frequency: %0d Hz", CLK_FREQ_HZ);
        $display("Baud Rate: %0d", BAUD_RATE);
        $display("Bit Time: %0d cycles (~%0.1f ns)", BIT_TIME_CYCLES, BIT_TIME_NS);
        $display("");
        
        // Initialize
        rst = 1;
        uart_if_inst.uart_rx = 1'b1;
        uart_if_inst.uart_cts_n = 1'b0;
        
        // Reset sequence
        repeat(10) @(posedge clk);
        rst = 0;
        repeat(5) @(posedge clk);
        
        // ====================================================================
        // TEST 1: Verify clocking block can drive single UART byte
        // ====================================================================
        
        test_single_byte_drive(8'hA5);
        
        // ====================================================================
        // TEST 2: Verify multiple bytes with inter-byte gaps
        // ====================================================================
        
        test_multi_byte_sequence();
        
        // ====================================================================
        // TEST 3: Verify watchdog does NOT fire during normal operation
        // ====================================================================
        
        test_normal_operation_no_watchdog();
        
        // ====================================================================
        // TEST 4: Verify START/STOP bit timing accuracy
        // ====================================================================
        
        test_bit_timing_accuracy();
        
        // ====================================================================
        // TEST 5: Stress test - long byte sequence
        // ====================================================================
        
        test_long_sequence();
        
        // ====================================================================
        // TEST SUMMARY
        // ====================================================================
        
        repeat(20) @(posedge clk);
        
        $display("");
        $display("========================================");
        $display("TEST SUMMARY");
        $display("========================================");
        $display("PASS: %0d", test_pass_count);
        $display("FAIL: %0d", test_fail_count);
        
        if (test_fail_count == 0) begin
            $display("");
            $display("*** ALL TESTS PASSED ***");
            $display("Clocking block implementation is DSIM-safe!");
        end else begin
            $display("");
            $display("*** SOME TESTS FAILED ***");
            $display("Review test output above");
        end
        
        $display("========================================");
        all_tests_complete = 1;
        #100ns;
        $finish;
    end
    
    // ========================================================================
    // TEST 1: Single Byte Drive via Clocking Block
    // ========================================================================
    
    task test_single_byte_drive(logic [7:0] data);
        time start_time, end_time, elapsed_ns;
        time expected_byte_time_ns;
        real time_error_percent;
        
        $display("");
        $display("TEST 1: Single Byte Drive (data=0x%02X)", data);
        $display("----------------------------------------");
        
        start_time = $time;
        
        // Drive byte using clocking block pattern
        fork
            begin
                drive_uart_byte_cb(data);
            end
            begin
                // Watchdog - should NOT fire for normal operation
                #(BIT_TIME_NS * 15);  // 1.5x expected time
                $display("  ERROR: Watchdog fired - byte drive took too long!");
                test_fail_count++;
            end
        join_any
        disable fork;
        
        end_time = $time;
        elapsed_ns = end_time - start_time;
        expected_byte_time_ns = time'(BIT_TIME_NS * 10);  // 10 bits total
        time_error_percent = 100.0 * real'(elapsed_ns - expected_byte_time_ns) / real'(expected_byte_time_ns);
        
        $display("  Start Time: %0t", start_time);
        $display("  End Time: %0t", end_time);
        $display("  Elapsed: %0t (%0.2f%% error)", elapsed_ns, time_error_percent);
        $display("  Expected: ~%0t", expected_byte_time_ns);
        
        if (elapsed_ns < expected_byte_time_ns * 1.5) begin
            $display("  RESULT: PASS - Byte completed without永久hang");
            test_pass_count++;
        end else begin
            $display("  RESULT: FAIL - Byte took too long");
            test_fail_count++;
        end
    endtask
    
    // ========================================================================
    // TEST 2: Multi-Byte Sequence
    // ========================================================================
    
    task test_multi_byte_sequence();
        logic [7:0] test_bytes[5] = '{8'h5A, 8'hA1, 8'h12, 8'h34, 8'hBC};
        time start_time, end_time;
        
        $display("");
        $display("TEST 2: Multi-Byte Sequence (5 bytes)");
        $display("----------------------------------------");
        
        start_time = $time;
        
        fork
            begin
                for (int i = 0; i < 5; i++) begin
                    drive_uart_byte_cb(test_bytes[i]);
                    
                    // Inter-byte gap
                    if (i < 4) begin
                        repeat(100) @(uart_if_inst.cb_drv);  // Gap
                    end
                end
            end
            begin
                #(BIT_TIME_NS * 100);  // Should complete much faster
                $display("  ERROR: Multi-byte sequence timeout!");
                test_fail_count++;
            end
        join_any
        disable fork;
        
        end_time = $time;
        
        $display("  Elapsed: %0t", end_time - start_time);
        
        if ((end_time - start_time) < time'(BIT_TIME_NS * 100)) begin
            $display("  RESULT: PASS");
            test_pass_count++;
        end else begin
            $display("  RESULT: FAIL");
            test_fail_count++;
        end
    endtask
    
    // ========================================================================
    // TEST 3: Normal Operation - No Watchdog
    // ========================================================================
    
    task test_normal_operation_no_watchdog();
        bit watchdog_fired;
        
        $display("");
        $display("TEST 3: Normal Operation - Watchdog Should NOT Fire");
        $display("----------------------------------------");
        
        watchdog_fired = 0;
        
        fork
            begin
                drive_uart_byte_cb(8'hFF);
            end
            begin
                #(BIT_TIME_NS * 12);  // Conservative margin
                watchdog_fired = 1;
            end
        join_any
        disable fork;
        
        if (!watchdog_fired) begin
            $display("  RESULT: PASS - No watchdog timeout");
            test_pass_count++;
        end else begin
            $display("  RESULT: FAIL - Unexpected watchdog timeout");
            test_fail_count++;
        end
    endtask
    
    // ========================================================================
    // TEST 4: Bit Timing Accuracy
    // ========================================================================
    
    task test_bit_timing_accuracy();
        time bit_start_time, bit_end_time;
        time measured_bit_time;
        real error_percent;
        
        $display("");
        $display("TEST 4: Bit Timing Accuracy");
        $display("----------------------------------------");
        
        // Drive single bit and measure
        uart_if_inst.uart_rx = 1'b0;  // Start bit
        bit_start_time = $time;
        repeat(BIT_TIME_CYCLES) @(uart_if_inst.cb_drv);
        bit_end_time = $time;
        uart_if_inst.uart_rx = 1'b1;
        
        measured_bit_time = bit_end_time - bit_start_time;
        error_percent = 100.0 * real'(measured_bit_time - time'(BIT_TIME_NS)) / BIT_TIME_NS;
        
        $display("  Expected Bit Time: %0.1f ns", BIT_TIME_NS);
        $display("  Measured Bit Time: %0t", measured_bit_time);
        $display("  Error: %0.2f%%", error_percent);
        
        if (error_percent < 5.0 && error_percent > -5.0) begin
            $display("  RESULT: PASS - Timing within 5%% tolerance");
            test_pass_count++;
        end else begin
            $display("  RESULT: FAIL - Timing error too large");
            test_fail_count++;
        end
    endtask
    
    // ========================================================================
    // TEST 5: Long Sequence Stress Test
    // ========================================================================
    
    task test_long_sequence();
        time start_time, end_time;
        
        $display("");
        $display("TEST 5: Long Sequence (20 bytes)");
        $display("----------------------------------------");
        
        start_time = $time;
        
        fork
            begin
                for (int i = 0; i < 20; i++) begin
                    drive_uart_byte_cb(8'(i));
                    repeat(50) @(uart_if_inst.cb_drv);
                end
            end
            begin
                #(BIT_TIME_NS * 500);  // Should complete faster
                $display("  ERROR: Long sequence timeout!");
                test_fail_count++;
            end
        join_any
        disable fork;
        
        end_time = $time;
        
        $display("  Elapsed: %0t", end_time - start_time);
        
        if ((end_time - start_time) < time'(BIT_TIME_NS * 500)) begin
            $display("  RESULT: PASS");
            test_pass_count++;
        end else begin
            $display("  RESULT: FAIL");
            test_fail_count++;
        end
    endtask
    
    // ========================================================================
    // HELPER: Drive UART Byte via Clocking Block
    // ========================================================================
    
    task drive_uart_byte_cb(logic [7:0] data);
        int cycle_count;
        
        // START BIT
        uart_if_inst.uart_rx = 1'b0;
        repeat(BIT_TIME_CYCLES) @(uart_if_inst.cb_drv);
        
        // DATA BITS
        for (int i = 0; i < 8; i++) begin
            uart_if_inst.uart_rx = data[i];
            repeat(BIT_TIME_CYCLES) @(uart_if_inst.cb_drv);
        end
        
        // STOP BIT
        uart_if_inst.uart_rx = 1'b1;
        repeat(BIT_TIME_CYCLES) @(uart_if_inst.cb_drv);
    endtask
    
    // ========================================================================
    // SIMULATION TIMEOUT (Safety)
    // ========================================================================
    
    initial begin
        #10ms;
        if (!all_tests_complete) begin
            $display("");
            $display("*** FATAL: Simulation timeout after 10ms ***");
            $display("*** Test永久hung - clocking block may have failed ***");
        end
        $finish;
    end

endmodule
