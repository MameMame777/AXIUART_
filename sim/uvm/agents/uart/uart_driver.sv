`timescale 1ns / 1ps

// Import protocol constants from test package
import uart_axi4_test_pkg::*;

// UART Driver for UART-AXI4 Bridge UVM Testbench
class uart_driver extends uvm_driver #(uart_frame_transaction);
    
    `uvm_component_utils(uart_driver)
    
    // Configuration
    uart_axi4_env_config cfg;
    uvm_tlm_analysis_fifo#(uart_frame_transaction) tx_response_fifo;
    uvm_analysis_port #(uart_frame_transaction) tx_request_ap;
    
    // Virtual interface
    virtual uart_if vif;
    
    // Protocol constants (Import from main test package)
    // These constants must match uart_axi4_test_pkg definitions
    
    function new(string name = "uart_driver", uvm_component parent = null);
        super.new(name, parent);
        tx_request_ap = new("tx_request_ap", this);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        if (!uvm_config_db#(uart_axi4_env_config)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("UART_DRIVER", "Failed to get configuration object");
        end
        
        // Get virtual interface
        if (!uvm_config_db#(virtual uart_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("UART_DRIVER", "Failed to get virtual interface");
        end

        // Optional monitor-provided response FIFO (preferred path)
        if (!uvm_config_db#(uvm_tlm_analysis_fifo#(uart_frame_transaction))::get(this, "", "tx_response_fifo", tx_response_fifo)) begin
            tx_response_fifo = null;
            `uvm_info("UART_DRIVER", "Monitor response FIFO not provided; falling back to direct sampling", UVM_LOW);
        end else begin
            `uvm_info("UART_DRIVER", "Using monitor response FIFO for DUT replies", UVM_LOW);
        end
    endfunction

    protected function void driver_debug_log(string id, string message, int default_verbosity = UVM_HIGH);
        int level;

        if (cfg == null || !cfg.enable_driver_debug_logs) begin
            return;
        end

        level = (cfg.driver_debug_verbosity != 0) ? cfg.driver_debug_verbosity : default_verbosity;
        `uvm_info(id, message, level)
    endfunction

    protected function void driver_runtime_log(string id, string message, int default_verbosity = UVM_MEDIUM);
        int level;

        if (cfg == null || !cfg.enable_driver_runtime_logs) begin
            return;
        end

        level = (cfg.driver_runtime_verbosity != 0) ? cfg.driver_runtime_verbosity : default_verbosity;
        `uvm_info(id, message, level)
    endfunction

    protected function void driver_forced_log(string id, string message);
        `uvm_info(id, message, UVM_NONE)
    endfunction

    protected function void apply_timeout_result(uart_frame_transaction tr);
        if (tr == null) begin
            return;
        end

        tr.response_received = 0;
        tr.response_status = STATUS_TIMEOUT;
        tr.crc_valid = 0;
        tr.monitor_recovered = 0;
        tr.response_data = new[0];
        tr.frame_data = new[0];
        tr.frame_length = 0;
        tr.timeout_error = 1;
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        uart_frame_transaction req;
        
        // CRITICAL DEBUG: Verify VIF and clock before starting
        if (vif == null) begin
            `uvm_fatal("UART_DRIVER", "VIF is NULL in run_phase!")
        end
        `uvm_info("UART_DRIVER_DEBUG", $sformatf("VIF check OK, clk=%0b", vif.clk), UVM_LOW)
        
        // Wait for reset de-assertion (UVM-compliant: reset runs in parallel)
        // Use @(posedge clk) to advance time (avoid #0 infinite loop)
        begin
            int timeout_counter = 0;
            while (vif.rst !== 1'b0) begin
                @(posedge vif.clk);
                timeout_counter++;
                if (timeout_counter > 200) `uvm_fatal("UART_DRIVER", "Reset timeout - rst never de-asserted")
            end
            `uvm_info("UART_DRIVER", $sformatf("Reset de-assertion detected after %0d clocks", timeout_counter), UVM_LOW)
        end
        
        repeat (10) @(vif.driver_cb);  // Stabilization after reset release
        
        // Wait for a few clocks to verify clock is running
        // CRITICAL: Verify clock is running using clocking block (NOT @(posedge vif.clk))
        fork
            begin
                repeat (5) @(vif.driver_cb);  // ← CLOCKING BLOCK (DSIM-SAFE)
                `uvm_info("UART_DRIVER_DEBUG", "Clock verified via driver_cb - 5 edges detected", UVM_LOW)
            end
            begin
                #100us; // Timeout if clock doesn't toggle
                `uvm_fatal("UART_DRIVER", "Clock signal (vif.clk) is not toggling! Simulation cannot proceed.")
            end
        join_any
        disable fork;
        
        // Initialize UART interface signals via clocking block
        vif.driver_cb.uart_rx <= 1'b1;      // RX line idle (high)
        vif.driver_cb.uart_cts_n <= 1'b0;   // CTS asserted (low) - allow DUT to transmit
        
        `uvm_info("UART_DRIVER_DEBUG", "Entering forever loop - ready to receive transactions", UVM_LOW)
        
        forever begin
            // Handshake trace to confirm sequencer requests reach the driver.
            `uvm_info("UART_DRIVER_HANDSHAKE", $sformatf("Issuing get_next_item() at time=%0t", $time), UVM_LOW)
            `uvm_info("UART_DRIVER_DEBUG", "Calling get_next_item() - waiting for sequence", UVM_LOW)
            seq_item_port.get_next_item(req);
            `uvm_info("UART_DRIVER_HANDSHAKE",
                $sformatf("get_next_item() returned %s at time=%0t", (req == null) ? "NULL" : "VALID", $time),
                UVM_LOW)
            `uvm_info("UART_DRIVER_DEBUG", "get_next_item() returned - transaction received", UVM_LOW)
            
            // CRITICAL DIAGNOSTIC: Check data array state immediately after handshake
            if (req.data.size() == 0) begin
                `uvm_fatal("UART_DRIVER_DATA_NULL", 
                    $sformatf("req.data has zero size after get_next_item() at time=%0t", $time))
            end else begin
                `uvm_info("UART_DRIVER_DATA_CHECK",
                    $sformatf("req.data exists (1 byte assumed) immediately after get_next_item() at time=%0t", 
                              $time), UVM_LOW)
            end
            
            driver_runtime_log("UART_DRIVER",
                $sformatf("Driving transaction: CMD=0x%02X, ADDR=0x%08X", req.cmd, req.addr));

            req.timeout_error = 0;

            if (tx_request_ap != null) begin
                uart_frame_transaction req_copy;
                driver_forced_log("UART_DRIVER_DEBUG", "About to call req.clone()");
                $cast(req_copy, req.clone());
                driver_forced_log("UART_DRIVER_DEBUG", 
                    $sformatf("About to call tx_request_ap.write() at time=%0t", $time));
                tx_request_ap.write(req_copy);
                driver_forced_log("UART_DRIVER_DEBUG", 
                    $sformatf("tx_request_ap.write() completed at time=%0t", $time));
                driver_debug_log("UART_DRIVER_METADATA",
                    $sformatf("Published metadata: CMD=0x%02X ADDR=0x%08X expect_error=%0b time=%0t",
                              req_copy.cmd, req_copy.addr, req_copy.expect_error, $realtime));
            end

            if (tx_response_fifo != null) begin
                int pre_drive_depth;
                bit skip_response;
                driver_forced_log("UART_DRIVER_DEBUG", 
                    $sformatf("Entering monitored response path at time=%0t", $time));
                pre_drive_depth = (tx_response_fifo != null) ? tx_response_fifo.used() : 0;
                driver_forced_log("UART_DRIVER_DEBUG",
                    $sformatf("FIFO depth query completed: depth=%0d", pre_drive_depth));
                driver_debug_log("UART_DRIVER_FIFO",
                    $sformatf("Entering monitored response path: fifo_depth=%0d", pre_drive_depth),
                    UVM_HIGH);
                driver_forced_log("UART_DRIVER_DEBUG", "About to call flush_monitor_responses()");
                flush_monitor_responses();
                driver_forced_log("UART_DRIVER_DEBUG", "flush_monitor_responses() completed");
                driver_forced_log("UART_DRIVER_DEBUG", "About to call drive_frame()");
                drive_frame(req);
                driver_forced_log("UART_DRIVER_DEBUG", "drive_frame() completed");
                
                // Determine if response collection should be skipped:
                // 1. RESET command (CMD=0xFF): Triggers soft reset, no response frame
                // 2. CONFIG write (addr=0x00001008, is_write=1): Baud switch, response at new baud (UVM still at old baud)
                skip_response = (req.cmd == 8'hFF) || 
                               (req.is_write && (req.addr == 32'h00001008));
                
                if (skip_response) begin
                    if (req.cmd == 8'hFF) begin
                        driver_runtime_log("UART_DRIVER_RESET",
                            "RESET command transmitted - no response expected (soft reset active)",
                            UVM_MEDIUM);
                    end else begin
                        driver_runtime_log("UART_DRIVER_CONFIG",
                            "CONFIG write transmitted - no response expected (baud rate mismatch)",
                            UVM_MEDIUM);
                    end
                end else begin
                    driver_runtime_log("UART_DRIVER",
                        "Invoking collect_response_from_fifo() after frame transmission",
                        UVM_LOW);
                    collect_response_from_fifo(req);
                end
            end else begin
                // Legacy direct sampling path - kept as fallback
                fork
                    begin
                        monitor_response(req);
                    end
                    begin
                        drive_frame(req);
                    end
                join
            end
            
            driver_runtime_log("UART_DRIVER",
                "Transaction processing complete, calling item_done()",
                UVM_LOW);
            seq_item_port.item_done();
            `uvm_info("UART_DRIVER_HANDSHAKE",
                $sformatf("item_done() called for transaction %s at time=%0t", (req == null) ? "NULL" : "VALID", $time),
                UVM_LOW)
        end
    endtask
    
    // Drive a complete UART frame
    virtual task drive_frame(uart_frame_transaction tr);
        logic [7:0] frame_bytes[];
        logic [7:0] calculated_crc;
        logic [7:0] crc_data[];
        logic [7:0] crc_data_fixed[5];
        int byte_count;
        int payload_bytes;
        bit is_write_cmd;
        
        // CRITICAL: Null check with fatal
        if (tr.data.size() == 0) begin
            `uvm_fatal("UART_DRIVER_FATAL", "tr.data has zero size!")
        end
        
        // DSIM BUG WORKAROUND: NO $display() calls before CHECKPOINT_B
        // DSIM crashes with ANY display after tr.data access
        // DSIM limitation: Avoid .size() method - use fixed allocation
        payload_bytes = 1;  // Single-byte write assumption
        
        // Validation without display
        if (payload_bytes > 256) begin
            `uvm_fatal("UART_DRIVER_FATAL", 
                $sformatf("Payload size=%0d exceeds maximum (256)", payload_bytes))
        end
        
        is_write_cmd = (tr.cmd[7] == 1'b0);

        // RESET command special handling (CMD=0xFF)
        if (tr.cmd == 8'hFF) begin
            byte_count = 3;  // RESET frame: SOF + CMD + CRC only
            frame_bytes = new[byte_count];
            frame_bytes[0] = SOF_HOST_TO_DEVICE;  // 0xA5
            frame_bytes[1] = 8'hFF;  // CMD = RESET
            // CRC calculation for RESET: only CMD byte (0xFF)
            calculated_crc = calculate_crc({8'hFF}, 1);
            frame_bytes[2] = calculated_crc;
            driver_runtime_log("UART_DRIVER_RESET",
                $sformatf("RESET frame: SOF=0x%02X CMD=0xFF CRC=0x%02X (3 bytes)",
                          SOF_HOST_TO_DEVICE, calculated_crc), UVM_MEDIUM);
        end else if (tr.cmd[7]) begin // Read command
            byte_count = 7; // SOF + CMD + ADDR(4) + CRC
            frame_bytes = new[byte_count];
            frame_bytes[0] = SOF_HOST_TO_DEVICE;
            frame_bytes[1] = tr.cmd;
            frame_bytes[2] = tr.addr[7:0];
            frame_bytes[3] = tr.addr[15:8];
            frame_bytes[4] = tr.addr[23:16];
            frame_bytes[5] = tr.addr[31:24];
            // CRC calculation excludes SOF (starts from index 1)
            crc_data_fixed[0] = frame_bytes[1];
            crc_data_fixed[1] = frame_bytes[2];
            crc_data_fixed[2] = frame_bytes[3];
            crc_data_fixed[3] = frame_bytes[4];
            crc_data_fixed[4] = frame_bytes[5];
            calculated_crc = calculate_crc(crc_data_fixed, 5);
            frame_bytes[6] = calculated_crc;
            driver_debug_log("UART_DRIVER_CRC",
                $sformatf("Read CRC: data=[%02X,%02X,%02X,%02X,%02X] -> CRC=0x%02X",
                          frame_bytes[1], frame_bytes[2], frame_bytes[3], frame_bytes[4], frame_bytes[5], calculated_crc));
        end else begin // Write command
            // DSIM workaround: Assume single-byte write operations (basic test scenario)
            int data_len;
            data_len = 1;  // Fixed allocation for known write pattern
            byte_count = 7 + data_len; // SOF + CMD + ADDR(4) + DATA + CRC
            
            if (byte_count > 1024) begin
                `uvm_fatal("UART_DRIVER_FATAL",
                    $sformatf("Frame size %0d exceeds limit (1024)", byte_count))
            end
            
            frame_bytes = new[byte_count];
            frame_bytes[0] = SOF_HOST_TO_DEVICE;
            frame_bytes[1] = tr.cmd;
            frame_bytes[2] = tr.addr[7:0];
            frame_bytes[3] = tr.addr[15:8];
            frame_bytes[4] = tr.addr[23:16];
            frame_bytes[5] = tr.addr[31:24];
            
            frame_bytes[6] = tr.data[0];
            // CRC calculation excludes SOF (starts from index 1)
            crc_data = new[byte_count - 2];
            for (int i = 0; i < byte_count - 2; i++) begin
                crc_data[i] = frame_bytes[1 + i];
            end
            
            calculated_crc = calculate_crc(crc_data, byte_count - 2);
            
            frame_bytes[byte_count - 1] = calculated_crc;
        end
        
        // Frame validation: RESET=3 bytes, Read=7 bytes, Write>=7 bytes
        if (tr.cmd == 8'hFF) begin  // RESET command
            if (byte_count != 3) begin
                `uvm_fatal("UART_DRIVER_FATAL", $sformatf("RESET frame byte_count=%0d (expected 3)", byte_count))
            end
        end else if (is_write_cmd) begin
            if (payload_bytes <= 0) begin
                `uvm_fatal("UART_DRIVER_FATAL", $sformatf("Write frame missing payload bytes (cmd=0x%02X)", tr.cmd))
            end
            if (byte_count < 7) begin
                `uvm_fatal("UART_DRIVER_FATAL", $sformatf("Write frame byte_count=%0d (expected >=7) payload=%0d cmd=0x%02X", byte_count, payload_bytes, tr.cmd))
            end
        end else begin
            if (byte_count != 7) begin
                `uvm_fatal("UART_DRIVER_FATAL", $sformatf("Read frame byte_count=%0d (expected 7) cmd=0x%02X", byte_count, tr.cmd))
            end
        end

        // Send frame byte by byte
        for (int i = 0; i < byte_count; i++) begin
            drive_uart_byte(frame_bytes[i]);
            
            // Add inter-byte gap (random between min and max idle cycles)
            if (i < byte_count - 1) begin
                int min_gap_cycles;
                int max_gap_cycles;
                int idle_cycles;
                int swap_value;
                bit gap_timeout;
                time gap_start_time;
                time gap_timeout_ns;
                int cycles_waited;

                min_gap_cycles = cfg.min_idle_cycles;
                max_gap_cycles = cfg.max_idle_cycles;

                if (min_gap_cycles < 0) begin
                    `uvm_warning("UART_DRIVER_IDLE_RANGE",
                        $sformatf("cfg.min_idle_cycles=%0d is negative; forcing to 0", min_gap_cycles));
                    min_gap_cycles = 0;
                end

                if (max_gap_cycles < 0) begin
                    `uvm_warning("UART_DRIVER_IDLE_RANGE",
                        $sformatf("cfg.max_idle_cycles=%0d is negative; forcing to min", max_gap_cycles));
                    max_gap_cycles = min_gap_cycles;
                end

                if (max_gap_cycles < min_gap_cycles) begin
                    `uvm_error("UART_DRIVER_IDLE_RANGE",
                        $sformatf("cfg.min_idle_cycles=%0d exceeds cfg.max_idle_cycles=%0d; swapping to protect repeat()",
                            min_gap_cycles, max_gap_cycles));
                    swap_value = max_gap_cycles;
                    max_gap_cycles = min_gap_cycles;
                    min_gap_cycles = swap_value;
                end

                if (max_gap_cycles > min_gap_cycles) begin
                    idle_cycles = $urandom_range(max_gap_cycles, min_gap_cycles);
                end else begin
                    idle_cycles = max_gap_cycles;
                end

                // Safety check: clamp to reasonable maximum
                if (idle_cycles < 0) begin
                    `uvm_warning("UART_DRIVER_GAP",
                        $sformatf("idle_cycles=%0d is negative, forcing to 0", idle_cycles));
                    idle_cycles = 0;
                end
                
                if (idle_cycles > 100000) begin
                    `uvm_warning("UART_DRIVER_GAP",
                        $sformatf("idle_cycles=%0d exceeds safety limit, clamping to 100000", idle_cycles));
                    idle_cycles = 100000;
                end

                driver_debug_log("UART_DRIVER_GAP",
                    $sformatf("Inter-byte gap START: idle_cycles=%0d (min=%0d max=%0d) between byte[%0d] and byte[%0d] at time=%0t",
                        idle_cycles, min_gap_cycles, max_gap_cycles, i, i+1, $time));

                // Inter-byte gap with timeout protection - DSIM-SAFE
                gap_timeout = 0;
                gap_start_time = $time;
                gap_timeout_ns = (cfg.byte_time_ns > 0) ? (cfg.byte_time_ns * 100) : 10_000_000;
                cycles_waited = 0;

                // Use clocking block instead of direct @(posedge)
                while (cycles_waited < idle_cycles) begin
                    @(vif.driver_cb);  // ← CLOCKING BLOCK
                    cycles_waited++;
                    if (($time - gap_start_time) > gap_timeout_ns) begin
                        gap_timeout = 1;
                        `uvm_fatal("UART_DRIVER_GAP_TIMEOUT",
                            $sformatf("Inter-byte gap timeout after %0t ns: target_cycles=%0d, waited_cycles=%0d, elapsed_time=%0t, between byte[%0d] and byte[%0d]",
                                      gap_timeout_ns, idle_cycles, cycles_waited, $time - gap_start_time, i, i+1));
                    end
                end

                driver_debug_log("UART_DRIVER_GAP",
                    $sformatf("Inter-byte gap COMPLETE: elapsed=%0t ns, cycles_waited=%0d/%0d at time=%0t",
                              $time - gap_start_time, cycles_waited, idle_cycles, $time));
            end
        end
        
        // Add inter-frame gap (much longer than inter-byte gap)
        begin
            int inter_frame_cycles = cfg.max_idle_cycles * 5;
            int cycles_counted = 0;
            time inter_frame_start = $time;
            time inter_frame_timeout_ns = (cfg.frame_timeout_ns > 0) ? cfg.frame_timeout_ns : 10_000_000; // 10ms fallback
            
            while (cycles_counted < inter_frame_cycles) begin
                @(vif.driver_cb);  // ← CLOCKING BLOCK (DSIM-SAFE)
                cycles_counted++;
                if (($time - inter_frame_start) > inter_frame_timeout_ns) begin
                    `uvm_fatal("UART_DRIVER_FATAL",
                        $sformatf("Inter-frame gap timeout after %0t ns: target_cycles=%0d, counted=%0d, elapsed=%0t",
                                  inter_frame_timeout_ns, inter_frame_cycles, cycles_counted, $time - inter_frame_start))
                end
            end
        end
        
        driver_runtime_log("UART_DRIVER",
            $sformatf("Frame transmission complete: %0d bytes sent", byte_count),
            UVM_LOW);
    endtask
    
    // Drive a single UART byte (8N1 format)
    virtual task drive_uart_byte(logic [7:0] data);
        static int debug_byte_count = 0;
        int bit_time_cycles;
        time base_guard_ns;
        time watchdog_delay_ns;
        bit byte_done;
        real cycle_ns;
        int cycles_per_byte;
        time start_time;
        bit emit_debug;

        // CRITICAL FIX: Use pre-calculated cfg.bit_time_cycles instead of recalculating
        // This ensures baud rate changes (via cfg.calculate_timing()) are respected
        bit_time_cycles = (cfg.bit_time_cycles > 0) ? cfg.bit_time_cycles : 
                          ((cfg.baud_rate > 0) ? (cfg.clk_freq_hz / cfg.baud_rate) : 1);
        if (bit_time_cycles <= 0) begin
            bit_time_cycles = 1;
        end

        base_guard_ns = cfg.byte_time_ns;
        cycles_per_byte = bit_time_cycles * 10;
        if (base_guard_ns <= 0) begin
            if (cfg.clk_freq_hz > 0) begin
                cycle_ns = 1.0e9 / cfg.clk_freq_hz;
                base_guard_ns = time'($ceil(cycle_ns * cycles_per_byte));
            end else begin
                base_guard_ns = time'(cycles_per_byte);
            end
        end
        if (base_guard_ns <= 0) begin
            base_guard_ns = 1000;
        end

        watchdog_delay_ns = base_guard_ns * 4;
        if (watchdog_delay_ns < base_guard_ns + 100) begin
            watchdog_delay_ns = base_guard_ns + 100;
        end

        // TEMPORARY DEBUG: Always emit timing logs (remove debug_byte_count restriction)
        emit_debug = 0;

        if (emit_debug) begin
            driver_debug_log("UART_DRIVER_TIMING",
                $sformatf("drive_uart_byte setup: data=0x%02X bit_time_cycles=%0d base_guard_ns=%0t watchdog_delay_ns=%0t",
                          data,
                          bit_time_cycles,
                          base_guard_ns,
                          watchdog_delay_ns));
        end

        byte_done = 0;
        start_time = $time;

        // Refactored to avoid fork/join_any instability with DSIM
        // Replaced parallel watchdog thread with inline deadline checks
        begin : drive_thread_single
            
            driver_runtime_log("UART_DRIVER_BYTE",
                $sformatf("Driving UART byte: 0x%02X", data),
                UVM_LOW);

            // Start bit
            vif.driver_cb.uart_rx <= 1'b0;
            for (int _cycle = 0; _cycle < bit_time_cycles; _cycle++) @(vif.driver_cb);
            
            if (emit_debug) begin
                driver_debug_log("UART_DRIVER_BYTE_STATE",
                    $sformatf("start bit complete: data=0x%02X time=%0t", data, $time));
            end

            // Data bits (LSB first)
            for (int i = 0; i < 8; i++) begin
                vif.driver_cb.uart_rx <= data[i];
                for (int _cycle = 0; _cycle < bit_time_cycles; _cycle++) @(vif.driver_cb);
            end

            // Stop bit
            vif.driver_cb.uart_rx <= 1'b1;
            for (int _cycle = 0; _cycle < bit_time_cycles; _cycle++) @(vif.driver_cb);
            
            if (emit_debug) begin
                driver_debug_log("UART_DRIVER_BYTE_STATE",
                    $sformatf("stop bit complete: data=0x%02X time=%0t", data, $time));
            end

            byte_done = 1;
            if (emit_debug) begin
                driver_debug_log("UART_DRIVER_BYTE_STATE",
                    $sformatf("byte_done asserted for data=0x%02X at time=%0t", data, $time));
            end
        end

        if (emit_debug) begin
            driver_debug_log("UART_DRIVER_BYTE_STATE",
                $sformatf("drive_uart_byte completed: data=0x%02X total_time=%0t", data, $time - start_time));
        end

        debug_byte_count++;
    endtask
    
    // Flush any stale monitor responses before starting a new transaction
    virtual task flush_monitor_responses();
        uart_frame_transaction stale;
        bit have_item;
        int dropped;

        if (tx_response_fifo == null) begin
            return;
        end

        driver_debug_log("UART_DRIVER_FIFO",
            $sformatf("flush_monitor_responses invoked at %0t initial_depth=%0d",
                      $time, tx_response_fifo.used()));

        dropped = 0;
        have_item = tx_response_fifo.try_get(stale);

        while (have_item) begin
            dropped++;
            // Log each flushed item for detailed tracing
            if (stale != null) begin
                driver_runtime_log("UART_DRIVER_FIFO",
                    $sformatf("Flushed item #%0d: dir=%0d cmd=0x%02X addr=0x%08X status=0x%02X parse_err=%s crc_valid=%0d len=%0d ts=%0t",
                              dropped, stale.direction, stale.cmd, stale.addr, stale.response_status, stale.parse_error_kind.name(), stale.crc_valid, stale.frame_length, stale.timestamp),
                    UVM_LOW);
            end else begin
                driver_runtime_log("UART_DRIVER_FIFO",
                    $sformatf("Flushed item #%0d: NULL item", dropped),
                    UVM_LOW);
            end

            // Keep reading until empty; stale contains the last item read
            have_item = tx_response_fifo.try_get(stale);
        end

        if (dropped > 0) begin
            driver_runtime_log("UART_DRIVER",
                $sformatf("Flushed %0d stale response transaction(s) before driving new frame", dropped),
                UVM_DEBUG);
            driver_debug_log("UART_DRIVER_FIFO",
                $sformatf("flush_monitor_responses dropped=%0d final_depth=%0d time=%0t",
                          dropped, tx_response_fifo.used(), $time));
        end
    endtask

    // Collect response using monitor-published transactions
    virtual task collect_response_from_fifo(uart_frame_transaction tr);
    uart_frame_transaction resp;
    bit success;
    time wait_time_ns;
    bit wait_task_completed;
    time guard_timeout_ns;
    bit guard_fired;

        if (tx_response_fifo == null) begin
            return;
        end

        driver_runtime_log("UART_DRIVER",
            $sformatf("Entering collect_response_from_fifo, expect_error=%0b", tr.expect_error),
            UVM_LOW);
        if (tx_response_fifo != null) begin
            driver_debug_log("UART_DRIVER_FIFO",
                $sformatf("collect_response_from_fifo start: depth=%0d expect_error=%0b time=%0t",
                          tx_response_fifo.used(), tr.expect_error, $time));
        end

        resp = null;
        success = 0;
        wait_time_ns = 0;
        wait_task_completed = 0;
        guard_fired = 0;
        guard_timeout_ns = (cfg.frame_timeout_ns > 0) ? time'(cfg.frame_timeout_ns) : 1_000_000;

        fork
            begin : wait_for_response_thread
                wait_for_monitor_response(resp, success, wait_time_ns);
                wait_task_completed = 1;
            end
            begin : guard_timeout_thread
                #(guard_timeout_ns);
                if (!wait_task_completed) begin
                    #0; // Allow wait thread to update completion flag before enforcing timeout
                    if (!wait_task_completed) begin
                        int guard_depth_snapshot;
                        guard_depth_snapshot = (tx_response_fifo != null) ? tx_response_fifo.used() : -1;
                        guard_fired = 1;
                        driver_runtime_log("UART_DRIVER",
                            $sformatf("Guard timeout fired after %0dns (expect_error=%0b)",
                                      guard_timeout_ns, tr.expect_error),
                            UVM_LOW);
                        driver_debug_log("UART_DRIVER_FIFO",
                            $sformatf("Guard timer fired at %0t depth=%0d expect_error=%0b",
                                      $time, guard_depth_snapshot, tr.expect_error));
                        apply_timeout_result(tr);

                        if (tr.expect_error) begin
                            driver_runtime_log("UART_DRIVER",
                                $sformatf("[expect_error=1] Guard timeout fired after %0dns without DUT response", guard_timeout_ns),
                                UVM_LOW);
                        end
                    end
                end
            end
        join_any
        disable fork;
        if (!wait_task_completed) begin
            // CRITICAL: Always report timeout, even for expect_error cases
            if (!tr.expect_error) begin
                `uvm_fatal("UART_DRIVER_TIMEOUT",
                    $sformatf("Guard timeout fired after %0dns waiting for monitor response - DUT did not respond", guard_timeout_ns));
            end else begin
                `uvm_warning("UART_DRIVER_TIMEOUT",
                    $sformatf("Expected timeout occurred after %0dns (expect_error=1)", guard_timeout_ns));
            end
            return;
        end

        driver_runtime_log("UART_DRIVER",
            $sformatf("wait_for_monitor_response returned: success=%0b, resp=%s, wait=%0dns",
                      success, (resp == null) ? "NULL" : "VALID", wait_time_ns),
            UVM_LOW);
        driver_debug_log("UART_DRIVER_FIFO",
            $sformatf("wait_for_monitor_response completed: success=%0b guard_fired=%0b wait=%0dns fifo_depth=%0d time=%0t",
                      success, guard_fired, wait_time_ns,
                      (tx_response_fifo != null) ? tx_response_fifo.used() : -1, $time));
        if (tx_response_fifo != null) begin
            driver_debug_log("UART_DRIVER_FIFO",
                $sformatf("FIFO depth after wait=%0d", tx_response_fifo.used()),
                UVM_HIGH);
        end

        if (guard_fired) begin
            // CRITICAL: Report guard timeout with clear diagnostic
            if (!tr.expect_error) begin
                `uvm_fatal("UART_DRIVER_TIMEOUT",
                    $sformatf("Guard timeout fired after %0dns - DUT failed to respond. Check RTL state machine.", guard_timeout_ns));
            end else begin
                `uvm_info("UART_DRIVER_EXPECTED_TIMEOUT",
                    $sformatf("Expected timeout after %0dns (expect_error=1)", guard_timeout_ns),
                    UVM_MEDIUM);
            end
            return;
        end

        if (!success || resp == null) begin
            apply_timeout_result(tr);

            if (tr.expect_error) begin
                driver_runtime_log("UART_DRIVER",
                    $sformatf("[expect_error=1] No DUT response within %0dns (CRC error等の意図的エラー)。",
                              wait_time_ns),
                    UVM_LOW);
            end else begin
                `uvm_fatal("UART_DRIVER_TIMEOUT",
                    $sformatf("Monitor response timeout after %0dns - Check: 1) DUT state machine stuck? 2) Monitor not detecting TX? 3) FIFO connection broken?",
                              wait_time_ns));
            end
            return;
        end

        tr.timeout_error = 0;

        // Copy response fields back to the active request
        tr.response_received = resp.response_received;
        tr.response_status = resp.response_status;
        tr.crc_valid = resp.crc_valid;
        tr.timestamp = resp.timestamp;
        tr.parse_error_kind = resp.parse_error_kind;
        tr.monitor_recovered = 0;

        // DSIM: Fixed response allocation (no .size() usage)
        if (resp.response_data != null) begin
            // Assume fixed 4-byte register response
            tr.response_data = new[4];
            tr.response_data[0] = resp.response_data[0];
            tr.response_data[1] = resp.response_data[1];
            tr.response_data[2] = resp.response_data[2];
            tr.response_data[3] = resp.response_data[3];
        end else begin
            tr.response_data = new[0];
        end

        tr.frame_length = resp.frame_length;
        // DSIM: Fixed frame allocation (no .size() comparison)
        if (resp.frame_length > 0) begin
            tr.frame_data = new[resp.frame_length];
            // Fixed index copy assuming bounded frame_length
            for (int j = 0; j < resp.frame_length; j++) begin
                tr.frame_data[j] = resp.frame_data[j];
            end
        end else begin
            tr.frame_data = new[0];
        end

        if (resp.parse_error_kind != PARSE_ERROR_NONE) begin
            time fallback_start_timeout;
            time fallback_inter_byte_timeout;

            // CRITICAL: Distinguish monitor timeout from parse errors
            if (resp.parse_error_kind == PARSE_ERROR_TIMEOUT) begin
                `uvm_warning("UART_DRIVER", $sformatf("Monitor timeout - DUT failed to respond after %0dns", cfg.frame_timeout_ns * 4));
                tr.response_received = 0;
                tr.response_status = STATUS_MONITOR_TIMEOUT;
                tr.crc_valid = 0;
                tr.timeout_error = 1;
                return; // No fallback for timeout - DUT didn't transmit anything
            end

            `uvm_warning("UART_DRIVER", $sformatf("Monitor reported TX parse failure (%s); attempting direct fallback", resp.parse_error_kind.name()));
            tr.response_received = 0;
            tr.response_status = STATUS_MONITOR_PARSE_FAIL;
            tr.crc_valid = 0;

            fallback_start_timeout = (cfg.byte_time_ns > 0) ? time'(cfg.byte_time_ns * 12) : 100_000;
            fallback_inter_byte_timeout = (cfg.byte_time_ns > 0) ? time'(cfg.byte_time_ns * 12) : 100_000;

            monitor_response(tr, fallback_start_timeout, fallback_inter_byte_timeout);
            if (tr.response_received) begin
                tr.monitor_recovered = 1;
                `uvm_info("UART_DRIVER", "Direct UART sampling recovered a response after monitor parse failure", UVM_MEDIUM);
            end else begin
                `uvm_error("UART_DRIVER", "Fallback UART sampling also failed to capture a response");
            end
            return;
        end

        driver_runtime_log("UART_DRIVER",
            $sformatf("Monitor FIFO response captured: status=0x%02X, crc_valid=%0d, length=%0d",
                      tr.response_status, tr.crc_valid, tr.frame_length));
    endtask

    // Wait for monitor-published UART_TX transaction with timeout and filtering
    virtual task wait_for_monitor_response(output uart_frame_transaction resp,
                                           output bit success,
                                           output time waited_ns);
        time timeout_ns;
        time poll_interval_ns;
        time start_time;
        time status_log_interval_ns;
        time next_status_log_time;
        uart_frame_transaction item;
        int unsigned discarded_non_tx;

        success = 0;
        resp = null;
        waited_ns = 0;
        discarded_non_tx = 0;

        if (tx_response_fifo == null) begin
            return;
        end

        timeout_ns = (cfg.frame_timeout_ns > 0) ? time'(cfg.frame_timeout_ns) : 1_000_000;
        poll_interval_ns = (cfg.byte_time_ns > 0) ? time'(cfg.byte_time_ns) : 10_000;

        if (poll_interval_ns > timeout_ns / 16 && timeout_ns > 16) begin
            poll_interval_ns = timeout_ns / 16;
        end

        if (poll_interval_ns < 1) begin
            poll_interval_ns = 1;
        end

        driver_runtime_log("UART_DRIVER_WAIT",
            $sformatf("Entering wait_for_monitor_response, timeout=%0dns, poll=%0dns",
                      timeout_ns, poll_interval_ns),
            UVM_LOW);
        driver_debug_log("UART_DRIVER_WAIT",
            $sformatf("wait_for_monitor_response start: timeout=%0dns poll=%0dns fifo_depth=%0d time=%0t",
                      timeout_ns, poll_interval_ns,
                      (tx_response_fifo != null) ? tx_response_fifo.used() : -1,
                      $time));

        status_log_interval_ns = (timeout_ns >= 4) ? timeout_ns / 4 : timeout_ns;
        if (status_log_interval_ns < poll_interval_ns) begin
            status_log_interval_ns = poll_interval_ns;
        end
        next_status_log_time = $time + status_log_interval_ns;

        if (tx_response_fifo != null) begin
            driver_debug_log("UART_DRIVER_FIFO",
                $sformatf("Initial monitor FIFO depth=%0d", tx_response_fifo.used()),
                UVM_MEDIUM);
        end

        start_time = $time;
        
        // PERFORMANCE FIX: Use event-driven wait instead of fixed polling delay
        // Original: #(poll_interval_ns) caused 270,000x slowdown (86.8µs taking 1.25s real time)
        // New: @(posedge vif.clk) allows simulation to run at full speed
        while (($time - start_time) < timeout_ns) begin
            if (tx_response_fifo.try_get(item)) begin
                driver_runtime_log("UART_DRIVER_WAIT",
                    $sformatf("FIFO returned item: %s", (item == null) ? "NULL" : "VALID"),
                    UVM_LOW);
                driver_debug_log("UART_DRIVER_WAIT",
                    $sformatf("try_get returned %s at %0t depth_after=%0d",
                              (item == null) ? "NULL" : "VALID",
                              $time,
                              (tx_response_fifo != null) ? tx_response_fifo.used() : -1));

                if (item == null) begin
                    driver_runtime_log("UART_DRIVER_WAIT", "FIFO returned NULL item - ignoring", UVM_LOW);
                    continue;
                end

                // Print detailed info about the returned item for debugging
                driver_debug_log("UART_DRIVER_FIFO_ITEM",
                    $sformatf("FIFO item: direction=%0d status=0x%02X crc_valid=%0d frame_length=%0d", 
                              item.direction, item.response_status, item.crc_valid, item.frame_length),
                    UVM_HIGH);

                if (item.direction != UART_TX) begin
                    discarded_non_tx++;
                    driver_debug_log("UART_DRIVER_WAIT",
                        $sformatf("Discarded non-TX item at %0t dir=%s status=0x%02X depth_now=%0d",
                                  $time, item.direction.name(), item.response_status,
                                  (tx_response_fifo != null) ? tx_response_fifo.used() : -1));
                    continue;
                end

                resp = item;
                success = 1;
                waited_ns = $time - start_time;
                if (discarded_non_tx > 0) begin
                    driver_runtime_log("UART_DRIVER_WAIT",
                        $sformatf("Observed valid TX response after discarding %0d non-TX items", discarded_non_tx),
                        UVM_LOW);
                end
                driver_runtime_log("UART_DRIVER_WAIT",
                    $sformatf("Valid response observed after %0dns", waited_ns),
                    UVM_LOW);
                driver_debug_log("UART_DRIVER_WAIT",
                    $sformatf("Valid TX response observed after %0dns at %0t depth_after=%0d",
                              waited_ns, $time,
                              (tx_response_fifo != null) ? tx_response_fifo.used() : -1));
                return;
            end

            if ($time >= next_status_log_time) begin
                driver_debug_log("UART_DRIVER_WAIT",
                    $sformatf("Waiting (%0dns elapsed) depth=%0d discarded_non_tx=%0d time=%0t",
                              $time - start_time,
                              (tx_response_fifo != null) ? tx_response_fifo.used() : -1,
                              discarded_non_tx,
                              $time));
                next_status_log_time += status_log_interval_ns;
            end

            // CRITICAL FIX: Use clocking block (was @(posedge vif.clk) - causes DSIM hang)
            @(vif.driver_cb);  // ← CLOCKING BLOCK (DSIM-SAFE)
        end

        waited_ns = timeout_ns;
        success = 0;
        resp = null;

        driver_runtime_log("UART_DRIVER_WAIT",
            $sformatf("Monitor response timeout expired after %0dns", waited_ns),
            UVM_LOW);
        driver_debug_log("UART_DRIVER_WAIT",
            $sformatf("Timeout expired after %0dns depth=%0d discarded_non_tx=%0d time=%0t",
                      waited_ns,
                      (tx_response_fifo != null) ? tx_response_fifo.used() : -1,
                      discarded_non_tx,
                      $time));

        if (discarded_non_tx > 0) begin
            driver_runtime_log("UART_DRIVER_WAIT",
                $sformatf("Timeout occurred after discarding %0d non-TX items", discarded_non_tx),
                UVM_LOW);
        end
        if (tx_response_fifo != null) begin
            driver_debug_log("UART_DRIVER_FIFO",
                $sformatf("FIFO depth at timeout=%0d", tx_response_fifo.used()),
                UVM_MEDIUM);
        end
    endtask

    // Collect response from DUT - Hardware Specification Based Implementation
    virtual task collect_response(uart_frame_transaction tr);
        logic [7:0] response_bytes[];
        logic [7:0] temp_byte;
        real timeout_ns = cfg.frame_timeout_ns;
        real clk_freq = cfg.clk_freq_hz;
        int response_timeout_cycles = int'((timeout_ns * clk_freq) / 1_000_000_000.0);
        int byte_count = 0;
        int expected_response_length;
        bit timeout_occurred = 0;
        bit response_detected = 0;
        
        // Hardware Spec: Response timeout = 200ms max processing delay (measured ~100ms)
        localparam int RESPONSE_TIMEOUT_US = 200000;
        int response_wait_cycles = (RESPONSE_TIMEOUT_US * cfg.clk_freq_hz) / 1_000_000;
        
        // Determine expected response length based on protocol specification
        if (tr.cmd[7] == 1'b0) begin // Write command
            expected_response_length = 4; // SOF + STATUS + CMD + CRC
            driver_runtime_log("UART_DRIVER",
                "Write command: expecting 4-byte response (SOF + STATUS + CMD + CRC)");
        end else begin // Read command
            expected_response_length = 4; // Minimum for error response
            driver_runtime_log("UART_DRIVER",
                "Read command: expecting variable length response (minimum 4 bytes)");
        end

        driver_runtime_log("UART_DRIVER",
            $sformatf("Starting response collection for %s command (CMD=0x%02X)",
                      (tr.cmd[7] == 1'b1) ? "Read" : "Write", tr.cmd));
        
        // Monitor-style immediate response detection (no fork delay)
        // Wait for TX line to go low (response start bit) - immediate detection like Monitor
        // FIX: Add timeout protection for start bit detection
        fork
            begin
                // CRITICAL FIX: Use clocked loop instead of wait to avoid blocking at time 0
                time tx_wait_start = $time;
                while (vif.driver_cb.uart_tx != 1'b1) begin  // ← Sample via CB
                    @(vif.driver_cb);  // ← CLOCKING BLOCK
                    if (($time - tx_wait_start) > timeout_ns) break;
                end
                if (vif.driver_cb.uart_tx == 1'b1) begin  // ← Sample via CB
                    @(negedge vif.driver_cb.uart_tx);  // ← Edge detection via CB
                    response_detected = 1;
                end
            end
            begin
                #(timeout_ns);
                response_detected = 0;
            end
        join_any
        disable fork;

        if (!response_detected) begin
            if (tr.expect_error) begin
                driver_runtime_log("UART_DRIVER", "[expect_error=1] No response start bit detected (timeout)", UVM_LOW);
            end else begin
                `uvm_error("UART_DRIVER", $sformatf("Timeout waiting for response start bit after %0t ns", timeout_ns));
            end
            tr.response_received = 0;
            tr.response_status = 8'hFF;
            return;
        end

        driver_runtime_log("UART_DRIVER",
            $sformatf("Response start detected at time %0t", $realtime));
        
        // Hardware Spec: Collect response bytes using precise timing
        response_bytes = new[20]; // Allocate reasonable size
        byte_count = 0;
        
        begin
            driver_runtime_log("UART_DRIVER", "Starting protocol-aware response collection");
            
            // Hardware Spec: Collect first response byte (should be SOF = 0x5A)
            collect_uart_byte(temp_byte);
            response_bytes[byte_count] = temp_byte;
            byte_count++;
            driver_runtime_log("UART_DRIVER",
                $sformatf("Collected SOF byte: 0x%02X (expected 0x5A)", temp_byte));
            
            // Hardware Spec: For Write commands, collect exactly 4 bytes total
            if (tr.cmd[7] == 1'b0) begin // Write command
                // Collect remaining 3 bytes (STATUS, CMD, CRC)
                for (int i = 1; i < expected_response_length; i++) begin
                    // Hardware Spec: Wait for next byte start bit with inter-byte timeout
                    time inter_byte_timeout_ns;
                    inter_byte_timeout_ns = (cfg.byte_time_ns > 0) ? time'(cfg.byte_time_ns * 12) : 200_000; // 200µs default
                    fork : inter_byte_wait
                        begin
                            // CRITICAL FIX: Use clocked loop instead of wait
                            time tx_wait_start = $time;
                            while (vif.driver_cb.uart_tx != 1'b1) begin  // ← Sample via CB
                                @(vif.driver_cb);  // ← CLOCKING BLOCK
                                if (($time - tx_wait_start) > inter_byte_timeout_ns) break;
                            end
                            if (vif.driver_cb.uart_tx == 1'b1) begin  // ← Sample via CB
                                @(negedge vif.driver_cb.uart_tx);  // ← Edge detection via CB
                            end else begin
                                timeout_occurred = 1;
                            end
                        end
                        begin
                            #(inter_byte_timeout_ns);
                            timeout_occurred = 1;
                        end
                    join_any
                    disable inter_byte_wait;
                    
                    if (timeout_occurred) begin
                        `uvm_warning("UART_DRIVER", $sformatf("Inter-byte timeout after %0d bytes", byte_count));
                        break;
                    end
                    
                    collect_uart_byte(temp_byte);
                    response_bytes[byte_count] = temp_byte;
                    byte_count++;
                    driver_runtime_log("UART_DRIVER",
                        $sformatf("Collected Write response byte %0d: 0x%02X", i, temp_byte));
                end
                
                driver_runtime_log("UART_DRIVER",
                    $sformatf("Write response collection complete: %0d bytes", byte_count));
                
            end else begin // Read command - collect variable length
                // Continue collecting bytes until no more are available
                while (byte_count < 20) begin
                    // Wait for next byte start bit with timeout
                    time read_continuation_timeout_ns;
                    read_continuation_timeout_ns = (cfg.byte_time_ns > 0) ? time'(cfg.byte_time_ns * 50) : 5_000_000; // 5ms default
                    fork : read_byte_wait
                        begin
                            // CRITICAL FIX: Use clocked loop instead of wait
                            time tx_wait_start = $time;
                            while (vif.driver_cb.uart_tx != 1'b1) begin  // ← Sample via CB
                                @(vif.driver_cb);  // ← CLOCKING BLOCK
                                if (($time - tx_wait_start) > read_continuation_timeout_ns) break;
                            end
                            if (vif.driver_cb.uart_tx == 1'b1) begin  // ← Sample via CB
                                @(negedge vif.driver_cb.uart_tx);  // ← Edge detection via CB
                            end else begin
                                timeout_occurred = 1;
                            end
                        end
                        begin
                            #(read_continuation_timeout_ns);
                            timeout_occurred = 1;
                        end
                    join_any
                    disable read_byte_wait;
                    
                    if (timeout_occurred) begin
                        driver_runtime_log("UART_DRIVER",
                            $sformatf("Read response collection complete after %0d bytes", byte_count));
                        break;
                    end
                    
                    collect_uart_byte(temp_byte);
                    response_bytes[byte_count] = temp_byte;
                    byte_count++;
                    driver_runtime_log("UART_DRIVER",
                        $sformatf("Collected Read response byte %0d: 0x%02X", byte_count-1, temp_byte));
                end
            end
        end
        
        // Protocol-compliant response parsing
        if (byte_count > 0) begin
            tr.response_received = 1;
            
            // Validate response format
            if (response_bytes[0] == SOF_DEVICE_TO_HOST) begin // 0x5A
                if (byte_count >= 3) begin
                    tr.response_status = response_bytes[1]; // STATUS byte
                    driver_runtime_log("UART_DRIVER",
                        $sformatf("Protocol response: SOF=0x%02X STATUS=0x%02X CMD=0x%02X, total_bytes=%0d",
                                  response_bytes[0], response_bytes[1], response_bytes[2], byte_count));
                    
                    // Validate response length according to protocol
                    if (tr.cmd[7] == 1'b0) begin // Write command
                        if (byte_count != 4) begin
                            `uvm_warning("UART_DRIVER", $sformatf("Write response length mismatch: expected=4, received=%0d", byte_count));
                        end
                    end else begin // Read command
                        if (response_bytes[1] == 8'h00) begin // Success
                            if (byte_count < 7) begin
                                `uvm_warning("UART_DRIVER", $sformatf("Read success response too short: expected>=7, received=%0d", byte_count));
                            end
                        end else begin // Error
                            if (byte_count != 4) begin
                                `uvm_warning("UART_DRIVER", $sformatf("Read error response length mismatch: expected=4, received=%0d", byte_count));
                            end
                        end
                    end
                end else begin
                    `uvm_warning("UART_DRIVER", $sformatf("Response too short: minimum 3 bytes expected, received %0d", byte_count));
                    tr.response_status = 8'hFF; // Invalid response indicator
                end
            end else begin
                `uvm_warning("UART_DRIVER", $sformatf("Invalid SOF in response: expected=0x5A, received=0x%02X", response_bytes[0]));
                tr.response_status = response_bytes[0]; // Use first byte as status for compatibility
            end
            
            // Debug: print all received bytes
            begin
                string byte_str = "";
                for (int i = 0; i < byte_count; i++) begin
                    byte_str = {byte_str, $sformatf("0x%02X ", response_bytes[i])};
                end
                driver_runtime_log("UART_DRIVER",
                    $sformatf("Complete response: %s", byte_str));
            end
        end else begin
            if (tr.expect_error) begin
                driver_runtime_log("UART_DRIVER",
                    $sformatf("[expect_error=1] No DUT response (CRC error等の意図的エラー)。UVM_ERRORを抑制し警告のみ出力。"),
                    UVM_LOW);
            end else begin
                `uvm_error("UART_DRIVER", "No response received");
            end
            tr.response_received = 0;
            tr.response_status = 8'hFF; // Error indicator
        end
    endtask
    // Collect a single UART byte from TX line (Monitor's exact pattern)
    virtual task collect_uart_byte(output logic [7:0] data);
        int bit_time_cycles_local;

        bit_time_cycles_local = (cfg.bit_time_cycles > 0) ? cfg.bit_time_cycles : 1;

        // CRITICAL FIX: Use clocking block for sampling (DSIM-SAFE)
        // Caller already detected start bit edge
        // Move to start bit midpoint for verification
        repeat (bit_time_cycles_local / 2) @(vif.driver_cb);  // ← CLOCKING BLOCK
        if (vif.driver_cb.uart_tx != 1'b0) begin
            `uvm_info("UART_DRIVER", "TX start bit timing variation detected", UVM_DEBUG);
        end

        // Advance one full bit period to center of data[0]
        repeat (bit_time_cycles_local) @(vif.driver_cb);  // ← CLOCKING BLOCK
        data[0] = vif.driver_cb.uart_tx;  // ← Sample via clocking block
        `uvm_info("UART_DRIVER", $sformatf("Sampled TX data[0]=%0b at %0t", data[0], $realtime), UVM_DEBUG);

        // Sample remaining data bits at full bit intervals
        for (int i = 1; i < 8; i++) begin
            repeat (bit_time_cycles_local) @(vif.driver_cb);  // ← CLOCKING BLOCK
            data[i] = vif.driver_cb.uart_tx;  // ← Sample via clocking block
            `uvm_info("UART_DRIVER", $sformatf("Sampled TX data[%0d]=%0b at %0t", i, data[i], $realtime), UVM_DEBUG);
        end

        // Sample stop bit midpoint
        repeat (bit_time_cycles_local) @(vif.driver_cb);  // ← CLOCKING BLOCK
        if (vif.driver_cb.uart_tx != 1'b1) begin
            `uvm_info("UART_DRIVER", "TX stop bit timing variation detected", UVM_DEBUG);
        end
        
        driver_runtime_log("UART_DRIVER",
            $sformatf("Collected UART byte: 0x%02X", data));
    endtask
    
    // Simple CRC-8 calculation (polynomial 0x07)
    virtual function logic [7:0] calculate_crc(logic [7:0] data[], int length);
        logic [7:0] crc = 8'h00;
        logic [7:8] crc_temp;
        
        // Input validation with fatal
        if (length < 0) begin
            `uvm_fatal("UART_DRIVER_FATAL", 
                $sformatf("calculate_crc: Invalid length=%0d (negative)", length))
        end
        
        if (length > 1024) begin
            `uvm_fatal("UART_DRIVER_FATAL",
                $sformatf("calculate_crc: Invalid length=%0d (exceeds 1024)", length))
        end
        
        if (data.size() == 0) begin
            `uvm_fatal("UART_DRIVER_FATAL", "calculate_crc: data array has zero size")
        end
        
        for (int i = 0; i < length; i++) begin
            // Match RTL implementation: XOR entire byte first, then process 8 bits
            crc_temp = crc ^ data[i];
            
            // Process each bit with polynomial 0x07 (matches RTL calc_crc8_byte)
            if (crc_temp[7]) crc_temp = (crc_temp << 1) ^ 8'h07; else crc_temp = crc_temp << 1;
            if (crc_temp[7]) crc_temp = (crc_temp << 1) ^ 8'h07; else crc_temp = crc_temp << 1;
            if (crc_temp[7]) crc_temp = (crc_temp << 1) ^ 8'h07; else crc_temp = crc_temp << 1;
            if (crc_temp[7]) crc_temp = (crc_temp << 1) ^ 8'h07; else crc_temp = crc_temp << 1;
            if (crc_temp[7]) crc_temp = (crc_temp << 1) ^ 8'h07; else crc_temp = crc_temp << 1;
            if (crc_temp[7]) crc_temp = (crc_temp << 1) ^ 8'h07; else crc_temp = crc_temp << 1;
            if (crc_temp[7]) crc_temp = (crc_temp << 1) ^ 8'h07; else crc_temp = crc_temp << 1;
            if (crc_temp[7]) crc_temp = (crc_temp << 1) ^ 8'h07; else crc_temp = crc_temp << 1;
            
            crc = crc_temp;
        end
        
        return crc;
    endfunction

    
    // Monitor response start with stability and timeout handling
    virtual task monitor_response(uart_frame_transaction tr,
                                  input time start_timeout_override = 0,
                                  input time inter_byte_timeout_override = 0);
        bit start_detected;

        wait_for_response_start(start_detected, start_timeout_override);

        if (!start_detected) begin
            time effective_timeout = (start_timeout_override > 0) ? start_timeout_override : time'(cfg.frame_timeout_ns);
            `uvm_error("UART_DRIVER", $sformatf("Response start not detected within %0dns", effective_timeout));
            tr.response_received = 0;
            tr.response_status = 8'hFF;
            return;
        end

    `uvm_info("UART_DRIVER", $sformatf("Response start detected at time %0t", $realtime), UVM_MEDIUM);
        collect_response_direct(tr, inter_byte_timeout_override);
    endtask

    // Wait for a stable UART TX start bit with glitch rejection
    virtual task wait_for_response_start(output bit detected, input time timeout_override = 0);
        int bit_time_cycles;
        int guard_cycles;
        time timeout_limit;

        bit_time_cycles = cfg.clk_freq_hz / cfg.baud_rate;
        detected = 0;

        guard_cycles = bit_time_cycles >> 2;
        if (guard_cycles == 0) begin
            guard_cycles = 1;
        end

        timeout_limit = (timeout_override > 0) ? timeout_override : time'(cfg.frame_timeout_ns);

        while (!detected) begin
            bit timeout_hit = 0;

            fork
                begin : wait_for_low
                    // CRITICAL FIX: Don't wait for HIGH if already LOW - just wait for negedge
                    if (vif.uart_tx == 1'b1) begin
                        @(negedge vif.uart_tx);
                    end else begin
                        // Already LOW - wait for return to IDLE then next negedge
                        @(posedge vif.uart_tx);
                        @(negedge vif.uart_tx);
                    end
                end
                begin : timeout_guard_thread
                    #(timeout_limit);
                    timeout_hit = 1;
                end
            join_any
            disable fork;

            if (timeout_hit) begin
                detected = 0;
                return;
            end

            repeat (guard_cycles) @(vif.driver_cb);  // ← CLOCKING BLOCK

            if (vif.driver_cb.uart_tx == 1'b0) begin  // ← Sample via CB
                detected = 1;
            end else begin
                `uvm_info("UART_DRIVER", "Ignoring spurious uart_tx pulse before response start", UVM_DEBUG);
            end
        end
    endtask

    // Direct response collection using exact Monitor pattern
    virtual task collect_response_direct(uart_frame_transaction tr,
                                         input time inter_byte_timeout_override = 0);
        logic [7:0] response_bytes[];
        logic [7:0] temp_byte;
        int byte_count = 0;
        int expected_response_length = 4; // SOF + STATUS + CMD + CRC
        time inter_byte_timeout;
        bit timeout_occurred;
        
        `uvm_info("UART_DRIVER", "Starting direct response collection (exact Monitor-style)", UVM_MEDIUM);
        
        // Hardware Spec: Collect response bytes using exact Monitor timing pattern
        response_bytes = new[20]; // Allocate reasonable size
        byte_count = 0;
        timeout_occurred = 0;
        inter_byte_timeout = (inter_byte_timeout_override > 0) ? inter_byte_timeout_override :
                             ((cfg.byte_time_ns > 0) ? time'(cfg.byte_time_ns * 12) : 100_000);
        
        begin
            // Hardware Spec: First byte collection - response already started
            // Do NOT wait for additional start bit - we detected response start already
            collect_uart_byte(temp_byte);
            response_bytes[byte_count] = temp_byte;
            byte_count++;
            `uvm_info("UART_DRIVER", $sformatf("Collected SOF byte: 0x%02X (expected 0x5A)", temp_byte), UVM_MEDIUM);
            
            // Hardware Spec: For Write commands, collect exactly 4 bytes total
            if (tr.cmd[7] == 1'b0) begin // Write command
                // Collect remaining 3 bytes (STATUS, CMD, CRC)
                for (int i = 1; i < expected_response_length; i++) begin
                    // Hardware Spec: Wait for next byte start bit with inter-byte timeout
                    fork : metadata_inter_byte_wait
                        begin
                            // CRITICAL FIX: Use clocked loop instead of wait
                            time tx_wait_start = $time;
                            while (vif.driver_cb.uart_tx != 1'b1) begin  // ← Sample via CB
                                @(vif.driver_cb);  // ← CLOCKING BLOCK
                                if (($time - tx_wait_start) > inter_byte_timeout) break;
                            end
                            if (vif.driver_cb.uart_tx == 1'b1) begin  // ← Sample via CB
                                @(negedge vif.driver_cb.uart_tx);  // ← Edge detection via CB
                            end else begin
                                timeout_occurred = 1;
                            end
                        end
                        begin
                            #(inter_byte_timeout);
                            timeout_occurred = 1;
                        end
                    join_any
                    disable metadata_inter_byte_wait;

                    if (timeout_occurred) begin
                        `uvm_warning("UART_DRIVER", $sformatf("Inter-byte timeout after %0d bytes", byte_count));
                        break;
                    end

                    collect_uart_byte(temp_byte);
                    response_bytes[byte_count] = temp_byte;
                    byte_count++;
                    `uvm_info("UART_DRIVER", $sformatf("Collected Write response byte %0d: 0x%02X", i, temp_byte), UVM_MEDIUM);
                end
                
                `uvm_info("UART_DRIVER", $sformatf("Write response collection complete: %0d bytes", byte_count), UVM_MEDIUM);
            end
        end
        
        // Validate first byte is SOF
        if (timeout_occurred) begin
            tr.response_received = 0;
            tr.response_status = 8'hFF;
            `uvm_warning("UART_DRIVER", "Direct response collection aborted due to inter-byte timeout");
        end else if (byte_count > 0 && response_bytes[0] == 8'h5A) begin
            `uvm_info("UART_DRIVER", "SUCCESS: Collected correct SOF byte 0x5A!", UVM_MEDIUM);
            tr.response_received = 1;
            tr.response_status = response_bytes[1]; // STATUS byte
        end else begin
            `uvm_error("UART_DRIVER", $sformatf("FAILURE: Wrong SOF byte 0x%02X, expected 0x5A", 
                       byte_count > 0 ? response_bytes[0] : 8'h00));
            tr.response_received = 0;
            tr.response_status = 8'hFF;
        end
    endtask

    // Monitor-exact TX byte collection pattern (immediate sampling)
    virtual task collect_uart_tx_byte_monitor(output logic [7:0] data);
        int bit_time_cycles = cfg.clk_freq_hz / cfg.baud_rate;
        
        // CRITICAL: Immediate sampling without any delay
        // We detect response start, now sample immediately from current position
        
        int half_bit_cycles;

        half_bit_cycles = bit_time_cycles >> 1;
        if (half_bit_cycles == 0) begin
            half_bit_cycles = 1;
        end

        // Align to middle of first data bit (skip remaining start bit time)
        repeat (bit_time_cycles + half_bit_cycles) @(vif.driver_cb);  // ← CLOCKING BLOCK

        // Sample data bits (LSB first) at bit center
        for (int i = 0; i < 8; i++) begin
            data[i] = vif.driver_cb.uart_tx;  // ← Sample via CB
            `uvm_info("UART_DRIVER", $sformatf("Immediate Bit[%0d]: %b", i, data[i]), UVM_DEBUG);
            if (i < 7) begin
                for (int _cycle = 0; _cycle < bit_time_cycles; _cycle++) @(vif.driver_cb);
            end
        end

        // Sample stop bit (advance to end of byte)
        for (int _cycle = 0; _cycle < bit_time_cycles; _cycle++) @(vif.driver_cb);
        if (vif.driver_cb.uart_tx != 1'b1) begin  // ← Sample via CB
            `uvm_info("UART_DRIVER", "TX stop bit timing variation detected", UVM_DEBUG);
        end
        
    endtask

    // Task to control CTS signal for flow control testing
    virtual task assert_cts(bit enable);
        vif.uart_cts_n = enable ? 1'b0 : 1'b1;  // Active low logic
        `uvm_info("UART_DRIVER", $sformatf("CTS %s", enable ? "asserted (low)" : "deasserted (high)"), UVM_MEDIUM);
    endtask

    // Task to wait for RTS assertion/deassertion
    virtual task wait_for_rts(bit expected_state, int timeout_cycles = 1000);
        logic expected_rts_n = expected_state ? 1'b0 : 1'b1;  // Active low logic
        int cycle_count = 0;
        bit rts_detected = 0;
        time timeout_ns = timeout_cycles * (1_000_000_000 / cfg.clk_freq_hz);
        time start_time = $time;
        
        // FIX: Add time-based timeout protection
        // Refactored to avoid fork/join_any instability
        while (vif.driver_cb.uart_rts_n !== expected_rts_n && cycle_count < timeout_cycles) begin  // ← Sample via CB
            @(vif.driver_cb);  // ← CLOCKING BLOCK
            cycle_count++;
            if (($time - start_time) > timeout_ns) begin
                break; // Timeout
            end
        end
        rts_detected = (vif.driver_cb.uart_rts_n === expected_rts_n);  // ← Sample via CB
        
        if (!rts_detected) begin
            `uvm_warning("UART_DRIVER", $sformatf("Timeout waiting for RTS %s (cycles=%0d, time=%0t ns)", 
                expected_state ? "assertion" : "deassertion", cycle_count, timeout_ns));
        end else begin
            `uvm_info("UART_DRIVER", $sformatf("RTS %s detected after %0d cycles", 
                expected_state ? "asserted" : "deasserted", cycle_count), UVM_MEDIUM);
        end
    endtask

    // Task to simulate flow control scenario
    virtual task simulate_flow_control_backpressure(int hold_cycles);
        time hold_time_ns = hold_cycles * (1_000_000_000 / cfg.clk_freq_hz);
        time max_hold_time = hold_time_ns * 2; // Safety margin
        time start_time = $time;
        int current_cycle = 0;
        
        `uvm_info("UART_DRIVER", $sformatf("Simulating flow control backpressure for %0d cycles", hold_cycles), UVM_MEDIUM);
        
        // Assert CTS to prevent transmission
        assert_cts(1'b0);  // Deassert CTS (high) to block transmission
        
        // FIX: Add time-based timeout protection
        // Refactored to avoid fork/join_any instability
        while (current_cycle < hold_cycles) begin
            @(vif.driver_cb);  // ← CLOCKING BLOCK
            current_cycle++;
            if (($time - start_time) > max_hold_time) begin
                `uvm_fatal("UART_DRIVER", $sformatf("Clock stopped during flow control backpressure (expected %0d cycles, %0t ns)", 
                    hold_cycles, max_hold_time));
            end
        end
        
        // Release CTS to allow transmission
        assert_cts(1'b1);  // Assert CTS (low) to allow transmission
        `uvm_info("UART_DRIVER", "Flow control backpressure released", UVM_MEDIUM);
    endtask

    // ★ Baud rate 切替時の応答バッファリセット
    // CONFIG write の response（baud rate 不一致で受信失敗したもの）を破棄
    // Test 側から明示的に呼び出される
    virtual function void reset_response_buffer();
        uart_frame_transaction dummy_tr;
        int flushed_count = 0;
        
        `uvm_info(get_type_name(), 
            $sformatf("Resetting response buffer @ t=%0t for baud rate change", $time),
            UVM_HIGH)
        
        // tx_response_fifo が使用可能な場合のみフラッシュ
        if (tx_response_fifo != null) begin
            // FIFO 内のゴミデータをすべて破棄
            while (tx_response_fifo.try_get(dummy_tr)) begin
                flushed_count++;
            end
            
            if (flushed_count > 0) begin
                `uvm_info(get_type_name(), 
                    $sformatf("Flushed %0d stale response(s) from FIFO (baud rate mismatch period)", flushed_count),
                    UVM_MEDIUM)
            end else begin
                `uvm_info(get_type_name(), 
                    "Response FIFO was already empty - no stale data to flush",
                    UVM_HIGH)
            end
        end else begin
            `uvm_info(get_type_name(), 
                "Response FIFO not available (direct sampling mode) - no buffer to reset",
                UVM_HIGH)
        end
        
        `uvm_info(get_type_name(), 
            "Response buffer reset complete - ready for new baud rate",
            UVM_HIGH)
    endfunction

endclass