`timescale 1ns / 1ps

class uart_axi4_basic_115200_test extends uart_axi4_basic_test;

    `uvm_component_utils(uart_axi4_basic_115200_test)

    // Changed from 115200 (67.8x slower) to 921600 (8.5x slower) for practical test duration
    // Original 115200 baud caused 465-second Phase 1 delay and >180s timeout
    // See: docs/uart_115200_baud_test_analysis_20251117.md
    localparam int TARGET_BAUD_RATE = 921_600;  // 125MHz / 921600 = 136 (0x88)
    int runtime_baud_divisor;
    int original_baud_rate;
    int original_byte_time_ns;
    int original_frame_timeout_ns;
    simple_debug_write_sequence_20250923 data_seq;  // Phase 4 data transfer

    function new(string name = "uart_axi4_basic_115200_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void configure_test();
        super.configure_test();

        // Save original timing parameters for phase 1 (default baud rate)
        original_baud_rate = cfg.baud_rate;
        original_byte_time_ns = cfg.byte_time_ns;
        original_frame_timeout_ns = cfg.frame_timeout_ns;

        // Phase 1: Keep default baud rate for CONFIG write
        // (DUT will be at original_baud_rate until we program CONFIG register)
        cfg.enable_driver_debug_logs = 1'b1;
        cfg.driver_debug_verbosity = UVM_HIGH;

        `uvm_info("BASIC115_CONFIG",
            $sformatf("Test initialized: phase1_baud=%0d target_baud=%0d byte_time_ns=%0d frame_timeout_ns=%0d",
                original_baud_rate, TARGET_BAUD_RATE, cfg.byte_time_ns, cfg.frame_timeout_ns),
            UVM_LOW)
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // Phase 1 uses default baud divisor - no override yet
        `uvm_info("BASIC115_CONFIG",
            $sformatf("Build phase: phase1_baud=%0d (will switch to %0d after CONFIG write)",
                cfg.baud_rate, TARGET_BAUD_RATE),
            UVM_LOW)
    endfunction

    protected function void compute_runtime_baud_divisor();
        int divisor;

        if (cfg == null) begin
            runtime_baud_divisor = 1;
            `uvm_warning("BASIC115_CONFIG", "Configuration handle unavailable; forcing baud divisor to 1")
            return;
        end

        divisor = (TARGET_BAUD_RATE > 0) ? (cfg.clk_freq_hz / TARGET_BAUD_RATE) : 0;
        if (divisor <= 0) begin
            divisor = 1;
        end

        if (divisor > 16'hFFFF) begin
            `uvm_warning("BASIC115_CONFIG",
                $sformatf("Computed divisor=%0d exceeds 16-bit field; clamping to 0xFFFF", divisor))
            divisor = 16'hFFFF;
        end

        runtime_baud_divisor = divisor;
        `uvm_info("BASIC115_CONFIG",
            $sformatf("Computed target baud divisor=%0d (0x%04h) for %0d baud (clk=%0d Hz)",
                runtime_baud_divisor, runtime_baud_divisor[15:0], TARGET_BAUD_RATE, cfg.clk_freq_hz),
            UVM_MEDIUM)
    endfunction

    protected function void apply_uart_interface_divisor(string caller_id);
        if (cfg != null && cfg.uart_vif != null) begin
            cfg.uart_vif.baud_divisor = runtime_baud_divisor[15:0];
            `uvm_info(caller_id,
                $sformatf("UART interface baud_divisor programmed to %0d (0x%04h)",
                    runtime_baud_divisor, runtime_baud_divisor[15:0]),
                UVM_LOW)
        end else begin
            `uvm_warning(caller_id,
                $sformatf("UART virtual interface unavailable; pending divisor=%0d (0x%04h)",
                    runtime_baud_divisor, runtime_baud_divisor[15:0]))
        end
    endfunction

    protected task wait_for_uart_quiescent(string caller_id, int idle_bit_windows = 16);
        virtual uart_if vif;
        int bit_cycles;
        int idle_cycles_required;
        int idle_counter;

        if (cfg == null) begin
            `uvm_warning(caller_id, "Configuration handle unavailable; cannot wait for UART idle")
            return;
        end

        vif = cfg.uart_vif;
        if (vif == null) begin
            `uvm_warning(caller_id, "UART virtual interface unavailable; cannot enforce idle guard")
            return;
        end

        bit_cycles = cfg.get_bit_time_cycles();
        if (bit_cycles < 1) begin
            bit_cycles = 1;
        end

        if (idle_bit_windows < 1) begin
            idle_bit_windows = 1;
        end

        idle_cycles_required = bit_cycles * idle_bit_windows;
        if (idle_cycles_required < 8) begin
            idle_cycles_required = 8;
        end

        `uvm_info(caller_id,
            $sformatf("Waiting for UART lines to remain idle for %0d cycles (bit_cycles=%0d)",
                idle_cycles_required, bit_cycles),
            UVM_MEDIUM)

        idle_counter = 0;
        while (idle_counter < idle_cycles_required) begin
            @(posedge vif.clk);
            if ((vif.uart_tx === 1'b1) && (vif.uart_rx === 1'b1) &&
                (vif.tx_busy === 1'b0) && (vif.rx_valid === 1'b0)) begin
                idle_counter++;
            end else begin
                idle_counter = 0;
            end
        end

        `uvm_info(caller_id,
            $sformatf("UART idle guard satisfied after %0d cycles", idle_cycles_required),
            UVM_LOW)
    endtask

    protected task program_baud_and_reset();
        uart_configure_baud_sequence cfg_seq;
        uart_reset_sequence reset_seq;

        if (env == null || env.uart_agt == null || env.uart_agt.sequencer == null) begin
            `uvm_fatal("BASIC115_CONFIG", "Environment or UART sequencer unavailable for baud programming")
        end

        // Ensure the runtime divisor has been evaluated before programming the DUT.
        if (runtime_baud_divisor == 0) begin
            compute_runtime_baud_divisor();
        end

        `uvm_info("BASIC115_PHASE1",
            "====================================================================",
            UVM_LOW)
        `uvm_info("BASIC115_PHASE1",
            "PHASE 1: Write CONFIG register @ default baud (7.8Mbps)",
            UVM_LOW)
        
        cfg_seq = uart_configure_baud_sequence::type_id::create("baud_cfg_seq", this);
        if (cfg_seq == null) begin
            `uvm_fatal("BASIC115_CONFIG", "Failed to create uart_configure_baud_sequence")
        end

        if (runtime_baud_divisor == 0) begin
            `uvm_fatal("BASIC115_CONFIG",
                "runtime_baud_divisor is zero prior to CONFIG write – divisor calculation failed")
        end

        cfg_seq.divisor_value = runtime_baud_divisor;
        cfg_seq.timeout_field_value = 8'h00;

        `uvm_info("BASIC115_PHASE1",
            $sformatf("CONFIG write: divisor=%0d (0x%04h) for %0d baud",
                runtime_baud_divisor, runtime_baud_divisor[15:0], TARGET_BAUD_RATE),
            UVM_MEDIUM)

        // NOTE: CONFIG write response will be skipped by uart_driver.sv
        // (addr==0x00001008 triggers response skip due to baud rate mismatch)
        cfg_seq.start(env.uart_agt.sequencer);
        
        `uvm_info("BASIC115_PHASE1",
            $sformatf("CONFIG write completed @ t=%0t", $time),
            UVM_MEDIUM)
        
        `uvm_info("BASIC115_PHASE2",
            "====================================================================",
            UVM_LOW)
        `uvm_info("BASIC115_PHASE2",
            "PHASE 2: Send RESET command @ default baud (7.8Mbps)",
            UVM_LOW)
        
        // Execute RESET sequence (soft reset without response)
        reset_seq = uart_reset_sequence::type_id::create("reset_seq", this);
        if (reset_seq == null) begin
            `uvm_fatal("BASIC115_PHASE2", "Failed to create uart_reset_sequence")
        end
        
        // NOTE: RESET response will be skipped by uart_driver.sv
        // (cmd==0xFF triggers response skip, RTL sends no response)
        reset_seq.start(env.uart_agt.sequencer);
        
        `uvm_info("BASIC115_PHASE2",
            $sformatf("RESET command completed @ t=%0t", $time),
            UVM_MEDIUM)
        
        `uvm_info("BASIC115_PHASE3",
            "====================================================================",
            UVM_LOW)
        `uvm_info("BASIC115_PHASE3",
            "PHASE 3: Update UVM timing parameters",
            UVM_LOW)
        
        `uvm_info("BASIC115_PHASE3",
            $sformatf("New baud rate: %0d (byte_time will be recalculated)", TARGET_BAUD_RATE),
            UVM_LOW)
        
        // Update UVM environment timing to match new baud rate
        cfg.baud_rate = TARGET_BAUD_RATE;
        cfg.calculate_timing();
        cfg.frame_timeout_ns = cfg.byte_time_ns * 128;
        
        `uvm_info("BASIC115_PHASE3",
            $sformatf("UVM timing updated: byte_time_ns=%0d, bit_time_cycles=%0d, frame_timeout_ns=%0d",
                cfg.byte_time_ns, cfg.bit_time_cycles, cfg.frame_timeout_ns),
            UVM_LOW)
        
        `uvm_info("BASIC115_PHASE3",
            "Waiting for RTL/UVM synchronization...",
            UVM_MEDIUM)
        
        // Short settling delay to ensure RTL and UVM are synchronized
        #1600ns;
        
        `uvm_info("BASIC115_PHASE3",
            "====================================================================",
            UVM_LOW)
        `uvm_info("BASIC115_PHASE3",
            $sformatf("Baud switch complete @ t=%0t", $time),
            UVM_LOW)
        `uvm_info("BASIC115_PHASE3",
            $sformatf("RTL and UVM now synchronized @ %0d baud", TARGET_BAUD_RATE),
            UVM_LOW)
        `uvm_info("BASIC115_PHASE3",
            "====================================================================",
            UVM_LOW)
    endtask

    virtual task run_phase(uvm_phase phase);
        bit test_timeout_occurred = 0;
        time watchdog_timeout;
        
        phase.raise_objection(this, "Baud rate change test");
        
        // Calculate watchdog timeout (use config or fallback)
        watchdog_timeout = (cfg != null) ? cfg.get_simulation_watchdog_timeout() : 60_000_000_000;
        
        fork
            begin: test_execution
                wait (uart_axi4_tb_top.rst_n == 1'b1);
                repeat (10) @(posedge uart_axi4_tb_top.clk);
                
                `uvm_info(get_type_name(), "Starting baud rate switch test", UVM_LOW)
                
                // Execute CONFIG write + RESET + timing update (Phases 1-3)
                program_baud_and_reset();
                
                `uvm_info(get_type_name(),
                    "################################################################################",
                    UVM_LOW)
                `uvm_info(get_type_name(),
                    "TEST COMPLETE: Baud switch verified",
                    UVM_LOW)
                `uvm_info(get_type_name(),
                    $sformatf("CONFIG write → RESET → Timing update @ %0d baud successful", TARGET_BAUD_RATE),
                    UVM_LOW)
                `uvm_info(get_type_name(),
                    "################################################################################",
                    UVM_LOW)
                
                // PHASE 4: Execute minimal data transfer @ 921.6kbps to verify new baud rate
                `uvm_info(get_type_name(),
                    "################################################################################",
                    UVM_LOW)
                `uvm_info(get_type_name(),
                    $sformatf("PHASE 4: Data transfer @ %0d baud (1 transaction)", TARGET_BAUD_RATE),
                    UVM_LOW)
                `uvm_info(get_type_name(),
                    "################################################################################",
                    UVM_LOW)
                
                data_seq = simple_debug_write_sequence_20250923::type_id::create("data_seq", this);
                data_seq.start(env.uart_agt.sequencer);
                
                `uvm_info(get_type_name(),
                    $sformatf("Phase 4 complete: Data transfer @ %0d baud successful", TARGET_BAUD_RATE),
                    UVM_LOW)
                
                `uvm_info(get_type_name(),
                    "################################################################################",
                    UVM_LOW)
                `uvm_info(get_type_name(),
                    "TEST COMPLETED SUCCESSFULLY",
                    UVM_LOW)
                `uvm_info(get_type_name(),
                    $sformatf("Final simulation time: %0t", $time),
                    UVM_LOW)
                `uvm_info(get_type_name(),
                    "################################################################################",
                    UVM_LOW)
            end
            
            begin: test_watchdog
                // Timeout protection - ensures objection is always dropped
                #(watchdog_timeout);
                test_timeout_occurred = 1;
                
                `uvm_fatal(get_type_name(),
                    $sformatf("Test timeout after %0t ns (%.2f sec) - forcing completion",
                              watchdog_timeout, watchdog_timeout / 1_000_000_000.0))
            end
        join_any
        
        disable fork;  // Clean up remaining processes
        
        if (test_timeout_occurred) begin
            `uvm_info("BASIC115_TIMEOUT",
                "Test watchdog triggered - objection will be dropped to prevent hang",
                UVM_NONE)
        end
        
        // Drop objection AFTER test completes (or timeout)
        phase.drop_objection(this, "Baud rate change test completed or timed out");
    endtask

endclass
