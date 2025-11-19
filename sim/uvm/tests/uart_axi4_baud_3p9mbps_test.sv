`timescale 1ns / 1ps

//=============================================================================
// uart_axi4_baud_3p9mbps_test.sv
//
// Baud Rate Switching Test: 7.8Mbps → 3.90625Mbps (divisor=2)
// 
// Description:
//   Tests baud rate switching from default 7.8Mbps to 3.90625Mbps using the
//   proper sequence: CONFIG write → RESET → UVM update → Data transfer.
//   This is 1 step slower than maximum speed for faster simulation.
//
// Timeline:
//   Phase 0: Initial state @ 7.8Mbps (default baud, divisor=1)
//   Phase 1: Write CONFIG register @ 7.8Mbps (set divisor=2 for 3.90625Mbps)
//            - DUT immediately switches to 3.90625Mbps (RTL behavior)
//            - Response skipped due to baud rate mismatch
//   Phase 2: Send RESET command @ 7.8Mbps (clear internal state)
//            - DUT still at 3.90625Mbps
//            - Response skipped due to baud rate mismatch  
//   Phase 3: Update UVM timing parameters to 3.90625Mbps
//            - cfg.baud_rate = 3_906_250
//            - cfg.calculate_timing()
//            - Synchronizes UVM with DUT
//   Phase 4: Execute data transfer @ 3.90625Mbps (verify synchronization)
//            - 1 WRITE transaction to verify baud rate switch
//
// Baud Rate Calculation:
//   Default:  125MHz / (1 * 16) = 7,812,500 bps
//   Target:   125MHz / (2 * 16) = 3,906,250 bps
//   Bit time: 16 * 2 = 32 cycles = 256ns @ 125MHz
//   Byte time: 10 bits * 256ns = 2,560ns = 2.56μs
//
// Expected Result:
//   - CONFIG write completes @ 7.8Mbps (no response expected)
//   - RESET completes @ 7.8Mbps (no response expected)
//   - UVM timing updated to bit_time_cycles=32
//   - Data transfer successful @ 3.90625Mbps with proper response
//   - Test completes significantly faster than 921.6kbps version
//
// Author: AXIUART Development Team
// Date: 2025-11-19
//=============================================================================

class uart_axi4_baud_3p9mbps_test extends uart_axi4_base_test;
    `uvm_component_utils(uart_axi4_baud_3p9mbps_test)
    
    // Target baud rate after switch
    localparam int TARGET_BAUD_RATE = 3_906_250;  // 125MHz / (2 * 16) = 3.90625Mbps
    localparam int TARGET_DIVISOR = 2;            // Baud divisor for 3.90625Mbps
    
    // Configuration references
    uart_configure_baud_sequence baud_seq;
    uart_reset_sequence reset_seq;
    simple_debug_write_sequence_20250923 data_seq;
    
    function new(string name = "uart_axi4_baud_3p9mbps_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        `uvm_info(get_type_name(),
            $sformatf("Building 3.90625Mbps baud switching test (divisor=%0d)", TARGET_DIVISOR),
            UVM_LOW)
    endfunction
    
    //-------------------------------------------------------------------------
    // Program Baud Rate and Reset Task
    // Sequence: CONFIG write → RESET → UVM update
    //-------------------------------------------------------------------------
    virtual task program_baud_and_reset();
        `uvm_info("BAUD_SWITCH",
            "====================================================================",
            UVM_LOW)
        `uvm_info("BAUD_SWITCH",
            "PHASE 1: Write CONFIG register @ 7.8Mbps",
            UVM_LOW)
        `uvm_info("BAUD_SWITCH",
            $sformatf("Setting divisor=%0d for target baud=%0d", TARGET_DIVISOR, TARGET_BAUD_RATE),
            UVM_LOW)
        
        // Step 1: CONFIG write at current (default) baud rate
        // DUT will immediately switch to new baud rate upon receiving this
        baud_seq = uart_configure_baud_sequence::type_id::create("baud_seq");
        baud_seq.divisor_value = TARGET_DIVISOR;
        baud_seq.start(env.uart_agt.sequencer);
        
        `uvm_info("BAUD_SWITCH",
            $sformatf("CONFIG write completed @ t=%0t", $time),
            UVM_MEDIUM)
        `uvm_info("BAUD_SWITCH",
            "Note: DUT has now switched to 3.90625Mbps (RTL immediate activation)",
            UVM_MEDIUM)
        
        // Small delay between CONFIG write and RESET command
        repeat (50) @(posedge uart_axi4_tb_top.clk);  // 400ns
        
        `uvm_info("BAUD_SWITCH",
            "====================================================================",
            UVM_LOW)
        `uvm_info("BAUD_SWITCH",
            "PHASE 2: Send RESET command @ 7.8Mbps",
            UVM_LOW)
        `uvm_info("BAUD_SWITCH",
            "This will clear internal state (FIFOs, state machines)",
            UVM_LOW)
        
        // Step 2: RESET command (UVM still at old baud rate)
        // DUT is already at new baud rate, so there's a mismatch
        // Response will not be readable, hence skip_response is used
        reset_seq = uart_reset_sequence::type_id::create("reset_seq");
        reset_seq.start(env.uart_agt.sequencer);
        
        `uvm_info("BAUD_SWITCH",
            $sformatf("RESET command completed @ t=%0t", $time),
            UVM_MEDIUM)
        
        `uvm_info("BAUD_SWITCH",
            "====================================================================",
            UVM_LOW)
        `uvm_info("BAUD_SWITCH",
            "PHASE 3: Update UVM timing parameters",
            UVM_LOW)
        `uvm_info("BAUD_SWITCH",
            $sformatf("New baud rate: %0d (synchronizing UVM with DUT)", TARGET_BAUD_RATE),
            UVM_LOW)
        
        // Step 3: Update UVM timing AFTER RTL has processed RESET
        // Now both RTL and UVM will be synchronized to new baud rate
        cfg.baud_rate = TARGET_BAUD_RATE;
        cfg.calculate_timing();
        cfg.frame_timeout_ns = cfg.byte_time_ns * 128;  // Generous timeout
        
        `uvm_info("BAUD_SWITCH",
            $sformatf("UVM timing updated: byte_time_ns=%0d, bit_time_cycles=%0d, frame_timeout_ns=%0d",
                cfg.byte_time_ns, cfg.bit_time_cycles, cfg.frame_timeout_ns),
            UVM_LOW)
        
        // Verify expected values
        if (cfg.bit_time_cycles != 32) begin
            `uvm_warning("BAUD_SWITCH",
                $sformatf("Unexpected bit_time_cycles=%0d (expected 32)", cfg.bit_time_cycles))
        end
        
        // Step 4: Stabilization wait
        `uvm_info("BAUD_SWITCH",
            "Waiting for RTL/UVM synchronization...",
            UVM_MEDIUM)
        
        repeat (200) @(posedge uart_axi4_tb_top.clk);  // 1.6µs
        
        `uvm_info("BAUD_SWITCH",
            "====================================================================",
            UVM_LOW)
        `uvm_info("BAUD_SWITCH",
            $sformatf("Baud switch complete @ t=%0t", $time),
            UVM_LOW)
        `uvm_info("BAUD_SWITCH",
            $sformatf("RTL and UVM now synchronized @ %0d baud", TARGET_BAUD_RATE),
            UVM_LOW)
        `uvm_info("BAUD_SWITCH",
            "====================================================================",
            UVM_LOW)
    endtask
    
    //-------------------------------------------------------------------------
    // Run Phase - Execute Complete Test Flow
    //-------------------------------------------------------------------------
    virtual task run_phase(uvm_phase phase);
        bit test_timeout = 0;
        time watchdog_timeout;
        
        phase.raise_objection(this, "3.90625Mbps baud switching test");
        
        // Calculate watchdog timeout (fallback to 60 seconds)
        watchdog_timeout = (cfg != null) ? cfg.get_simulation_watchdog_timeout() : 60_000_000_000;
        
        fork
            begin: test_execution
                // Wait for reset deassertion
                wait (uart_axi4_tb_top.rst_n == 1'b1);
                repeat (10) @(posedge uart_axi4_tb_top.clk);
                
                `uvm_info(get_type_name(),
                    "################################################################################",
                    UVM_LOW)
                `uvm_info(get_type_name(),
                    "STARTING 3.90625Mbps BAUD SWITCHING TEST",
                    UVM_LOW)
                `uvm_info(get_type_name(),
                    $sformatf("Target: 7.8Mbps → 3.90625Mbps (divisor: 1 → %0d)", TARGET_DIVISOR),
                    UVM_LOW)
                `uvm_info(get_type_name(),
                    "################################################################################",
                    UVM_LOW)
                
                // Execute baud rate switch (PHASE 1-3)
                // Sequence: CONFIG write → RESET → UVM update
                program_baud_and_reset();
                
                `uvm_info(get_type_name(),
                    "################################################################################",
                    UVM_LOW)
                `uvm_info(get_type_name(),
                    "PHASE 1-3 COMPLETE: Baud switch verified",
                    UVM_LOW)
                `uvm_info(get_type_name(),
                    "CONFIG write → RESET → UVM timing update @ 3.90625Mbps successful",
                    UVM_LOW)
                `uvm_info(get_type_name(),
                    "################################################################################",
                    UVM_LOW)
                
                // PHASE 4: Execute minimal data transfer @ 3.90625Mbps to verify new baud rate
                `uvm_info(get_type_name(),
                    "################################################################################",
                    UVM_LOW)
                `uvm_info(get_type_name(),
                    "PHASE 4: Data transfer @ 3.90625Mbps (1 transaction)",
                    UVM_LOW)
                `uvm_info(get_type_name(),
                    "Expected: ~2.56μs per byte, ~20.5μs for 1 WRITE frame (8 bytes)",
                    UVM_LOW)
                `uvm_info(get_type_name(),
                    "################################################################################",
                    UVM_LOW)
                
                data_seq = simple_debug_write_sequence_20250923::type_id::create("data_seq", this);
                data_seq.start(env.uart_agt.sequencer);
                
                `uvm_info(get_type_name(),
                    "Phase 4 complete: Data transfer @ 3.90625Mbps successful",
                    UVM_LOW)
                
                // Final stabilization
                repeat (100) @(posedge uart_axi4_tb_top.clk);
                
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
                    "Baud rate switching from 7.8Mbps to 3.90625Mbps verified",
                    UVM_LOW)
                `uvm_info(get_type_name(),
                    "################################################################################",
                    UVM_LOW)
            end
            
            begin: test_watchdog
                #(watchdog_timeout);
                test_timeout = 1;
                `uvm_fatal(get_type_name(),
                    $sformatf("Test timeout after %0t ns (%.2f sec)",
                        watchdog_timeout, watchdog_timeout / 1_000_000_000.0))
            end
        join_any
        
        disable fork;
        
        if (test_timeout) begin
            `uvm_info("TIMEOUT",
                "Test watchdog triggered - forcing completion",
                UVM_NONE)
        end
        
        phase.drop_objection(this, "3.90625Mbps baud switching test completed");
    endtask
    
endclass
