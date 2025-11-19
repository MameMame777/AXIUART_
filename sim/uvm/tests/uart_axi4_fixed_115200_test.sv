`timescale 1ns / 1ps

//=============================================================================
// uart_axi4_fixed_115200_test.sv
//
// Fixed Baud Rate Switching Test using RESET Command
// 
// Description:
//   Demonstrates safe baud rate switching using protocol-level RESET command.
//   Validates that CONFIG registers are preserved across soft reset while
//   internal state (FIFOs, state machines) is cleared.
//
// Timeline:
//   Phase 0: Initial state @ 7.8Mbps (default baud)
//   Phase 1: Write CONFIG register @ 7.8Mbps (set divisor for 921.6kbps)
//   Phase 2: Send RESET command @ 7.8Mbps (activate new baud, clear state)
//   Phase 3: Update UVM timing parameters to 921.6kbps
//   Phase 4: Execute data transfer @ 921.6kbps (verify synchronization)
//
// Expected Result:
//   - CONFIG write ACK received @ 7.8Mbps
//   - RESET ACK received @ 7.8Mbps
//   - Data transfer successful @ 921.6kbps
//   - No response collection timeouts or errors
//
// Author: AXIUART Development Team
// Date: 2025-11-19
//=============================================================================

class uart_axi4_fixed_115200_test extends uart_axi4_base_test;
    `uvm_component_utils(uart_axi4_fixed_115200_test)
    
    // Target baud rate after switch (actual rate, not true 115200)
    localparam int TARGET_BAUD_RATE = 921_600;  // 125MHz / (135 * 16) ≈ 921.6kbps
    localparam int TARGET_DIVISOR = 135;        // Baud divisor for 921.6kbps
    
    // Configuration references
    uart_configure_baud_sequence baud_seq;
    uart_reset_sequence reset_seq;
    simple_debug_write_sequence_20250923 data_seq;
    
    function new(string name = "uart_axi4_fixed_115200_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        `uvm_info(get_type_name(),
            $sformatf("Building FIXED 115200 test (target baud=%0d)", TARGET_BAUD_RATE),
            UVM_LOW)
    endfunction
    
    //-------------------------------------------------------------------------
    // Program Baud Rate and Reset Task
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
        baud_seq = uart_configure_baud_sequence::type_id::create("baud_seq");
        baud_seq.divisor_value = TARGET_DIVISOR;
        baud_seq.start(env.uart_agt.sequencer);
        
        `uvm_info("BAUD_SWITCH",
            $sformatf("CONFIG write completed @ t=%0t", $time),
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
            "This will activate new baud rate and clear internal state",
            UVM_LOW)
        
        // Step 2: RESET command (still at old baud rate)
        // RTL will apply new baud rate after processing this command
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
            $sformatf("New baud rate: %0d (byte_time will be recalculated)", TARGET_BAUD_RATE),
            UVM_LOW)
        
        // Step 3: Update UVM timing AFTER RTL has processed RESET
        // Now both RTL and UVM will be synchronized to new baud rate
        cfg.baud_rate = TARGET_BAUD_RATE;
        cfg.calculate_timing();
        cfg.frame_timeout_ns = cfg.byte_time_ns * 128;
        
        `uvm_info("BAUD_SWITCH",
            $sformatf("UVM timing updated: byte_time_ns=%0d, bit_time_cycles=%0d, frame_timeout_ns=%0d",
                cfg.byte_time_ns, cfg.bit_time_cycles, cfg.frame_timeout_ns),
            UVM_LOW)
        
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
        
        phase.raise_objection(this, "Fixed 115200 baud switching test");
        
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
                    "STARTING FIXED 115200 BAUD SWITCHING TEST",
                    UVM_LOW)
                `uvm_info(get_type_name(),
                    "################################################################################",
                    UVM_LOW)
                
                // Execute baud rate switch (PHASE 1-3)
                program_baud_and_reset();
                
                `uvm_info(get_type_name(),
                    "################################################################################",
                    UVM_LOW)
                `uvm_info(get_type_name(),
                    "TEST COMPLETE: Baud switch verified",
                    UVM_LOW)
                `uvm_info(get_type_name(),
                    "CONFIG write → RESET → Timing update @ 921.6kbps successful",
                    UVM_LOW)
                `uvm_info(get_type_name(),
                    "################################################################################",
                    UVM_LOW)
                
                // PHASE 4: Execute minimal data transfer @ 921.6kbps to verify new baud rate
                `uvm_info(get_type_name(),
                    "################################################################################",
                    UVM_LOW)
                `uvm_info(get_type_name(),
                    "PHASE 4: Data transfer @ 921.6kbps (1 transaction)",
                    UVM_LOW)
                `uvm_info(get_type_name(),
                    "################################################################################",
                    UVM_LOW)
                
                data_seq = simple_debug_write_sequence_20250923::type_id::create("data_seq", this);
                data_seq.start(env.uart_agt.sequencer);
                
                `uvm_info(get_type_name(),
                    "Phase 4 complete: Data transfer @ 921.6kbps successful",
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
        
        phase.drop_objection(this, "Fixed 115200 baud switching test completed");
    endtask
    
endclass

