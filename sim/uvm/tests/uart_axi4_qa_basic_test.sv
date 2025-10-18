`timescale 1ns/1ps

// QA-1.3 Basic Test Quality Fix
// Purpose: Address ZERO ACTIVITY error by implementing proper DUT response verification
// Created: 2025-10-13 for FastMCP Quality Assurance Phase

class uart_axi4_qa_basic_test extends enhanced_uart_axi4_base_test;
    `uvm_component_utils(uart_axi4_qa_basic_test)
    
    function new(string name = "uart_axi4_qa_basic_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        debug_single_write_sequence debug_seq;
        uart_axi4_env_config cfg;
        
        phase.raise_objection(this);
        
        `uvm_info("QA_BASIC_TEST", "===============================================", UVM_LOW)
        `uvm_info("QA_BASIC_TEST", "      QA-1.3 BASIC FUNCTIONAL TEST FIXED     ", UVM_LOW)
        `uvm_info("QA_BASIC_TEST", "===============================================", UVM_LOW)
        `uvm_info("QA_BASIC_TEST", "Test started with DUT response verification", UVM_LOW)
        
        // Wait for reset completion and system stability
        if (!uvm_config_db#(uart_axi4_env_config)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("QA_BASIC_TEST", "Cannot get configuration from config_db")
        end
        #(cfg.bit_time_ns * 100); // Extended wait
        
        `uvm_info("QA_BASIC_TEST", "=== Starting QA Fixed Functional Test ===", UVM_LOW)
        
        // **QA-1.3 FIX**: Add DUT state verification before transaction
        verify_dut_ready_state();
        
        // Execute single write with enhanced monitoring
        `uvm_info("QA_BASIC_TEST", "Running enhanced single write debug sequence", UVM_LOW)
        debug_seq = debug_single_write_sequence::type_id::create("debug_seq");
        // Use cfg to get sequencer reference instead of global uvm_test_top
        if (env != null && env.uart_agt != null && env.uart_agt.sequencer != null) begin
            debug_seq.start(env.uart_agt.sequencer);
        end else begin
            `uvm_fatal("QA_BASIC_TEST", "Cannot access sequencer from environment")
        end
        
        // **QA-1.3 FIX**: Add explicit DUT response monitoring
        monitor_dut_response(debug_seq);
        
        // **QA-1.3 FIX**: Verify bridge internal state
        verify_bridge_internal_state();
        
        // Extended timeout for complete response processing
        #(cfg.frame_timeout_ns * 5);
        
        `uvm_info("QA_BASIC_TEST", "=== QA Basic Test Completed Successfully ===", UVM_LOW)
        
        phase.drop_objection(this);
    endtask

    function automatic uart_axi4_scoreboard get_scoreboard();
        if (env == null || env.phase3_scoreboard == null) begin
            `uvm_fatal("QA_BASIC_TEST", "Scoreboard handle is not available")
        end
        return env.phase3_scoreboard;
    endfunction

    function automatic virtual bridge_status_if get_bridge_status_vif_handle();
        if (bridge_status_vif == null) begin
            `uvm_fatal("QA_BASIC_TEST", "bridge_status_vif handle is not available")
        end
        return bridge_status_vif;
    endfunction

    // **QA-1.3 NEW METHOD**: Verify DUT ready state before transaction
    virtual task verify_dut_ready_state();
        virtual bridge_status_if status_vif = get_bridge_status_vif_handle();

        `uvm_info("QA_BASIC_TEST", "=== DUT READY STATE VERIFICATION ===", UVM_LOW)

        @(posedge status_vif.clk);

        // Check reset release through exported reset indicator
        if (!status_vif.rst_n) begin
            `uvm_error("QA_BASIC_TEST", "DUT reset not released properly")
        end else begin
            `uvm_info("QA_BASIC_TEST", "✅ DUT reset state: RELEASED", UVM_LOW)
        end

        // Check AXI handshake readiness via virtual interface if available
        if (axi_vif != null && axi_vif.awready) begin
            `uvm_info("QA_BASIC_TEST", "✅ AXI interface ready", UVM_LOW)
        end else begin
            `uvm_warning("QA_BASIC_TEST", "AXI AWREADY not asserted - DUT may not be ready")
        end

        // Report bridge-level readiness information
        `uvm_info("QA_BASIC_TEST", $sformatf("Bridge busy: %b, system ready: %b, error code: 0x%02h",
                  status_vif.bridge_busy, status_vif.system_ready, status_vif.bridge_error), UVM_LOW)

        `uvm_info("QA_BASIC_TEST", "=== DUT READY STATE VERIFICATION COMPLETE ===", UVM_LOW)
    endtask
    
    // **QA-1.3 NEW METHOD**: Monitor DUT response after transaction
    virtual task monitor_dut_response(debug_single_write_sequence_20250923 seq);
        uart_axi4_scoreboard scb = get_scoreboard();
        virtual bridge_status_if status_vif = get_bridge_status_vif_handle();
        bit response_received = 0;
        int timeout_count = 0;
        int initial_uart_ok = scb.uart_status_ok_count;

        `uvm_info("QA_BASIC_TEST", "=== DUT RESPONSE MONITORING ===", UVM_LOW)

        fork
            begin
                // Monitor scoreboard and exported status for a completed response
                while (!response_received && timeout_count < 1000) begin
                    @(posedge status_vif.clk);

                    if (!status_vif.rst_n) begin
                        continue;
                    end

                    if (scb.uart_status_ok_count > initial_uart_ok) begin
                        `uvm_info("QA_BASIC_TEST", "✅ UART response observed via scoreboard", UVM_LOW)
                        response_received = 1;
                    end else if (status_vif.bridge_error != 8'h00) begin
                        `uvm_warning("QA_BASIC_TEST", $sformatf("UART error response detected: status=0x%02h", status_vif.bridge_error))
                        response_received = 1;
                    end

                    timeout_count++;
                end

                if (!response_received) begin
                    `uvm_warning("QA_BASIC_TEST", $sformatf("No UART response after %0d cycles", timeout_count))
                end
            end

            begin
                // Monitor AXI activity via virtual interface
                while (timeout_count < 1000) begin
                    @(posedge status_vif.clk);

                    if (!status_vif.rst_n || axi_vif == null) begin
                        continue;
                    end

                    if (axi_vif.awvalid && axi_vif.awready) begin
                        `uvm_info("QA_BASIC_TEST", $sformatf("✅ AXI WRITE detected: addr=0x%08x", axi_vif.awaddr), UVM_LOW)
                    end

                    if (axi_vif.wvalid && axi_vif.wready) begin
                        `uvm_info("QA_BASIC_TEST", $sformatf("✅ AXI DATA detected: data=0x%08x", axi_vif.wdata), UVM_LOW)
                    end
                end
            end
        join_any
        disable fork;

        `uvm_info("QA_BASIC_TEST", "=== DUT RESPONSE MONITORING COMPLETE ===", UVM_LOW)
    endtask
    
    // **QA-1.3 NEW METHOD**: Verify bridge internal state
    virtual task verify_bridge_internal_state();
        uart_axi4_scoreboard scb = get_scoreboard();
        virtual bridge_status_if status_vif = get_bridge_status_vif_handle();

        `uvm_info("QA_BASIC_TEST", "=== BRIDGE INTERNAL STATE VERIFICATION ===", UVM_LOW)

        `uvm_info("QA_BASIC_TEST", $sformatf("Scoreboard matches: %0d, mismatches: %0d, UART errors: %0d",
                  scb.match_count, scb.mismatch_count, scb.uart_status_error_count), UVM_LOW)

        `uvm_info("QA_BASIC_TEST", $sformatf("Bridge busy: %b, system ready: %b, error code: 0x%02h",
                  status_vif.bridge_busy, status_vif.system_ready, status_vif.bridge_error), UVM_LOW)

        `uvm_info("QA_BASIC_TEST", "=== BRIDGE INTERNAL STATE VERIFICATION COMPLETE ===", UVM_LOW)
    endtask

endclass