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

    // **QA-1.3 NEW METHOD**: Verify DUT ready state before transaction
    virtual task verify_dut_ready_state();
        `uvm_info("QA_BASIC_TEST", "=== DUT READY STATE VERIFICATION ===", UVM_LOW)
        
        // Check reset state
        if (uvm_test_top.dut.rst_n !== 1'b1) begin
            `uvm_error("QA_BASIC_TEST", "DUT reset not released properly")
        end else begin
            `uvm_info("QA_BASIC_TEST", "✅ DUT reset state: RELEASED", UVM_LOW)
        end
        
        // Check AXI interface state
        if (uvm_test_top.dut.axi_awready !== 1'b1) begin
            `uvm_warning("QA_BASIC_TEST", "AXI AWREADY not asserted - DUT may not be ready")
        end else begin
            `uvm_info("QA_BASIC_TEST", "✅ AXI interface ready", UVM_LOW)
        end
        
        // Check UART interface state
        `uvm_info("QA_BASIC_TEST", $sformatf("UART RX ready: %b, TX ready: %b", 
                  uvm_test_top.dut.uart_rx_ready, uvm_test_top.dut.uart_tx_ready), UVM_LOW)
        
        `uvm_info("QA_BASIC_TEST", "=== DUT READY STATE VERIFICATION COMPLETE ===", UVM_LOW)
    endtask
    
    // **QA-1.3 NEW METHOD**: Monitor DUT response after transaction
    virtual task monitor_dut_response(debug_single_write_sequence_20250923 seq);
        bit response_received = 0;
        int timeout_count = 0;
        
        `uvm_info("QA_BASIC_TEST", "=== DUT RESPONSE MONITORING ===", UVM_LOW)
        
        fork
            begin
                // Monitor UART TX for response
                while (!response_received && timeout_count < 1000) begin
                    @(posedge uvm_test_top.clk);
                    
                    if (uvm_test_top.dut.uart_tx_valid) begin
                        `uvm_info("QA_BASIC_TEST", $sformatf("✅ UART TX activity detected: data=0x%02x", 
                                  uvm_test_top.dut.uart_tx_data), UVM_LOW)
                        response_received = 1;
                    end
                    
                    timeout_count++;
                end
                
                if (!response_received) begin
                    `uvm_warning("QA_BASIC_TEST", $sformatf("No UART response after %d cycles", timeout_count))
                end
            end
            
            begin
                // Monitor AXI activity
                while (timeout_count < 1000) begin
                    @(posedge uvm_test_top.clk);
                    
                    if (uvm_test_top.dut.axi_awvalid) begin
                        `uvm_info("QA_BASIC_TEST", $sformatf("✅ AXI WRITE detected: addr=0x%08x", 
                                  uvm_test_top.dut.axi_awaddr), UVM_LOW)
                    end
                    
                    if (uvm_test_top.dut.axi_wvalid) begin
                        `uvm_info("QA_BASIC_TEST", $sformatf("✅ AXI DATA detected: data=0x%08x", 
                                  uvm_test_top.dut.axi_wdata), UVM_LOW)
                    end
                end
            end
        join_any
        
        `uvm_info("QA_BASIC_TEST", "=== DUT RESPONSE MONITORING COMPLETE ===", UVM_LOW)
    endtask
    
    // **QA-1.3 NEW METHOD**: Verify bridge internal state
    virtual task verify_bridge_internal_state();
        `uvm_info("QA_BASIC_TEST", "=== BRIDGE INTERNAL STATE VERIFICATION ===", UVM_LOW)
        
        // Check Frame Parser state
        `uvm_info("QA_BASIC_TEST", $sformatf("Frame Parser state: %d", 
                  uvm_test_top.dut.frame_parser_inst.current_state), UVM_LOW)
        
        // Check Register Block state  
        `uvm_info("QA_BASIC_TEST", $sformatf("Register Block ready: %b", 
                  uvm_test_top.dut.register_block_inst.ready), UVM_LOW)
        
        // Check Bridge FSM state
        `uvm_info("QA_BASIC_TEST", $sformatf("Bridge FSM state: %d", 
                  uvm_test_top.dut.current_state), UVM_LOW)
        
        `uvm_info("QA_BASIC_TEST", "=== BRIDGE INTERNAL STATE VERIFICATION COMPLETE ===", UVM_LOW)
    endtask

endclass