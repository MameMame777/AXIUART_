`timescale 1ns / 1ps

// Basic Functional Test for UART-AXI4 Bridge
class uart_axi4_basic_test extends uart_axi4_base_test;
    
    `uvm_component_utils(uart_axi4_basic_test)
    
    function new(string name = "uart_axi4_basic_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Configure test-specific settings
        uvm_config_db#(int)::set(this, "*", "recording_detail", UVM_FULL);
        
        // UVMレポート機能の設定
        begin
            uvm_report_server server = uvm_report_server::get_server();
            server.set_max_quit_count(1);  // エラー1個で終了
        end
        
        `uvm_info("BASIC_TEST", "Basic functional test configured with enhanced reporting", UVM_LOW)
    endfunction
    
    virtual function void start_of_simulation_phase(uvm_phase phase);
        super.start_of_simulation_phase(phase);
        
        `uvm_info("BASIC_TEST", "========================================", UVM_NONE)
        `uvm_info("BASIC_TEST", "    UART-AXI4 BASIC FUNCTIONAL TEST     ", UVM_NONE)
        `uvm_info("BASIC_TEST", "========================================", UVM_NONE)
        `uvm_info("BASIC_TEST", "Test started with comprehensive UVM reporting", UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        uart_axi4_basic_sequence basic_seq;
        uart_axi4_read_sequence read_seq;
        uart_axi4_write_sequence write_seq;
        uart_axi4_burst_sequence burst_seq;
        
        phase.raise_objection(this, "Starting basic test");
        
        // Set reasonable timeout for the test
        phase.phase_done.set_drain_time(this, 1000ns);
        
        `uvm_info("BASIC_TEST", "=== Starting Basic Functional Test ===", UVM_LOW)
        
        // Wait for reset to complete
        wait (uart_axi4_tb_top.dut.rst == 1'b0);  // Wait for reset to be released
        repeat (10) @(posedge uart_axi4_tb_top.dut.clk);
        
        // Run basic functionality sequence
        `uvm_info("BASIC_TEST", "Running basic functionality sequence", UVM_MEDIUM)
        basic_seq = uart_axi4_basic_sequence::type_id::create("basic_seq");
        basic_seq.num_transactions = 15;
        basic_seq.test_reads = 1;
        basic_seq.test_writes = 1;
        basic_seq.start(env.uart_agt.sequencer);
        
        // Wait between sequences
        repeat (50) @(posedge uart_axi4_tb_top.dut.clk);
        
        // Run dedicated write sequence
        `uvm_info("BASIC_TEST", "Running write sequence", UVM_MEDIUM)
        write_seq = uart_axi4_write_sequence::type_id::create("write_seq");
        write_seq.num_writes = 8;
        write_seq.base_addr = 32'h1000;
        write_seq.start(env.uart_agt.sequencer);
        
        // Wait between sequences
        repeat (50) @(posedge uart_axi4_tb_top.dut.clk);
        
        // Run dedicated read sequence to read back written data
        `uvm_info("BASIC_TEST", "Running read sequence", UVM_MEDIUM)
        read_seq = uart_axi4_read_sequence::type_id::create("read_seq");
        read_seq.num_reads = 8;
        read_seq.base_addr = 32'h1000;
        read_seq.start(env.uart_agt.sequencer);
        
        // Wait between sequences
        repeat (50) @(posedge uart_axi4_tb_top.dut.clk);
        
        // Run burst sequence with different data sizes
        `uvm_info("BASIC_TEST", "Running burst sequence", UVM_MEDIUM)
        burst_seq = uart_axi4_burst_sequence::type_id::create("burst_seq");
        burst_seq.start(env.uart_agt.sequencer);
        
        // Final wait
        repeat (100) @(posedge uart_axi4_tb_top.dut.clk);
        
        `uvm_info("BASIC_TEST", "=== Basic Functional Test Completed ===", UVM_LOW)
        
        phase.drop_objection(this, "Basic test completed");
    endtask
    
    virtual function void final_phase(uvm_phase phase);
        super.final_phase(phase);
        
        // Print comprehensive test summary
        `uvm_info("BASIC_TEST", "=== COMPREHENSIVE TEST SUMMARY ===", UVM_LOW)
        `uvm_info("BASIC_TEST", $sformatf("Scoreboard Matches: %0d", env.scoreboard.match_count), UVM_LOW)
        `uvm_info("BASIC_TEST", $sformatf("Scoreboard Mismatches: %0d", env.scoreboard.mismatch_count), UVM_LOW)
        
        if (env.scoreboard.mismatch_count == 0) begin
            `uvm_info("BASIC_TEST", "*** TEST PASSED ***", UVM_LOW)
        end else begin
            `uvm_error("BASIC_TEST", "*** TEST FAILED ***")
        end
    endfunction
    
    // UVM最終レポート機能 - UVMフェーズの一部として自動実行される
    virtual function void report_phase(uvm_phase phase);
        uvm_report_server server = uvm_report_server::get_server();
        int error_count, warning_count, info_count, fatal_count;
        
        super.report_phase(phase);
        
        // UVMレポートサーバーから統計情報を取得
        fatal_count = server.get_severity_count(UVM_FATAL);
        error_count = server.get_severity_count(UVM_ERROR);
        warning_count = server.get_severity_count(UVM_WARNING);
        info_count = server.get_severity_count(UVM_INFO);
        
        `uvm_info("BASIC_TEST", "========================================", UVM_NONE)
        `uvm_info("BASIC_TEST", "           FINAL UVM REPORT             ", UVM_NONE)
        `uvm_info("BASIC_TEST", "========================================", UVM_NONE)
        `uvm_info("BASIC_TEST", $sformatf("Total FATAL messages:   %0d", fatal_count), UVM_NONE)
        `uvm_info("BASIC_TEST", $sformatf("Total ERROR messages:   %0d", error_count), UVM_NONE)
        `uvm_info("BASIC_TEST", $sformatf("Total WARNING messages: %0d", warning_count), UVM_NONE)
        `uvm_info("BASIC_TEST", $sformatf("Total INFO messages:    %0d", info_count), UVM_NONE)
        `uvm_info("BASIC_TEST", "----------------------------------------", UVM_NONE)
        
        // 総合判定
        if (fatal_count > 0 || error_count > 0) begin
            `uvm_info("BASIC_TEST", "❌ OVERALL RESULT: TEST FAILED", UVM_NONE)
            `uvm_info("BASIC_TEST", $sformatf("   - FATAL: %0d, ERROR: %0d", fatal_count, error_count), UVM_NONE)
        end else begin
            `uvm_info("BASIC_TEST", "✅ OVERALL RESULT: TEST PASSED", UVM_NONE)
            `uvm_info("BASIC_TEST", "   - No fatal or error messages detected", UVM_NONE)
        end
        
        `uvm_info("BASIC_TEST", "========================================", UVM_NONE)
    endfunction

endclass