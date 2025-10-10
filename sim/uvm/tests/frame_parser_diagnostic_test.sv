`timescale 1ns / 1ps

// Frame Parser診断専用テスト - 指示書 Step 1-1 対応
// 固定値での最小限テストによる captured_cmd=0x00 問題の根本原因特定

class frame_parser_diagnostic_test extends uart_axi4_base_test;
    `uvm_component_utils(frame_parser_diagnostic_test)
    
    function new(string name = "frame_parser_diagnostic_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        simple_debug_write_sequence_20250923 seq;
        
        phase.raise_objection(this);
        
        `uvm_info("DIAG", "========== FRAME PARSER DIAGNOSTIC TEST START ==========", UVM_LOW)
        `uvm_info("DIAG", "Purpose: Isolate captured_cmd=0x00 root cause with fixed values", UVM_LOW)
        
        // 診断用シーケンスを実行
        seq = simple_debug_write_sequence_20250923::type_id::create("diagnostic_seq");
        
        `uvm_info("DIAG", "Starting diagnostic sequence with fixed values", UVM_LOW)
        seq.start(env.uart_agt.sequencer);
        
        `uvm_info("DIAG", "Waiting for sequence completion...", UVM_LOW)
        #10000; // シーケンス完了待ち
        
        // 結果の詳細ログ出力
        check_frame_parser_state();
        
        `uvm_info("DIAG", "========== FRAME PARSER DIAGNOSTIC TEST END ==========", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
    // フレームパーサー状態確認 (テストベンチインターフェース経由で実装予定)
    virtual task check_frame_parser_state();
        `uvm_info("DIAG", "=== FRAME PARSER STATE DIAGNOSTIC ===", UVM_LOW)
        
        // TODO: テストベンチインターフェース経由で以下を確認
        // - parser_frame_error の値
        // - captured_cmd の値 (期待値: 0x01)
        // - parser_error_status の値
        // - Frame Parser FSM の現在状態
        
        `uvm_info("DIAG", "Frame Parser state check implementation needed in testbench", UVM_LOW)
        `uvm_info("DIAG", "Expected: captured_cmd=0x01, parser_frame_error=0", UVM_LOW)
        `uvm_info("DIAG", "Actual values to be read from DUT interface", UVM_LOW)
    endtask
    
endclass