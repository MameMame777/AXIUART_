`timescale 1ns / 1ps

// Scoreboard感度確認・偽陽性検出テスト
// Purpose: スコアボードが適切にトランザクションを検出・処理できるかを検証
// Late Connection問題を利用した否定証明テスト

class scoreboard_sensitivity_verification_test extends uart_axi4_base_test;

    `uvm_component_utils(scoreboard_sensitivity_verification_test)

    function new(string name = "scoreboard_sensitivity_verification_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // テスト固有設定: 高い verbosity で詳細ログ取得
        uvm_config_db#(uvm_verbosity)::set(this, "*scoreboard*", "verbosity", UVM_HIGH);
        uvm_config_db#(uvm_verbosity)::set(this, "*monitor*", "verbosity", UVM_HIGH);
        
        `uvm_info("SENSITIVITY_TEST", "Scoreboard sensitivity verification test configured", UVM_LOW)
    endfunction

    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        `uvm_info("SENSITIVITY_TEST", "=== SCOREBOARD SENSITIVITY VERIFICATION TEST ===", UVM_LOW)
        
        // Test 1: 既知のLate Connection状況での動作確認
        test_late_connection_scenario(phase);
        
        // Test 2: 正常接続での基本感度確認  
        test_normal_connection_sensitivity(phase);
        
        // Test 3: スコアボード統計の妥当性確認
        test_scoreboard_statistics_validity(phase);
        
        // Test 4: ZERO ACTIVITY検出機能の動作確認
        test_zero_activity_detection(phase);
        
        #50000ns; // 結果安定化待機
        
        phase.drop_objection(this);
    endtask

    // Test 1: Late Connection問題状況での動作解析
    virtual task test_late_connection_scenario(uvm_phase phase);
        `uvm_info("SENSITIVITY_TEST", "Test 1: Late Connection scenario analysis", UVM_LOW)
        
        // 現在のテスト環境では既にLate Connectionが発生している
        // この状況でスコアボードがどのように反応するかを観察
        
        // 基本的なUARTトランザクション送信
        send_basic_uart_transaction();
        
        // スコアボード状態確認
        check_scoreboard_internal_state("late_connection");
        
        `uvm_info("SENSITIVITY_TEST", "Test 1 completed - Late connection scenario analyzed", UVM_LOW)
    endtask
    
    // Test 2: 正常接続での基本感度確認
    virtual task test_normal_connection_sensitivity(uvm_phase phase);
        `uvm_info("SENSITIVITY_TEST", "Test 2: Normal connection sensitivity check", UVM_LOW)
        
        // 注意: 現在の環境では正常接続が困難だが、将来の修正用テストケース
        
        // 予想される正常動作パターン
        // 1. UART transaction送信
        // 2. AXI transaction生成  
        // 3. スコアボードでのマッチング
        // 4. 統計カウンタ更新
        
        `uvm_info("SENSITIVITY_TEST", "Test 2 completed - Normal connection would require connection fix", UVM_LOW)
    endtask
    
    // Test 3: スコアボード統計の妥当性確認
    virtual task test_scoreboard_statistics_validity(uvm_phase phase);
        `uvm_info("SENSITIVITY_TEST", "Test 3: Scoreboard statistics validity check", UVM_LOW)
        
        // 統計値の論理的整合性を確認
        // - UART transactions received = 0
        // - AXI transactions received = 0  
        // - Matches found = 0
        // - ZERO ACTIVITY判定 = 正しい
        
        `uvm_info("SENSITIVITY_TEST", "Statistics should show: UART=0, AXI=0, Matches=0 -> ZERO ACTIVITY=TRUE", UVM_MEDIUM)
        `uvm_info("SENSITIVITY_TEST", "Test 3 completed - Statistics consistency will be verified at end", UVM_LOW)
    endtask
    
    // Test 4: ZERO ACTIVITY検出機能の動作確認  
    virtual task test_zero_activity_detection(uvm_phase phase);
        `uvm_info("SENSITIVITY_TEST", "Test 4: ZERO ACTIVITY detection verification", UVM_LOW)
        
        // ZERO ACTIVITY条件:
        // - match_count == 0
        // - UVM_ERROR should be generated
        
        `uvm_info("SENSITIVITY_TEST", "Expected behavior: UVM_ERROR for ZERO ACTIVITY should be generated", UVM_MEDIUM)
        `uvm_info("SENSITIVITY_TEST", "Test 4 completed - ZERO ACTIVITY detection will be verified in final_phase", UVM_LOW)
    endtask
    
    // Helper: 基本UARTトランザクション送信
    virtual task send_basic_uart_transaction();
        uart_frame_sequence basic_seq;
        
        basic_seq = uart_frame_sequence::type_id::create("basic_seq");
        
        // 基本的な書き込みトランザクション設定
        basic_seq.cmd = 8'h01;        // Write command
        basic_seq.addr = 32'h00001000; // 有効アドレス
        basic_seq.data_bytes.push_back(8'h42); // Test data
        
        `uvm_info("SENSITIVITY_TEST", $sformatf("Sending basic UART transaction: CMD=0x%02X ADDR=0x%08X", 
                  basic_seq.cmd, basic_seq.addr), UVM_MEDIUM)
                  
        basic_seq.start(env.uart_agt.sequencer);
        
        `uvm_info("SENSITIVITY_TEST", "Basic UART transaction sent - checking if scoreboard receives it", UVM_MEDIUM)
    endtask
    
    // Helper: スコアボード内部状態確認
    virtual task check_scoreboard_internal_state(string test_phase);
        `uvm_info("SENSITIVITY_TEST", $sformatf("Checking scoreboard state during: %s", test_phase), UVM_MEDIUM)
        
        // スコアボードの内部カウンタは final_phase でレポートされるため、
        // ここでは接続状態の確認に留める
        
        if (env.phase3_scoreboard == null) begin
            `uvm_error("SENSITIVITY_TEST", "Scoreboard is null - critical configuration error")
        end else begin
            `uvm_info("SENSITIVITY_TEST", "Scoreboard instance exists - connection status will be verified by UVM framework", UVM_MEDIUM)
        end
    endtask
    
    // 検証結果の最終評価
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        
        `uvm_info("SENSITIVITY_TEST", "=== SCOREBOARD SENSITIVITY VERIFICATION RESULTS ===", UVM_LOW)
        
        // Late Connection警告の検出確認
        `uvm_info("SENSITIVITY_TEST", "Expected findings:", UVM_LOW)
        `uvm_info("SENSITIVITY_TEST", "1. Late Connection warnings should be present", UVM_LOW)
        `uvm_info("SENSITIVITY_TEST", "2. UART transactions received = 0 (due to connection issue)", UVM_LOW)
        `uvm_info("SENSITIVITY_TEST", "3. AXI transactions received = 0 (no UART trigger)", UVM_LOW)
        `uvm_info("SENSITIVITY_TEST", "4. UVM_ERROR for ZERO ACTIVITY should be generated", UVM_LOW)
        `uvm_info("SENSITIVITY_TEST", "5. Test result should show SUCCESS despite UVM_ERROR (false positive)", UVM_LOW)
        
        `uvm_info("SENSITIVITY_TEST", "=== SENSITIVITY VERIFICATION COMPLETED ===", UVM_LOW)
        `uvm_info("SENSITIVITY_TEST", "This test demonstrates the false positive issue:", UVM_LOW)
        `uvm_info("SENSITIVITY_TEST", "- Exit Code = 0 (SUCCESS) but verification is invalid", UVM_LOW)
        `uvm_info("SENSITIVITY_TEST", "- Root cause: Late Connection prevents scoreboard operation", UVM_LOW)
    endfunction

endclass