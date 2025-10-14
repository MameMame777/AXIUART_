`timescale 1ns / 1ps

// QA品質検証用の確実動作テスト
class uart_axi4_qa_verification_test extends enhanced_uart_axi4_base_test;

    `uvm_component_utils(uart_axi4_qa_verification_test)
    
    // シンプルなデバッグシーケンス
    debug_single_write_sequence debug_seq;

    function new(string name = "uart_axi4_qa_verification_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // QA検証用設定
        cfg.enable_coverage = 1;
        cfg.enable_scoreboard = 1;
        cfg.enable_protocol_checking = 1;
        
        uvm_config_db#(uart_axi4_env_config)::set(this, "env", "config", cfg);
        `uvm_info("QA_VERIFICATION_TEST", "QA verification test configured", UVM_LOW)
    endfunction

    virtual task main_phase(uvm_phase phase);
        `uvm_info("QA_VERIFICATION_TEST", "=== QA Verification Test Starting ===", UVM_LOW)
        
        phase.raise_objection(this, "QA verification test running");

        // Wait for reset to complete
        wait (uart_axi4_tb_top.dut.rst == 1'b0);
        repeat (10) @(posedge uart_axi4_tb_top.dut.clk);
        
        `uvm_info("QA_VERIFICATION_TEST", "Running verified debug sequence", UVM_MEDIUM)
        
        // 確実に動作するシーケンスを実行
        debug_seq = debug_single_write_sequence::type_id::create("debug_seq");
        if (debug_seq == null) begin
            `uvm_error("QA_VERIFICATION_TEST", "Failed to create debug sequence")
            phase.drop_objection(this, "Sequence creation failed");
            return;
        end
        
        debug_seq.start(env.uart_agt.sequencer);
        
        // システム安定化待ち
        repeat (2000) @(posedge uart_axi4_tb_top.dut.clk);
        
        `uvm_info("QA_VERIFICATION_TEST", "=== QA Verification Test Completed ===", UVM_LOW)
        
        phase.drop_objection(this, "QA verification test completed");
    endtask

endclass