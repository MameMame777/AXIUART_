# AXIUART Phase 4 緊急作業指示書

**作成日**: 2025年10月13日  
**対象環境**: DSIM v20240422.0.0 · SystemVerilog UVM 1.2 · Windows PowerShell  
**品質基準**: 実機動作保証レベル · UVM_ERROR完全ゼロ · 偽陽性・見逃しリスク完全排除

---

## 🚨 現状分析 - 確認された問題と解決の必要性

### ✅ 確立された基盤 (Phase 3成果)

- **基本コンパイル**: 全UVM環境エラーなし
- **基本シミュレーション**: `UVM_ERROR = 0` 達成済み
- **Phase 3 Scoreboard**: Correlation Engine統合・動作確認完了
- **波形生成**: MXD形式での安定生成確認
- **Enhanced Reporting**: Report counts by ID機能実装完了

### 🔴 CRITICAL問題群 (即座対応必須)

#### 1. テストファクトリー登録問題

**症状**: `UVM_FATAL: "Requested test not found"`

**影響テスト**:

- uart_axi4_write_protocol_test
- uart_axi4_simple_write_test
- uart_axi4_comprehensive_test
- uart_axi4_burst_perf_test
- uart_axi4_error_injection_test

**根本原因**: UVMファクトリーへの不適切な登録
**緊急度**: CRITICAL (包括的テスト実行の完全阻害)

#### 2. フロー制御シーケンス制約エラー

**症状**: `"Failed to randomize transaction"`
**場所**: `sequences\flow_control_sequences.sv:25`
**根本原因**: 制約競合または矛盾する制約定義
**緊急度**: HIGH (品質保証の前提条件)

#### 3. カバレッジ低迷問題

**現状**:

- Frame coverage: 1.39% - 29.55% (目標: 80%以上)
- Total coverage: 17.13% - 35.89% (目標: 80%以上)

**根本原因**: テストシナリオの不十分な網羅
**緊急度**: MEDIUM-HIGH (見逃しリスクの増大)

#### 4. Frame_Parser RTL信号制御問題

**症状**: 546件のassertion failures (11秒シミュレーション中)
**根本原因**: frame_valid_hold信号のタイミング制御不良
**影響**: UART→AXI変換の完全失敗
**緊急度**: CRITICAL (RTL修正必須)

---

## 🎯 Phase 4 解決計画

### Phase 4.1: 基盤問題完全解決 (2-3日)

#### Task 4.1.1: テストファクトリー登録問題の解決

**目標**: 全テストクラスがUVMファクトリーで正常認識される

**実行内容**:

1. **欠落テストクラスの完全実装**

```systemverilog
// tests/uart_axi4_write_protocol_test.sv
class uart_axi4_write_protocol_test extends enhanced_uart_axi4_base_test;
    
    `uvm_component_utils(uart_axi4_write_protocol_test)
    
    function new(string name = "uart_axi4_write_protocol_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        configure_test_specific_reporting();
        cfg.num_transactions = 50;
        cfg.enable_protocol_checking = 1'b1;
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        uart_axi4_write_protocol_sequence write_seq;
        phase.raise_objection(this);
        
        wait(cfg.bridge_status_vif.rst_n);
        #1000ns;
        
        write_seq = uart_axi4_write_protocol_sequence::type_id::create("write_seq");
        write_seq.start(env.uart_agt.sequencer);
        
        #5000000ns;
        phase.drop_objection(this);
    endtask
    
endclass
```

2. **dsim_config.fファイルへの追加**

```text
tests/uart_axi4_write_protocol_test.sv
tests/uart_axi4_simple_write_test.sv
tests/uart_axi4_comprehensive_test.sv
tests/uart_axi4_burst_perf_test.sv
tests/uart_axi4_error_injection_test.sv
```

**完了基準**: 全てのテストが `run_uvm.ps1` で正常認識される

#### Task 4.1.2: フロー制御制約エラーの修正

**目標**: フロー制御テストが正常実行される

**実行内容**:

```systemverilog
// sequences/flow_control_sequences.sv の修正
class flow_control_sequence extends uart_axi4_base_sequence;
    
    `uvm_object_utils(flow_control_sequence)
    
    virtual task body();
        uart_frame_transaction req;
        
        for (int i = 0; i < 10; i++) begin
            `uvm_create_on(req, p_sequencer)
            
            // 段階的制約適用 (競合回避)
            if (!req.randomize() with {
                address_field == 32'h0000_1000 + (i * 4);
                rw_bit == (i % 2);
                size_field == 2;
                length_field == 4;
            }) begin
                `uvm_error("FLOW_CTRL", $sformatf("Randomization failed at iteration %0d", i))
                continue;
            end
            
            `uvm_send(req)
            #5000;
        end
    endtask
    
endclass
```

**完了基準**: `uart_flow_control_test` が正常実行される

#### Task 4.1.3: Frame_Parser RTL修正

**目標**: Assertion failures < 10件/11秒

**実行内容**:

```systemverilog
// rtl/Frame_Parser.sv の修正
always_ff @(posedge clk) begin
    if (rst) begin
        frame_valid_hold <= 1'b0;
    end else begin
        case (state)
            VALIDATE: begin
                if (error_status_reg == STATUS_OK) begin
                    frame_valid_hold <= 1'b1;
                end
            end
            SEND_TO_BRIDGE: begin
                if (frame_consumed) begin
                    frame_valid_hold <= 1'b0;
                end
            end
            default: begin
                frame_valid_hold <= 1'b0;
            end
        endcase
    end
end
```

**完了基準**: 基本テストスイートが100%成功

---

### Phase 4.2: 偽陽性・見逃しリスク完全排除 (3-4日)

#### Task 4.2.1: 三重検証システム実装

**目標**: Triple Verification Systemにより偽陽性・見逃しリスクを完全排除

**実行内容**:

```systemverilog
// env/triple_verification_framework.sv
class triple_verification_framework extends uvm_component;
    
    `uvm_component_utils(triple_verification_framework)
    
    typedef struct {
        bit passed;
        string method;
        string details;
        time timestamp;
    } verification_result_t;
    
    virtual task verify_transaction(uart_frame_transaction tx);
        verification_result_t uvm_result, waveform_result, assertion_result;
        
        // Method 1: UVMスコアボード検証
        uvm_result = verify_by_uvm_scoreboard(tx);
        
        // Method 2: 波形解析検証
        waveform_result = verify_by_waveform_analysis(tx);
        
        // Method 3: RTLアサーション検証
        assertion_result = verify_by_rtl_assertions(tx);
        
        // 三重検証の一致確認
        check_triple_verification_consistency();
    endtask
    
    virtual function void check_triple_verification_consistency();
        if (uvm_result.passed != waveform_result.passed || 
            waveform_result.passed != assertion_result.passed) begin
            
            `uvm_fatal("TRIPLE_VERIFY", $sformatf(
                "Triple verification MISMATCH detected:\n" +
                "UVM: %s, Waveform: %s, Assertion: %s",
                uvm_result.passed ? "PASS" : "FAIL",
                waveform_result.passed ? "PASS" : "FAIL",
                assertion_result.passed ? "PASS" : "FAIL"
            ))
        end
    endfunction
    
endclass
```

#### Task 4.2.2: 否定証明テスト実装

**目標**: エラー検出率95%以上達成

**実行内容**:

```systemverilog
// tests/negative_proof_verification_test.sv
class negative_proof_verification_test extends enhanced_uart_axi4_base_test;
    
    `uvm_component_utils(negative_proof_verification_test)
    
    virtual task test_crc_error_detection_capability();
        uart_frame_transaction error_tx;
        
        // 意図的にCRCエラーを含むフレーム生成
        `uvm_create(error_tx)
        error_tx.randomize();
        error_tx.crc_field = ~error_tx.calculate_correct_crc();
        
        // エラーフレーム送信
        send_error_frame(error_tx);
        
        // エラー検出確認 (10us以内)
        fork
            begin
                wait(error_detector.crc_error_detected);
                `uvm_info("NEG_PROOF", "✓ CRC error correctly detected", UVM_LOW)
            end
            begin
                #10us;
                `uvm_fatal("NEG_PROOF", "CRC error NOT detected - verification environment inadequate")
            end
        join_any
        disable fork;
    endtask
    
endclass
```

**完了基準**: エラー検出率95%以上、偽陽性検出ゼロ確認

---

### Phase 4.3: 完全カバレッジ達成 (3-4日)

#### Task 4.3.1: 全フレームバリエーション実行

**目標**: カバレッジ80%以上達成

**実行内容**:

```systemverilog
// tests/complete_coverage_verification_test.sv
class complete_coverage_verification_test extends enhanced_uart_axi4_base_test;
    
    `uvm_component_utils(complete_coverage_verification_test)
    
    virtual task execute_all_frame_variations();
        uart_frame_transaction req;
        
        // 全4096パターンの実行
        // RW bit: 0,1 × INC bit: 0,1 × Size: 0-3 × Length: 0-255
        for (int rw = 0; rw <= 1; rw++) begin
            for (int inc = 0; inc <= 1; inc++) begin
                for (int size = 0; size <= 3; size++) begin
                    for (int length = 0; length <= 255; length++) begin
                        `uvm_create(req)
                        req.rw_bit = rw[0];
                        req.inc_bit = inc[0];
                        req.size_field = size[1:0];
                        req.length_field = length[7:0];
                        req.address_field = 32'h0000_1000;
                        req.data_field = {rw, inc, size, length};
                        
                        `uvm_send(req)
                        
                        // カバレッジ確認 (目標達成で早期終了可能)
                        if (get_current_coverage() >= 80.0) return;
                        
                        #1000;
                    end
                end
            end
        end
    endtask
    
endclass
```

**完了基準**: Frame coverage 80%以上、全体coverage 80%以上達成

---

### Phase 4.4: 実機レベル検証実装 (4-5日)

#### Task 4.4.1: 波形解析自動化

**目標**: 波形レベル自動解析システム構築

#### Task 4.4.2: タイミング検証システム

**目標**: セットアップ・ホールド時間検証実装

**完了基準**: 実機レベル検証レポート生成

---

### Phase 4.5: 統合検証・最終確認 (3-4日)

#### Task 4.5.1: 統合テストスイート実行

**目標**: 全Phase 4成果の統合・Level 4品質基準達成確認

**実行内容**:

```powershell
# Phase 4統合テスト実行
$CriticalTests = @(
    "uart_axi4_write_protocol_test",
    "uart_flow_control_test", 
    "uart_axi4_error_injection_test",
    "triple_verification_test",
    "negative_proof_verification_test",
    "complete_coverage_verification_test"
)

foreach ($TestName in $CriticalTests) {
    $Result = & .\run_uvm.ps1 -TestName $TestName -Verbosity UVM_MEDIUM
    if ($LASTEXITCODE -ne 0) {
        Write-Error "❌ Test $TestName FAILED"
        exit 1
    }
    Write-Host "✅ Test $TestName PASSED" -ForegroundColor Green
}
```

---

## 📊 Phase 4 成功基準

### Level 4品質基準チェックリスト

#### ✅ Critical問題解決 (必須)

- [ ] テストファクトリー登録問題: 完全解決
- [ ] フロー制御制約エラー: 完全解決
- [ ] Frame_Parser RTL問題: 完全解決
- [ ] 全てのcriticalテストが正常実行

#### ✅ 偽陽性・見逃しリスク排除 (必須)

- [ ] Triple verification system: 実装・動作確認
- [ ] エラー検出率: 95%以上達成
- [ ] 否定証明テスト: 全項目通過
- [ ] 検証環境の感度確認: 完了

#### ✅ カバレッジ目標達成 (必須)

- [ ] Frame coverage: 80%以上達成
- [ ] 全体coverage: 80%以上達成
- [ ] 全フレームバリエーション: テスト完了
- [ ] 全エラーモード: テスト完了

#### ✅ 実機レベル検証 (必須)

- [ ] 波形解析自動化: 実装・動作確認
- [ ] タイミング検証: 実装・動作確認
- [ ] 信号品質評価: 実装・動作確認
- [ ] 実機レベル検証レポート: 生成完了

#### ✅ 統合品質保証 (必須)

- [ ] 全Phase 4テストスイート: 100%通過
- [ ] Level 4品質基準: 全項目達成
- [ ] 品質保証レポート: 生成完了
- [ ] 継続的改善体制: 確立完了

---

## 🚨 緊急実行スケジュール

| Phase | 期間 | 主要成果物 | 完了基準 |
|-------|------|------------|----------|
| **Phase 4.1** | 2-3日 | Critical問題完全解決 | 基本テスト100%成功 |
| **Phase 4.2** | 3-4日 | 偽陽性・見逃し排除 | エラー検出率95%以上 |
| **Phase 4.3** | 3-4日 | カバレッジ80%達成 | 包括的テスト完了 |
| **Phase 4.4** | 4-5日 | 実機レベル検証 | 波形解析自動化 |
| **Phase 4.5** | 3-4日 | 統合検証完了 | Level 4品質達成 |

**合計期間**: 15-20日 (約3-4週間)

---

## 🎯 成功の絶対条件

### 1. 問題の根本解決

症状対処ではなく、根本原因の完全排除を最優先とする

### 2. 偽陽性ゼロトレラント

疑義のある結果は全て再検証し、100%の確信なくしてPASS判定を出さない

### 3. 見逃しリスク完全排除

全てのエラーモードに対する検出能力95%以上を証明する

### 4. 段階的品質向上

Phase 3で確立された基盤を堅実に活用し、段階的に品質を向上させる

---

**この作業指示書に従い、現状の問題点を確実に把握し、有効な解決手段を間違いなく実装することで、実機動作保証レベル(Level 4)の品質達成を確実に実現します。**
