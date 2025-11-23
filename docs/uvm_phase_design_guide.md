# UVM Phase Design Guide - AXIUART Project

## Critical Rule: Time Consumption
**時間を使うのは `run_phase` のみ。他のphaseでは `@(posedge clk)`, `#delay`, `wait` は厳禁。**

---

## Phase Overview

```
build_phase         → Create components
connect_phase       → Connect ports/interfaces  
end_of_elaboration  → Final checks
start_of_simulation → Pre-simulation setup
run_phase          → ★ ALL TIME-CONSUMING OPERATIONS ★
extract_phase       → Collect results
check_phase         → Pass/Fail判定
report_phase        → Final report
```

---

## 1. build_phase - 「作る（構築）」

### ✅ やるべきこと
- UVMコンポーネントのインスタンス生成 (`::type_id::create()`)
- `config_db` による設定の読み取り
- Factory override設定
- 軽量な初期化（時間を消費しない）

### ❌ してはいけないこと
- 時間待ち (`@(posedge clk)`, `#delay`)
- DUT信号の駆動
- `raise_objection` / `drop_objection`
- ポート接続（`connect_phase`で行う）

### 実装例
```systemverilog
virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);  // MUST call super
    
    // Component creation
    env = uart_env::type_id::create("env", this);
    
    // Configuration
    if (!uvm_config_db#(uart_config)::get(this, "", "cfg", cfg))
        `uvm_fatal("NOCFG", "No config object")
    
    // Pass config to children
    uvm_config_db#(uart_config)::set(this, "env", "config", cfg);
endfunction
```

---

## 2. connect_phase - 「つなぐ（接続）」

### ✅ やるべきこと
- ポートとエクスポートの接続
- Virtual interface の取得・配布
- Sequencer/Driver の接続確認

### ❌ してはいけないこと
- 時間を消費する処理
- Sequenceの開始 (`seq.start()`)
- DUTリセット操作

### 実装例
```systemverilog
virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    
    // Get virtual interface
    if (!uvm_config_db#(virtual uart_if)::get(this, "", "vif", vif))
        `uvm_fatal("NOVIF", "No virtual interface")
    
    // Distribute to driver/monitor
    driver.vif = vif;
    monitor.vif = vif;
    
    // Connect ports
    monitor.analysis_port.connect(scoreboard.analysis_export);
endfunction
```

---

## 3. run_phase - 「実行（時間消費が許される唯一の場所）」

### ✅ やるべきこと
- **すべての時間消費操作** (`@(posedge clk)`, `#delay`, `wait`)
- Sequenceの実行 (`seq.start(sequencer)`)
- `raise_objection` / `drop_objection` による実行制御
- DUTリセット、stimulus生成、結果収集

### ❌ してはいけないこと
- Component生成（`build_phase`で行う）
- `super.run_phase(phase)` の呼び忘れ
- `drop_objection` の呼び忘れ（ハングの原因）
- Phase責務の混在

### 重要な注意点
**`run_phase` は全コンポーネントで並列実行される**
- Driver, Monitor, Scoreboard の `run_phase` が同時に動作
- Deadlock（相互待ち）に注意
- Objection管理は慎重に（複数箇所でraise可能）

### 実装例（Test）
```systemverilog
virtual task run_phase(uvm_phase phase);
    uart_reset_sequence reset_seq;
    uart_test_sequence test_seq;
    
    super.run_phase(phase);  // CRITICAL: Always call first
    
    phase.raise_objection(this, "Executing test");
    
    // Step 1: Reset
    reset_seq = uart_reset_sequence::type_id::create("reset_seq");
    reset_seq.start(env.agent.sequencer);
    
    // Step 2: Test stimulus
    test_seq = uart_test_sequence::type_id::create("test_seq");
    test_seq.start(env.agent.sequencer);
    
    phase.drop_objection(this, "Test completed");
endtask
```

### 実装例（Driver）
```systemverilog
virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    
    forever begin
        seq_item_port.get_next_item(req);  // Blocks until sequence provides item
        drive_transaction(req);             // Contains @(posedge clk), #delays
        seq_item_port.item_done();
    end
endtask
```

---

## 4. extract_phase - 「結果抽出」

### ✅ やるべきこと
- Run完了後の統計集計
- カウンタ・測定値の最終計算
- 結果の整理（時間を消費しない）

### ❌ してはいけないこと
- 時間待ち
- 再シミュレーション

---

## 5. check_phase - 「チェック（合否判定）」

### ✅ やるべきこと
- スコアボードの最終判定
- 期待値vs実測値の比較
- `uvm_error` / `uvm_fatal` の発行

### ❌ してはいけないこと
- 時間待ち
- 大規模I/O

---

## 6. report_phase - 「報告」

### ✅ やるべきこと
- 最終レポート出力
- サマリ生成
- 外部ツールへの結果送信

### ❌ してはいけないこと
- Run中の処理の代替
- `uvm_fatal` による遅延停止

---

## Common Mistakes Checklist

- [ ] run_phase以外で `@(posedge clk)` を使っていないか？
- [ ] `drop_objection` を必ず呼んでいるか？
- [ ] `super.<phase>(phase)` を呼んでいるか？
- [ ] Virtual interfaceがnullでないか確認しているか？
- [ ] Run_phaseで相互待ち（deadlock）になっていないか？

---

## Debug Tips

### Hang時の確認手順
1. `+UVM_VERBOSITY=UVM_DEBUG` でフェーズ進行ログ取得
2. Objection trace確認: `+UVM_OBJECTION_TRACE`
3. Phase trace確認: `+UVM_PHASE_TRACE`
4. Run_phaseの各所に `uvm_info` を配置して進行確認
5. 最小テストで段階的に機能追加して原因切り分け

### Objection Debugging
```systemverilog
// Objection状態を常時監視
phase.raise_objection(this, "Starting test");
`uvm_info("OBJECTION", $sformatf("Raised objection - count=%0d", 
          phase.get_objection_count(this)), UVM_LOW)

// ... processing ...

phase.drop_objection(this, "Test completed");
`uvm_info("OBJECTION", $sformatf("Dropped objection - count=%0d", 
          phase.get_objection_count(this)), UVM_LOW)
```

---

## AXIUART Project-Specific Notes

### Current Implementation
- **Test**: Uses `run_phase` for reset + functional test (CORRECT)
- **Driver**: Uses `run_phase` for transaction execution (CORRECT)
- **Monitor**: Uses `run_phase` for signal monitoring (CORRECT)

### Previous Issues (RESOLVED)
❌ **WRONG**: Using `reset_phase` for reset sequence + `main_phase` for test
- Problem: Phase ordering caused deadlock between driver and sequence
- Solution: Moved all to `run_phase` for proper synchronization

### Design Pattern
```systemverilog
// Test's run_phase executes:
// 1. Reset sequence → driver receives reset transaction
// 2. Test sequence → driver receives test transactions
// All synchronized within same phase context
```

---

## References
- IEEE 1800.2-2017 UVM Standard
- UVM Cookbook: Phase Execution Order
- Accellera UVM Class Reference
