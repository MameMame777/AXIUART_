# UBUS リファレンス分析と再構成提案

## 1. UBUSについて

### 1.1 概要
**UBUS (Universal Bus)** は、Accellera UVM公式リポジトリが提供する統合サンプル検証環境です。UVM方法論のベストプラクティスを示すリファレンス実装として設計されています。

### 1.2 目的
- **UVM学習教材**: UVMアーキテクチャの実践的な実装例を提供
- **再利用可能なVIP**: 汎用バスプロトコル検証用のVerification IP
- **スケーラビリティ実証**: 1 Master/1 Slave から 2 Masters/4 Slaves への拡張可能性

### 1.3 プロトコル仕様
- **アドレス幅**: 16ビット (`[15:0]`)
- **データ幅**: 8ビット (`[7:0]`)
- **トランザクションタイプ**: READ, WRITE, NOP
- **バーストサイズ**: 1, 2, 4, 8バイト可変長
- **アービトレーション**: グラント/リクエスト方式（優先度: Master 0 > Master 1）
- **フロー制御**: `sig_wait`, `sig_bip` (Burst In Progress), `sig_error`

### 1.4 主要特徴
1. **マルチマスター/マルチスレーブ対応**: 動的なトポロジ設定
2. **アドレスマップ管理**: スレーブごとの専用アドレス範囲
3. **完全なUVMフェーズ実装**: build/connect/run/extract/check/report
4. **Objection駆動**: シーケンスベースのテスト制御
5. **スコアボード統合**: メモリトランザクション検証
6. **再利用可能なシーケンスライブラリ**: Read-Modify-Write等の複雑パターン

---

## 2. テストベンチ構造

### 2.1 ディレクトリ構成
```
distrib/examples/integrated/ubus/
├── sv/                          # UVMコンポーネント（再利用可能VIP）
│   ├── ubus_pkg.sv             # パッケージルート
│   ├── ubus_if.sv              # インターフェース定義
│   ├── ubus_transfer.sv        # トランザクションクラス
│   ├── ubus_master_agent.sv    # Masterエージェント
│   ├── ubus_master_driver.sv
│   ├── ubus_master_monitor.sv
│   ├── ubus_master_sequencer.sv
│   ├── ubus_slave_agent.sv     # Slaveエージェント
│   ├── ubus_slave_driver.sv
│   ├── ubus_slave_monitor.sv
│   ├── ubus_slave_sequencer.sv
│   ├── ubus_bus_monitor.sv     # バスレベルモニタ
│   └── ubus_env.sv             # 環境トップ
└── examples/                    # テストベンチインスタンス化
    ├── ubus_tb_top.sv          # トップモジュール
    ├── dut_dummy.v             # DUTダミー（RTL）
    ├── ubus_example_tb.sv      # テストベンチ環境
    ├── ubus_example_scoreboard.sv
    ├── ubus_master_seq_lib.sv
    ├── ubus_example_master_seq_lib.sv
    ├── ubus_slave_seq_lib.sv
    └── test_lib.sv             # テストケース群
```

### 2.2 階層構造

#### レベル1: トップモジュール (`ubus_tb_top.sv`)
```systemverilog
module ubus_tb_top;
  ubus_if vif();                        // インターフェースインスタンス
  dut_dummy dut(...);                   // DUT接続
  
  initial begin
    uvm_config_db#(virtual ubus_if)::set(uvm_root::get(), "*", "vif", vif);
    run_test();                         // UVMテスト起動
  end
  
  // クロック生成 (10ns周期)
  always #5 vif.sig_clock = ~vif.sig_clock;
endmodule
```

**責務**: クロック生成、リセット制御、インターフェース配布

#### レベル2: テストクラス (`test_lib.sv`)
```systemverilog
class ubus_example_base_test extends uvm_test;
  ubus_example_tb ubus_example_tb0;    // TB環境
  
  virtual function void build_phase(uvm_phase phase);
    // トポロジ設定
    uvm_config_db#(int)::set(this, "ubus_example_tb0.ubus0", 
                             "num_masters", 1);
    uvm_config_db#(int)::set(this, "ubus_example_tb0.ubus0", 
                             "num_slaves", 1);
    ubus_example_tb0 = ubus_example_tb::type_id::create("ubus_example_tb0", this);
  endfunction
  
  function void end_of_elaboration_phase(uvm_phase phase);
    // アドレスマップ設定
    ubus_example_tb0.ubus0.set_slave_address_map("slaves[0]", 16'h0000, 16'hFFFF);
  endfunction
endclass
```

**派生テスト例**:
- `test_read_modify_write`: RMWシーケンス実行
- `test_r8_w8_r4_w4`: 混合サイズアクセス
- `test_2m_4s`: 2マスター/4スレーブ構成

#### レベル3: テストベンチ環境 (`ubus_example_tb.sv`)
```systemverilog
class ubus_example_tb extends uvm_env;
  ubus_env ubus0;                      // UBUSコアVIP
  ubus_example_scoreboard scoreboard0; // スコアボード
  
  virtual function void build_phase(uvm_phase phase);
    ubus0 = ubus_env::type_id::create("ubus0", this);
    scoreboard0 = ubus_example_scoreboard::type_id::create("scoreboard0", this);
  endfunction
  
  function void connect_phase(uvm_phase phase);
    // スレーブ0のモニタ → スコアボード接続
    ubus0.slaves[0].monitor.item_collected_port.connect(
      scoreboard0.item_collected_export);
  endfunction
endclass
```

**責務**: VIPインスタンス化、スコアボード接続、デフォルトシーケンス設定

#### レベル4: UBUS環境 (`ubus_env.sv`)
```systemverilog
class ubus_env extends uvm_env;
  int num_masters = 0;
  int num_slaves = 0;
  
  ubus_master_agent masters[];
  ubus_slave_agent slaves[];
  ubus_bus_monitor bus_monitor;
  
  virtual function void build_phase(uvm_phase phase);
    // 動的エージェント生成
    masters = new[num_masters];
    foreach(masters[i]) begin
      masters[i] = ubus_master_agent::type_id::create($sformatf("masters[%0d]", i), this);
      masters[i].master_id = i;
    end
    
    slaves = new[num_slaves];
    foreach(slaves[i])
      slaves[i] = ubus_slave_agent::type_id::create($sformatf("slaves[%0d]", i), this);
    
    bus_monitor = ubus_bus_monitor::type_id::create("bus_monitor", this);
  endfunction
  
  function void set_slave_address_map(string slave_name, bit [15:0] start, bit [15:0] end);
    // スレーブアドレスマップ設定
  endfunction
endclass
```

**責務**: マスター/スレーブエージェント動的生成、バスレベルモニタリング

#### レベル5: エージェント (`ubus_master_agent.sv` / `ubus_slave_agent.sv`)
```systemverilog
class ubus_master_agent extends uvm_agent;
  protected int master_id;
  
  ubus_master_driver driver;
  uvm_sequencer#(ubus_transfer) sequencer;
  ubus_master_monitor monitor;
  
  virtual function void build_phase(uvm_phase phase);
    monitor = ubus_master_monitor::type_id::create("monitor", this);
    
    if(get_is_active() == UVM_ACTIVE) begin
      sequencer = uvm_sequencer#(ubus_transfer)::type_id::create("sequencer", this);
      driver = ubus_master_driver::type_id::create("driver", this);
    end
  endfunction
  
  function void connect_phase(uvm_phase phase);
    if(get_is_active() == UVM_ACTIVE)
      driver.seq_item_port.connect(sequencer.seq_item_export);
  endfunction
endclass
```

**責務**: ドライバ/モニタ/シーケンサのカプセル化、アクティブ/パッシブ制御

#### レベル6: ドライバ (`ubus_master_driver.sv`)
```systemverilog
class ubus_master_driver extends uvm_driver #(ubus_transfer);
  virtual ubus_if vif;
  protected int master_id;
  
  virtual task run_phase(uvm_phase phase);
    fork
      get_and_drive();
      reset_signals();
    join
  endtask
  
  virtual protected task get_and_drive();
    forever begin
      seq_item_port.get_next_item(req);
      drive_transfer(req);
      seq_item_port.item_done();
    end
  endtask
  
  virtual protected task drive_transfer(ubus_transfer trans);
    // アービトレーション
    wait_for_grant();
    // アドレスフェーズ
    drive_address_phase(trans);
    // データフェーズ
    drive_data_phase(trans);
  endtask
endclass
```

**責務**: シーケンスアイテムをバス信号に変換、タイミング制御

#### レベル7: モニタ (`ubus_master_monitor.sv`)
```systemverilog
class ubus_master_monitor extends uvm_monitor;
  virtual ubus_if vif;
  uvm_analysis_port #(ubus_transfer) item_collected_port;
  
  virtual task run_phase(uvm_phase phase);
    collect_transactions();
  endtask
  
  virtual protected task collect_transactions();
    forever begin
      ubus_transfer trans;
      // バス信号監視
      @(posedge vif.sig_start);
      trans = ubus_transfer::type_id::create("trans");
      // アドレス/データキャプチャ
      collect_address_phase(trans);
      collect_data_phase(trans);
      // 解析ポート経由で送信
      item_collected_port.write(trans);
    end
  endtask
endclass
```

**責務**: バストランザクション受動的監視、解析ポート経由配信

---

## 3. AXIUART_再構成提案

### 3.1 現状の問題点
1. **Objection不在**: run_phaseでオブジェクション上げていないため時刻0で終了
2. **Agent構造不統一**: `uart_agent`がvifを直接公開せず、`driver.vif`経由のみアクセス可能
3. **シーケンス起動方法**: `start(sequencer)`を使用するが、objection管理が不明確
4. **スコアボード統合**: UART/AXIの相関検証は実装済みだが、ZERO ACTIVITY問題

### 3.2 UBUSベースの再構成

#### ステップ1: Agent構造の標準化
**修正対象**: `sim/uvm/agents/uart/uart_agent.sv`

```systemverilog
// UBUS準拠のエージェント構造
class uart_agent extends uvm_agent;
  uart_driver driver;
  uart_monitor monitor;
  uvm_sequencer#(uart_frame_transaction) sequencer;
  
  // ★ vifを直接公開（UBUS準拠）
  virtual uart_if vif;
  
  virtual function void build_phase(uvm_phase phase);
    monitor = uart_monitor::type_id::create("monitor", this);
    
    if(get_is_active() == UVM_ACTIVE) begin
      sequencer = uvm_sequencer#(uart_frame_transaction)::type_id::create("sequencer", this);
      driver = uart_driver::type_id::create("driver", this);
    end
    
    // ★ 環境から取得したvifを共有
    if(!uvm_config_db#(virtual uart_if)::get(this, "", "vif", vif))
      `uvm_fatal("AGENT", "Virtual interface not found")
  endfunction
  
  function void connect_phase(uvm_phase phase);
    if(get_is_active() == UVM_ACTIVE) begin
      driver.seq_item_port.connect(sequencer.seq_item_export);
      // ★ ドライバ/モニタにvifを配布
      driver.vif = vif;
      monitor.vif = vif;
    end
  endfunction
endclass
```

**利点**:
- `env.uart_agt.vif.clk`でクロック直接アクセス可能
- UBUS構造と一貫性維持

#### ステップ2: Objection駆動のrun_phase実装
**修正対象**: `sim/uvm/tests/uart_axi4_basic_test.sv`

```systemverilog
// UBUSパターン準拠
virtual task run_phase(uvm_phase phase);
  uart_reset_sequence reset_seq;
  uart_debug_simple_write_seq debug_seq;
  
  // ★ CRITICAL: objection BEFORE any delays
  phase.raise_objection(this, "Executing UART-AXI4 basic test");
  
  // クロック安定化待機（objection後に実行）
  repeat (2) @(posedge env.uart_agt.vif.clk);
  
  `uvm_info("BASIC_TEST", "===============================================", UVM_LOW)
  `uvm_info("BASIC_TEST", "     UART-AXI4 BASIC FUNCTIONAL TEST", UVM_LOW)
  `uvm_info("BASIC_TEST", "===============================================", UVM_LOW)
  
  // リセットシーケンス
  reset_seq = uart_reset_sequence::type_id::create("reset_seq");
  reset_seq.reset_cycles = 100;
  reset_seq.start(env.uart_agt.sequencer);
  `uvm_info("BASIC_TEST", "Reset completed", UVM_MEDIUM)
  
  // 機能テスト
  debug_seq = uart_debug_simple_write_seq::type_id::create("debug_seq");
  debug_seq.start(env.uart_agt.sequencer);
  `uvm_info("BASIC_TEST", "Functional test completed", UVM_MEDIUM)
  
  // ★ テスト完了
  phase.drop_objection(this, "Basic test completed");
endtask
```

**UBUSとの差分**:
- UBUS: デフォルトシーケンスを`uvm_config_db`で設定 → 自動実行
- AXIUART: run_phase内で明示的に`start()`呼び出し → **objection必須**

#### ステップ3: デフォルトシーケンス方式の採用（オプション）
**UBUS方式の完全採用**:

```systemverilog
// test_lib.sv内
class uart_axi4_basic_test extends enhanced_uart_axi4_base_test;
  virtual function void build_phase(uvm_phase phase);
    // ★ シーケンスを設定で指定（UBUSパターン）
    uvm_config_db#(uvm_object_wrapper)::set(this,
      "env.uart_agt.sequencer.run_phase", 
      "default_sequence",
      uart_basic_sequence::type_id::get());  // 自動実行されるシーケンス
    
    super.build_phase(phase);
  endfunction
  
  // ★ run_phaseは不要（デフォルトシーケンスが自動実行）
endclass
```

**利点**:
- テストクラスがシンプル化（run_phase不要）
- シーケンス切り替えが設定のみで可能
- **objection管理をシーケンス内で完結**

#### ステップ4: シーケンス内Objection（推奨）
**修正対象**: `sim/uvm/sequences/basic_sequences.sv`

```systemverilog
class uart_basic_sequence extends uart_base_sequence;
  `uvm_object_utils(uart_basic_sequence)
  
  virtual task body();
    uvm_phase phase;
    
    // ★ UBUS slave_memory_seqパターン準拠
    phase = get_starting_phase();
    if (phase != null) begin
      phase.raise_objection(this, "uart_basic_sequence executing");
    end
    
    // リセット
    `uvm_do_with(req, { req.cmd == CMD_RESET; })
    
    // ライト
    `uvm_do_with(req, { 
      req.cmd == CMD_WRITE;
      req.addr == 32'h1000;
    })
    
    // リード
    `uvm_do_with(req, { 
      req.cmd == CMD_READ;
      req.addr == 32'h1000;
    })
    
    if (phase != null) begin
      phase.drop_objection(this, "uart_basic_sequence completed");
    end
  endtask
endclass
```

**UBUSのsimple_response_seqパターン**:
```systemverilog
// 参考: ubus_slave_seq_lib.sv
forever begin
  p_sequencer.addr_ph_port.peek(util_transfer);
  uvm_test_done.raise_objection(this);  // ★ アイテムごとにobjection
  `uvm_do_with(req, ...)
  uvm_test_done.drop_objection(this);
end
```

#### ステップ5: スコアボード統合の見直し
**現状**: `uart_axi4_scoreboard.sv`が相関エンジン実装済み

**UBUS参考点**:
- `ubus_example_scoreboard.sv`: メモリモデル内蔵
- `item_collected_export`経由でトランザクション受信
- `write()`メソッドで即時検証

**提案**: 現状維持（既に高度な実装）、ZERO ACTIVITY問題はobjection修正で解決

---

## 4. 実装優先順位

### Phase 1: 緊急修正（即座に実行）
1. **`uart_axi4_basic_test.sv`**: run_phase冒頭に`phase.raise_objection()`追加
2. **検証**: テストが時刻0で終了せず、トランザクション実行を確認

### Phase 2: 構造改善（次回リファクタリング）
3. **`uart_agent.sv`**: vif公開化（UBUS準拠）
4. **全テストクラス**: objection位置の見直し

### Phase 3: 高度化（将来拡張）
5. **デフォルトシーケンス方式**: テストクラス簡素化
6. **シーケンスライブラリ拡充**: UBUS的な再利用可能パターン

---

## 5. 具体的修正コード

### 修正1: uart_axi4_basic_test.sv (緊急)
```systemverilog
virtual task run_phase(uvm_phase phase);
  uart_reset_sequence reset_seq;
  uart_debug_simple_write_seq debug_seq;
  
  // ★★★ CRITICAL FIX ★★★
  phase.raise_objection(this, "Executing reset and functional test");
  
  // クロック安定化
  repeat (2) @(posedge env.uart_agt.driver.vif.clk);  // 現状の経路
  
  `uvm_info("BASIC_TEST", "===============================================", UVM_LOW)
  
  // ... (既存のシーケンス実行コード)
  
  // ★★★ CRITICAL FIX ★★★
  phase.drop_objection(this, "Test completed");
endtask
```

### 修正2: uart_agent.sv (構造改善)
```systemverilog
class uart_agent extends uvm_agent;
  uart_driver driver;
  uart_monitor monitor;
  uvm_sequencer#(uart_frame_transaction) sequencer;
  
  // ★ NEW: vif直接公開
  virtual uart_if vif;
  
  virtual function void build_phase(uvm_phase phase);
    if(!uvm_config_db#(virtual uart_if)::get(this, "", "vif", vif))
      `uvm_fatal("UART_AGENT", "Virtual interface not configured")
    
    monitor = uart_monitor::type_id::create("monitor", this);
    
    if(cfg.is_active == UVM_ACTIVE) begin
      sequencer = uvm_sequencer#(uart_frame_transaction)::type_id::create("sequencer", this);
      driver = uart_driver::type_id::create("driver", this);
    end
  endfunction
  
  function void connect_phase(uvm_phase phase);
    if(cfg.is_active == UVM_ACTIVE) begin
      driver.seq_item_port.connect(sequencer.seq_item_export);
      // ★ vif配布
      driver.vif = vif;
    end
    monitor.vif = vif;
  endfunction
endclass
```

---

## 6. まとめ

| 項目 | UBUS構造 | AXIUART_現状 | 推奨アクション |
|------|---------|-------------|--------------|
| **Objection** | シーケンス内 or テスト内で明示的 | ❌ 未実装 | ✅ run_phase先頭に追加 |
| **Agent vif** | 直接公開 | ❌ driver経由のみ | ⚠️ 将来的に統一 |
| **シーケンス起動** | デフォルトシーケンス設定 | 明示的start()呼び出し | △ 現状維持可 |
| **スコアボード** | シンプルなメモリチェック | ✅ 高度な相関エンジン | ✅ 現状維持 |
| **テスト構造** | base_test → 派生テスト | ✅ 同様の階層 | ✅ 現状維持 |

**今すぐ実行すべき修正**: `uart_axi4_basic_test.sv`のrun_phaseにobjection追加のみ。
