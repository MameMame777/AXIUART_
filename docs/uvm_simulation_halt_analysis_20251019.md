# UVMシミュレーション停止問題の詳細分析

**日付**: 2025年10月19日  
**プロジェクト**: AXIUART_  
**問題**: UVMシミュレーションが876nsで停止、MCPサーバーがタイムアウト

---

## 1. 現状の問題

### 1.1 症状
- **シミュレーション時刻**: 876ns時点で停止
- **MCPサーバー**: 90-120秒後にタイムアウトでDSIMプロセスを強制終了
- **ログ出力**: 876ns以降の出力が一切ない

### 1.2 最後のログ出力
```
@ 876000: uvm_test_top [BASIC_TEST] Sequence created, calling start()
@ 876000: uvm_test_top.env.uart_agt.driver [UART_DRIVER_DEBUG] get_next_it
```

---

## 2. コード構造の分析

### 2.1 テストコード (uart_axi4_basic_test.sv)
```systemverilog
// Line 62-64
debug_seq = simple_debug_write_sequence_20250923::type_id::create("debug_seq");
`uvm_info("BASIC_TEST", "Sequence created, calling start()", UVM_LOW)
debug_seq.start(env.uart_agt.sequencer);  // ここで停止
```

**状態**: `start()`呼び出し後、制御が戻らない

### 2.2 シーケンスコード (debug_single_write_sequence.sv)
```systemverilog
virtual task body();
    `uvm_info("DEBUG_SEQ", "Sequence body() started", UVM_LOW)  // この出力がない
    
    `uvm_create(req)
    
    req.is_write = 1'b1;
    req.auto_increment = 1'b0;
    req.size = 2'b00;
    req.length = 4'h0;
    req.expect_error = 1'b1;
    req.addr = 32'h0000_1000;
    req.data = new[1];
    req.data[0] = 8'h42;
    
    `uvm_send(req)
    `uvm_info("DEBUG_SEQ", "Sequence completed", UVM_LOW)
endtask
```

**状態**: `body()`の最初の`uvm_info`すら出力されていない

### 2.3 ドライバーコード (uart_driver.sv)
```systemverilog
// Line 88-90
`uvm_info("UART_DRIVER_DEBUG", "Calling get_next_item() - waiting for sequence", UVM_LOW)
seq_item_port.get_next_item(req);  // ここで待機中
`uvm_info("UART_DRIVER_DEBUG", "get_next_item() returned - transaction received", UVM_LOW)
```

**状態**: `get_next_item()`で無限待機

### 2.4 UVMコンポーネント接続
```systemverilog
// uart_agent.sv Line 52
driver.seq_item_port.connect(sequencer.seq_item_export);
```

**状態**: 接続は正しい

---

## 3. UVM実行フローの分析

### 3.1 正常な実行フロー
1. テスト: `debug_seq.start(env.uart_agt.sequencer)` 呼び出し
2. UVMフレームワーク: `pre_start()` 実行
3. UVMフレームワーク: `pre_body()` 実行
4. シーケンス: `body()` 実行開始
5. シーケンス: `uvm_create` → `start_item()` 呼び出し
6. セコンサー: アイテムをドライバーのFIFOに追加
7. ドライバー: `get_next_item()` から戻る
8. ドライバー: トランザクション実行
9. ドライバー: `item_done()` 呼び出し
10. シーケンス: `finish_item()` から戻る
11. シーケンス: `body()` 完了
12. テスト: `start()` から戻る

### 3.2 現在の停止ポイント
**停止位置**: ステップ3と4の間（`pre_body()`完了後、`body()`開始前）

---

## 4. MCPサーバーのプロセス管理

### 4.1 現在の実装 (dsim_uvm_server.py)
```python
def _run_subprocess_sync(cmd: List[str], timeout: int, cwd: Path):
    proc = subprocess.Popen(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        cwd=cwd,
        env=os.environ.copy()
    )
    
    start_time = time.time()
    while proc.poll() is None:
        elapsed = time.time() - start_time
        if elapsed > timeout:
            proc.terminate()  # 穏やかな終了を試行
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()  # 強制終了
                proc.wait()
            raise subprocess.TimeoutExpired(cmd, timeout)
        time.sleep(0.1)
    
    stdout, stderr = proc.communicate()
    return subprocess.CompletedProcess(cmd, proc.returncode, stdout, stderr)
```

**動作**:
- 100msごとにプロセス生存確認
- タイムアウト時は`terminate()` → 5秒待機 → `kill()`
- DSIMプロセスが応答しない場合、強制終了

### 4.2 タイムアウト設定
- **コンパイル**: 90秒
- **実行**: 90秒
- **batch実行**: compile 90秒 + run 90秒

---

## 5. 問題の根本原因（仮説）

### 5.1 仮説A: UVMフレームワークの初期化不完全
**根拠**:
- `body()`が全く呼ばれていない
- `pre_body()`で停止している可能性

**検証方法**:
- UVM内部のフェーズ実行ログを有効化
- `+UVM_PHASE_TRACE` plusarg追加

### 5.2 仮説B: シーケンサーとの通信デッドロック
**根拠**:
- ドライバーは`get_next_item()`で待機
- シーケンスは`start()`で待機
- 相互に待ち合わせ状態

**検証方法**:
- sequencerの内部状態確認
- TLM通信ポートのFIFO状態確認

### 5.3 仮説C: DSIMのUVMライブラリ問題
**根拠**:
- `-uvm 1.2` オプション使用
- DSIM固有のUVM実装に問題がある可能性

**検証方法**:
- 別のシミュレーターで同じコードを実行
- DSIM公式サンプルコードで動作確認

---

## 6. ライセンス問題

### 6.1 現在の状態
```
License not obtained: Lease acquisition denied. 
Already at maxLeases (1) for supplied license.
```

**原因**: 前回のDSIMプロセスがライセンスを保持したまま

**対策**: ライセンスサーバーのリース解放待ち（通常30分）

---

## 7. 次の調査手順

### 7.1 即座に実施可能な調査
1. ✅ **ログファイル末尾確認** - 完了（876ns時点で停止確認）
2. ✅ **MCPプロセス管理確認** - 完了（Popen実装に変更済み）
3. ❌ **UVMフェーズトレース有効化** - 未実施
4. ❌ **シーケンサー内部状態確認** - 未実施

### 7.2 ライセンス解放後の調査
1. UVMフェーズトレースを有効化して再実行
2. より詳細なverbosity (`UVM_DEBUG`) で実行
3. 最小構成のテストケース作成

### 7.3 コード修正候補
```systemverilog
// Option 1: 明示的なsequencer確認
virtual task body();
    if (m_sequencer == null) begin
        `uvm_fatal("DEBUG_SEQ", "Sequencer is null")
    end
    `uvm_info("DEBUG_SEQ", $sformatf("Sequencer: %s", m_sequencer.get_full_name()), UVM_LOW)
    
    // 既存のコード
endtask

// Option 2: シーケンスの明示的な開始
debug_seq.start(env.uart_agt.sequencer, null, 0);  // priority=0明示
```

---

## 8. 結論

### 8.1 確実な事実
1. シミュレーションは876nsで停止
2. シーケンスの`body()`は呼ばれていない
3. ドライバーは`get_next_item()`で待機中
4. MCPサーバーは90-120秒後にタイムアウト
5. ライセンスが他で使用中

### 8.2 最も可能性の高い原因
**UVMシーケンスの`start()`メソッドが、`body()`タスクを起動する前の初期化段階でデッドロックしている**

具体的には：
- `pre_body()`フェーズでの無限ループ
- または、sequencerへのアクセス権取得での待機

### 8.3 今後の対応
1. ライセンス解放待ち（30分）
2. UVMフェーズトレース有効化
3. sequencer状態の明示的確認コード追加
4. 最小構成テストでの切り分け

---

## 9. 関連ファイル一覧

| ファイル | パス | 役割 |
|---------|------|------|
| テスト | `sim/uvm/tests/uart_axi4_basic_test.sv` | メインテストケース |
| シーケンス | `sim/uvm/sequences/debug_single_write_sequence.sv` | デバッグ用シーケンス |
| ドライバー | `sim/uvm/agents/uart/uart_driver.sv` | UARTドライバー |
| エージェント | `sim/uvm/agents/uart/uart_agent.sv` | UARTエージェント |
| MCPサーバー | `mcp_server/dsim_uvm_server.py` | DSIMプロセス管理 |
| ログ | `sim/exec/logs/uart_axi4_basic_test_*.log` | 実行ログ |

---

**作成者**: GitHub Copilot  
**最終更新**: 2025年10月19日 10:35
