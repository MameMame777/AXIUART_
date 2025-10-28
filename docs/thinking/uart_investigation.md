Read [](file:///e%3A/Nautilus/workspace/fpgawork/AXIUART_/sim/uvm/sequences)

Read [](file:///e%3A/Nautilus/workspace/fpgawork/AXIUART_/sim/uvm/sequences/debug_sequences.sv)

Ran terminal command: Select-String -Path "e:/Nautilus/workspace/fpgawork/AXIUART_/sim/uvm/**" -Pattern "simple_debug_write_sequence_20250923"

Ran terminal command: Select-String -Path "e:/Nautilus/workspace/fpgawork/AXIUART_/sim/uvm/**/*.sv" -Pattern "class simple_debug_write_sequence"

Read [](file:///e%3A/Nautilus/workspace/fpgawork/AXIUART_/sim/uvm/sequences/debug_single_write_sequence.sv)

Ran terminal command: Select-String -Path "e:/Nautilus/workspace/fpgawork/AXIUART_/sim/uvm/agents/uart/uart_driver.sv" -Pattern "break"

**解析結果**
- 実行ログでは `drive_frame` が SOF(0xA5)、CMD(0x00) の 2 バイト送信後に停止しており、3 バイト目（アドレス LSB）以降の `UART_DRIVER_BYTE_FORCED` ログ・`BRIDGE_RX` ログが出力されていません。`collect_response_from_fifo` やハンドシェイク監視までは進んでいないため、現状のタイムアウトは「UART ドライバがフレーム中盤で停止→パーサが次バイトを待ち続ける」ことが直接要因です。
- RTL の `Uart_Axi4_Bridge` は `parser_frame_valid` を待って `MAIN_AXI_TRANSACTION` に遷移し、`axi_start_transaction`→`axi_transaction_done`→`builder_response_complete` で応答を組み立てる設計になっています。今回の停止位置は `parser_frame_valid` 以前なので、状態機械や `axi*`／`builder_*` 信号はまだ動いていません。RTL 側に入ってくるバイト列が途中で止まる限り、ブリッジ側を掘っても進展は望めません。

---

**UVM テストベンチ構造ドキュメント**

```markdown
# UVM Testbench Architecture for AXIUART_

## 1. トップレベル (`sim/uvm/tb/uart_axi4_tb_top.sv`)
- DUT: `AXIUART_Top`（内部で `Uart_Axi4_Bridge`, `Register_Block`, UART RX/TX 等を包含）。
- インタフェース:
  - `uart_if` (driver/modport, monitor/modport, dut/modport)。`uvm_config_db` 経由でテストへ提供。
  - `bridge_status_if` (DUT ステータス観測)。
  - `axi4_lite_if` (DUT 内部 AXI-Lite をモニタリング専用でエクスポート)。
- プラス引数:
  - `SIM_TIMEOUT_NS/US/MS`, `UART_BASIC_VERBOSE`, `NOWAVES`, `WAVEFILE` 等。
  - `tb_parse_timeout_plusargs()` で DSIM ガードタイムを算出し、`uvm_root::get().set_timeout()` と独自監視用に使用。
- 波形:
  - 既定で MXD を有効化。`+NOWAVES` で抑止。
- リセット／クロック:
  - `CLK_PERIOD = 8ns` (125 MHz)。
  - `RESET_CYCLES = 40` クロックの同期リセット。

## 2. パッケージ (`sim/uvm/packages/uart_axi4_test_pkg.sv`)
- `uvm_analysis_imp_decl` で UART/AXI/DUT 用 analysis imp を事前宣言。
- `uart_axi4_env_config`（詳細は env/config/）を `typedef` し、env/agent と共有。
- 主要 typedef/const:
  - UART/AXI トランザクション列挙、SOF 定数、ステータスコード。
  - `uart_frame_transaction`（CRC 計算 `calculate_crc()` を内包）、`axi4_lite_transaction`、`dut_internal_transaction`。
- インクルード順:
  1. `env/uart_axi4_coverage.sv`
  2. `scoreboard/correlation_engine.sv`, `env/uart_axi4_scoreboard.sv`
  3. `agents/axi4_lite/axi4_lite_monitor.sv`, `monitors/bridge_status_monitor.sv`
  4. `agents/uart/uart_driver.sv`, `agents/uart/uart_monitor.sv`, `agents/uart/uart_agent.sv`
  5. `env/uart_axi4_env.sv`
  6. シーケンス各種
  7. テスト (`tests/…`)
- 依存関係をパッケージ内で完結させており、`import uart_axi4_test_pkg::*;` で全テストがビルド可能。

## 3. 環境 (`sim/uvm/env/uart_axi4_env.sv`)
- 構成 (`uart_axi4_env_config`):
  - クロック／ボーレート、`frame_timeout_ns`, `min/max_idle_cycles`, `enable_*` フラグ。
  - `calculate_timing()` で `bit_time_ns`, `byte_time_ns`, `frame_timeout_ns` を算出。
- ビルド:
  - UART エージェント（常設）、AXI モニタ（`enable_axi_monitor` 時）、スコアボード、カバレッジ、ステータスモニタを条件生成。
  - `uvm_config_db` に VIF と CFG を配布。
- コネクト:
  - UART モニタ → `phase3_scoreboard.uart_analysis_imp`／カバレッジ。
  - UART ドライバ `tx_request_ap` → スコアボード期待値入力。
  - AXI モニタ → スコアボード (`axi_analysis_imp`)。
- レポート:
  - `report_phase` で簡易ログ。

## 4. エージェント
### 4.1 UART Agent (`sim/uvm/agents/uart/uart_agent.sv`)
- `cfg.uart_agent_is_active` に応じてドライバ＋シーケンサ生成。
- モニタからの `item_collected_port` を `uvm_tlm_analysis_fifo` に接続し、ドライバへのレスポンス経路として使用。
- ログ: `UART_AGENT_DBG`, `UART_AGENT_FIFO_FORCE` など。

### 4.2 UART Driver (`sim/uvm/agents/uart/uart_driver.sv`)
- `run_phase`:
  - `get_next_item`→`drive_frame`→レスポンス取得（FIFO または直接サンプリング）。
  - `drive_frame` で SOF→CMD→ADDR→DATA→CRC を逐次送出。バイトごとに watchdog (`drive_uart_byte`) を併設。
- 重要メソッド:
  - `flush_monitor_responses()`：送信前に FIFO を空にする。
  - `drive_uart_byte()`：開始ビット・8データビット・停止ビットを `bit_time_cycles` クロック単位で生成し、完了ログを `UART_DRIVER_BYTE_STATE`/`BYTE_FORCED` で出力。
  - `collect_response_from_fifo()`：モニタ解析結果を待つ。`guard_timeout_ns = frame_timeout_ns` でガード。
- 現象:
  - 最新ログでは `drive_frame` が 2 バイト送出した時点で停止しており、後続バイトのログが存在しない。

### 4.3 UART Monitor (`sim/uvm/agents/uart/uart_monitor.sv`)
- `collect_rx_transactions()`：
  - UART ラインを直接観測し、SOF 検出後にバイト列を `calculate_expected_frame_length()` で評価。
  - 成功時に `item_collected_port.write()` で配信（方向は `UART_RX`）。
- `collect_tx_transactions()`：
  - DUT 送信（`UART_TX`）を同様にキャプチャ。
- RTS/CTS 監視タスクを併走し、`UVM_INFO` ログを出力。

### 4.4 AXI Monitor (`sim/uvm/agents/axi4_lite/axi4_lite_monitor.sv`)
- DUT 内部 AXI-Lite バスを観測、`uart_axi4_enhanced_scoreboard` 等へストリーム。

## 5. スコアボード (`sim/uvm/scoreboard/uavrt_axi4_enhanced_scoreboard.sv`)
- Analysis Imp: UART, AXI, DUT 内部状態。
- トランザクション追跡:
  - `active_responses[string]` マップで UART→AXI→UART 応答のタイミング紐付け。
- アクティビティ監視:
  - 無動作検出、タイムアウト監視 (`activity_timeout_threshold` デフォルト 1ms)。
- DUT 状態遷移検証:
  - `check_dut_state_transition()` で不正遷移を `UVM_ERROR`。

## 6. シーケンス
- `simple_debug_write_sequence_20250923`（`debug_single_write_sequence.sv`）:
  - 手動で `uart_frame_transaction` を構築（WRITE, addr=0x1000, data=0x42）。
  - `build_cmd()` と `calculate_crc()` を呼び出し、1 トランザクションのみ送信。
  - 応答が無い場合は `UVM_FATAL("DEBUG_SEQ_TIMEOUT")`。
- その他、`basic_func_sequence.sv` や `uart_axi4_*` 系列が多数存在。今回のテストはデバッグ用シンプルシーケンスのみ使用。

## 7. テスト階層
- `uart_axi4_base_test`:
  - CFG の初期化、VIF 取得、環境生成、`test_scenario`／波形設定。
  - `configure_test()` でクロック/ボーレート/タイムアウト/監視を設定。
- `enhanced_uart_axi4_base_test`:
  - レポーティング標準化 (`configure_default_reporting` で verbosity / action 設定)。
- `uart_axi4_basic_test`:
  - `+UART_BASIC_VERBOSE` で詳細ログ切替。
  - `run_phase` でデバッグシーケンスを単発実行。
  - 手動ハンドシェイク監視（`axi_transaction_done`, `builder_response_complete`, `parser_frame_consumed`）とタイムアウトガード（`handshake_timeout_ns`）。
```

---

**追加観察 (RTL)**
- `Uart_Axi4_Bridge`:
  - `MAIN_IDLE`⇒`MAIN_AXI_TRANSACTION`⇒`MAIN_BUILD_RESPONSE`⇒`MAIN_WAIT_RESPONSE` の 4 段 FSM。
  - `parser_frame_valid` を見て `captured_cmd/addr` を更新、AXI/Builder の開始1サイクル幅パルスは `axi_start_transaction = !axi_start_issued`, `builder_build_response = !builder_start_issued`。
  - `parser_frame_error` の場合は `MAIN_BUILD_RESPONSE` でエラー応答を組み立て、`builder_response_complete` 待ち。
  - `parser_frame_valid` が来なければ `axi_*` は一切動作しないため、現在の停止点では RTL には未到達。
- `Frame_Parser`:
  - SOF (0xA5) 検出後に CMD→ADDR4バイト→データ→CRC を順次読み出し、CRC チェック後に `frame_valid` を発行。
  - `expected_data_bytes` は CMD 内容から算出。WRITE で SIZE=00, LEN=0 の場合は 1 バイトデータを期待。
- `Frame_Builder` / `Axi4_Lite_Master` は今回のハング地点では呼ばれていない（ハンディング信号なし）。

---

**結論とフォローアップ**
- タイムアウト延長は効果が無く、根因は「UART ドライバが 3 バイト目以降を送出できていない」ことにある。`drive_frame` 内で何が停止を引き起こしているか（例: `@(posedge vif.clk)` で進まない、ランダム待機の範囲不整合、他タスクとの同期競合など）を追跡する必要がある。
- 次の調査候補:
  1. `drive_frame` 内の `repeat ($urandom_range(cfg.min_idle_cycles, cfg.max_idle_cycles))` が想定外の引数 (`min > max` など) を受け取っていないか確認。
  2. `drive_uart_byte` の watchdog が発火していないか（`UART_DRIVER_BYTE_TIMEOUT` が抑止されていないか）をログで確認・必要に応じてアサーション追加。
  3. `vif.clk` が 2 バイト目完了後も動作しているかを `driver` 側で記録（`@(posedge vif.clk)` ループにデバッグカウンタ追加）。
  4. `uart_if` の `uart_cts_n`／`uart_rts_n` のハンドシェイクがドライバ停止に影響していないかを `uart_monitor` と突き合わせる。

この解析を踏まえ、次はドライバのステップ実行や追加ログ挿入で停止原因を特定します。