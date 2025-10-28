# uart_axi4_basic_test デバッグ手順（2025-10-28）

## 調査結果概要

- DSIM 20240422.0.0／UVM 1.2 環境で `uart_axi4_basic_test` をコンパイルすると常に成功。
- ランモード（`--mode run --waves --timeout 600`）では 600s でタイムアウトし、UVM_FATAL／ERROR は発生しないが処理が進まない。
- ログ `sim/exec/logs/uart_axi4_basic_test_20251028_092635.log` では UART 受信が SOF 含む 3 バイト分まで進行するが、`[PARSER_VALIDATE]` ログが一度も出ず `Frame_Parser` が `VALIDATE` へ到達しない。
- 波形 `archive/waveforms/uart_axi4_basic_test_20251028_092635.vcd` を確認すると `parser_frame_valid`（記号 `^`）が 0 のままで、`Uart_Axi4_Bridge` の `main_state` も `MAIN_IDLE` に張り付いている。
- `axi_start_transaction`／`builder_build_response`／`parser_frame_consumed` などブリッジ側のハンドシェイク信号は一切トグルせず、AXI 取引が開始されない。

## 想定される原因

- `Frame_Parser` が `ADDR_BYTE1` 以降の状態へ遷移できず停止している可能性（FIFO 読み出し条件や `expected_data_bytes` 計算の不整合）。
- `VALIDATE` に入れていない、もしくは入った瞬間に CRC／コマンド検証で NG 判定され `frame_valid_hold` がセットされない。
- `frame_valid` が立たないことでブリッジ FSM が常に `MAIN_IDLE` に滞留し、`parser_frame_consumed` も発火しないループ。
- CRC やタイムアウト制御のシーケンスが誤っており、CRC バイト受信前に `DATA_RX` → `CRC_RX` へ進めていない。
- 既存デバッグ出力の制限（24 イベント制限など）により真の停止箇所のログが欠落している。

## 解決に向けた対応策

- `Frame_Parser` と `Uart_Axi4_Bridge` の主要信号を追加でダンプし、停止状態を波形で完全に把握する。
- `ADDR`／`DATA` フェーズの `rx_fifo_rd_en`・`rx_fifo_empty`・`data_byte_count` を追跡し、読み出しが継続しているか検証する。
- `VALIDATE` 遷移時に CRC／コマンド判定がどのように評価されているかを詳細ログで確認し、条件式を見直す。
- 必要に応じて CRC リセット／イネーブルのタイミング、`expected_data_bytes` 計算ロジックを修正し、再度シミュレーションでタイムアウト解消を確認する。
- デバッグ強化後も問題が再現する場合は、`Frame_Parser` 単体ベンチで同コマンド (0x00) を入力し再現性を切り分ける。

## 追加ログの仕込み

- `rtl/Frame_Parser.sv` の `parser_state_transition_count` 制限を一時的に外し、状態遷移・`rx_fifo_rd_en`・`rx_fifo_empty`・`expected_data_bytes` を `$display` またはデバッグ信号で観測できるようにする。
- `Frame_Parser` の `frame_valid_hold`、`state`、`data_byte_count`、`expected_crc`、`received_crc` を `$dumpvars` に追加して波形上で追跡できるようにする。
- `rtl/Uart_Axi4_Bridge.sv` の `main_state`、`axi_start_issued`、`builder_start_issued`、`parser_frame_consumed` も `$dumpvars` 対象に追加する。

## シミュレーション実行

- MCP 経由で `python mcp_server/mcp_client.py --tool run_uvm_simulation --test-name uart_axi4_basic_test --mode compile` を実行する。
- 続けて `python mcp_server/mcp_client.py --tool run_uvm_simulation --test-name uart_axi4_basic_test --mode run --waves` を実行し、ログと VCD を取得する。
- 生成された `sim/exec/logs/*.log` と `archive/waveforms/*.vcd` を確認し、`Frame_Parser` がどの状態で停止しているか、CRC 判定や `frame_valid` の挙動を特定する。

## 切り分けと修正

- 状態が `ADDR` フェーズで止まっている場合は、`rx_fifo_rd_en` 条件や `expected_data_bytes` 計算の不整合を修正する。
- `VALIDATE` に入っているのに `frame_valid` が立たない場合は、`cmd_valid` や CRC 判定ロジックを精査して修正する。
- 修正後に再度 `uart_axi4_basic_test` を実行し、タイムアウトが解消されることを確認する。

## フォローアップ

- 問題解消後は追加したデバッグ出力を整理・削除し、AXI 取引完了とレスポンス生成が確認できるログを保存する。
