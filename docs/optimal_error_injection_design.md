# RTL仕様に基づいたエラー注入テスト設計書

## 概要
AXIUART RTL実装に基づき、最適なエラー注入テストを設計しました。RTLモジュールの実際のエラー処理機能と検出能力を重点的にテストします。

## RTL分析結果

### Frame Parser (Frame_Parser.sv)
- **CRC検証機能**: CRC8計算（多項式0x07）による完全性チェック
- **タイムアウト検出**: 設定可能なタイムアウト時間での通信中断検出
- **状態機械**: IDLE→CMD→ADDR(4bytes)→DATA→CRC→VALIDATE→ERRORの遷移
- **エラーステータス**: STATUS_CRC_ERR(0x01), STATUS_CMD_INV(0x02), STATUS_ADDR_ALIGN(0x03), STATUS_TIMEOUT(0x04), STATUS_LEN_RANGE(0x07)

### CRC Calculator (Crc8_Calculator.sv)
- **アルゴリズム**: ビット単位処理によるCRC8計算
- **初期値**: 0x00
- **多項式**: 0x07 (x^8 + x^2 + x^1 + 1)
- **リセット**: 同期リセット対応

### Register Block (Register_Block.sv)
- **AXI4-Liteインターフェース**: 標準準拠のレジスタアクセス
- **アドレス範囲**: 0x000-0x100の各種レジスタ
- **書き込みストローブ**: バイト、ハーフワード、ワードアクセス対応
- **エラー応答**: RESP_SLVERR(0x10)による不正アクセス検出

## エラー注入テストカテゴリ

### 1. CRCエラー注入テスト (最重要)
**RTL根拠**: Frame_Parser.svのCRC検証機能
```systemverilog
// CRC計算エラー
if (rx_fifo_data_reg == expected_crc) begin
    error_status_reg <= STATUS_OK;
end else begin
    error_status_reg <= STATUS_CRC_ERR;
end
```
**テスト項目**:
- 1ビットCRCエラー注入
- 複数ビットCRCエラー注入  
- CRC完全反転エラー
- CRC計算中断エラー
- CRCタイミングエラー

### 2. プロトコル違反エラー注入テスト
**RTL根拠**: Frame Parserの状態機械とSOF検証
```systemverilog
if (!rx_fifo_empty && (rx_fifo_data == SOF_HOST_TO_DEVICE)) begin
    state_next = CMD;
end else if (!rx_fifo_empty) begin
    rx_fifo_rd_en = 1'b1;  // Discard invalid SOF
end
```
**テスト項目**:
- 無効SOF（0xA5以外）注入
- フレーム順序違反
- 不正コマンドコード注入
- フレーム長不整合

### 3. タイムアウトエラー注入テスト
**RTL根拠**: Frame_Parserのタイムアウト機能
```systemverilog
localparam int TIMEOUT_CLOCKS = BYTE_TIME_CLOCKS * TIMEOUT_BYTE_TIMES;
if (timeout_occurred) begin
    state_next = ERROR;
end
```
**テスト項目**:
- データ受信中のタイムアウト
- CRC受信待ちタイムアウト
- フレーム開始タイムアウト
- 段階的タイムアウト時間テスト

### 4. AXI4-Liteプロトコルエラー注入テスト
**RTL根拠**: Register_BlockのAXI4-Lite応答機能
```systemverilog
function automatic bit is_wstrb_supported(logic [1:0] addr_lsb, logic [3:0] wstrb);
case (wstrb)
    4'b0001: return (addr_lsb == 2'b00);
    4'b0011: return (addr_lsb == 2'b00);
    4'b1100: return (addr_lsb == 2'b10);
    4'b1111: return (addr_lsb == 2'b00);
    default: return 1'b0;  // RESP_SLVERR応答
endcase
```
**テスト項目**:
- 不正アドレスアクセス
- 無効書き込みストローブパターン
- アライメント違反アクセス
- 不正バースト操作

### 5. FIFO境界エラー注入テスト
**RTL根拠**: Frame ParserのFIFO制御ロジック
```systemverilog
if (!rx_fifo_empty) begin
    rx_fifo_rd_en = 1'b1;
end
```
**テスト項目**:
- FIFOアンダーフローエラー
- FIFOオーバーフローエラー
- FIFO空読み出しエラー
- FIFO満杯書き込みエラー

### 6. データ完全性エラー注入テスト
**RTL根拠**: フレーム構造とデータ検証
**テスト項目**:
- ペイロードデータ破損
- アドレスフィールド破損
- コマンドフィールド破損
- 長さフィールド不整合

## 実装優先度

### Phase 1: 基本エラー検出機能 (最優先)
1. **CRCエラー注入テスト** - RTLの主要検証機能
2. **タイムアウトエラー注入テスト** - 通信断検出
3. **プロトコル違反エラー注入テスト** - SOF/コマンド検証

### Phase 2: 高度なエラー処理 (第二優先)
4. **AXI4-Liteプロトコルエラー注入テスト** - レジスタアクセス
5. **FIFOエラー注入テスト** - バッファ境界
6. **データ完全性エラー注入テスト** - ペイロード検証

## 期待効果

### カバレッジ向上
- **機能カバレッジ**: エラー処理パスの完全検証
- **コードカバレッジ**: エラー分岐の網羅的テスト
- **アサーションカバレッジ**: RTL設計意図の確認

### 品質保証
- **ロバストネス**: 異常条件下での動作確認
- **プロトコル準拠**: 仕様書通りのエラー応答検証
- **障害検出**: 実際のハードウェア問題の早期発見

### 検証完了度
- **エラー検出率**: 100%のエラー検出能力確認
- **応答時間**: エラー検出時間の測定と最適化
- **復旧能力**: エラー後の正常動作復帰確認

この設計により、RTL実装の実際のエラー処理能力を最適にテストし、カバレッジ目標80%以上達成と堅牢性確認を実現します。