# UART-AXI4-Lite Bridge プロトコル違反診断レポート
日付: 2025年10月6日  
ボーレート: 9600 baud (デバッグ用)

## 🚨 確認されたプロトコル違反

### 1. SOF (Start of Frame) 違反
- **期待値**: `0x5A` (プロトコル仕様)
- **実際値**: `0xAD` 
- **ビットパターン**: `01011010` → `10101101`
- **XOR**: `0xF7` (7ビット変化)

### 2. CMD_ECHO 違反  
- **期待値**: `0x20` (Write command)
- **実際値**: `0x48`
- **ビットパターン**: `00100000` → `01001000` 
- **XOR**: `0x68` (3ビット変化: bit[3,5,6])

### 3. STATUS 違反
- **期待値**: `0x00` (成功)
- **実際値**: `0x80`, `0x83` (未定義エラーコード)
- **プロトコル仕様**: 0x00-0x08のみ定義

## 🔍 RTL コード解析結果

### Frame_Builder.sv
```systemverilog
// 正しい定数定義
localparam [7:0] SOF_DEVICE_TO_HOST = 8'h5A;

// 以前の「修正」コード（現在は無効化）
localparam [7:0] SOF_CORRECTION_MASK = 8'hF7;
localparam [7:0] SOF_DEVICE_TO_HOST_CORRECTED = SOF_DEVICE_TO_HOST ^ SOF_CORRECTION_MASK;

// 現在の送信コード（正常）
tx_fifo_data = SOF_DEVICE_TO_HOST;  // 0x5A を送信
```

**結論**: Frame_Builderは正しく`0x5A`を送信している

### Uart_Tx.sv
```systemverilog
// 標準的なUART送信実装
tx_shift_reg <= tx_data;                      // データロード
uart_tx_int = tx_shift_reg[0];                // LSB first
tx_shift_reg_next = {1'b0, tx_shift_reg[7:1]}; // 右シフト
```

**結論**: Uart_Txの実装は正常

### Uart_Axi4_Bridge.sv
```systemverilog
// captured_cmdロジック（Phase 4で修正済み）
captured_cmd <= parser_cmd;           // フレーム受信時にキャプチャ
builder_cmd_echo = captured_cmd;      // 正しいCMD_ECHOを渡す
```

**結論**: CMD_ECHO ロジックは修正済み

## 💡 ビットパターン分析

### 変換パターンの特徴
1. **固定マスクではない**: SOF(0xF7), CMD_ECHO(0x68)など異なるXORパターン
2. **bit[7]が最頻出**: 4回中3回変化（最も不安定）
3. **独立したビット反転**: 各データで異なる変化パターン

### 検証済み仮説
- ❌ 固定XORマスクによる修正
- ❌ プロトコル実装エラー  
- ❌ CMD_ECHOロジックエラー（Phase 4で修正済み）

## 🎯 推定根本原因

### 最有力候補: UART 送信経路のハードウェア問題

1. **タイミング/クロック問題**
   - セットアップ/ホールド時間違反
   - クロックドメイン境界でのメタステーブル
   - 9600 baudでの特殊な同期問題

2. **FIFO データ破損**
   - TX FIFOの読み書きタイミング
   - データ格納時のビット反転
   - メモリ/レジスタの不安定性

3. **ピン/I/O 設定問題**
   - UART TXピンの電気的特性
   - ドライブ強度/スルーレート設定
   - Zybo Z7-20ハードウェア固有の問題

## 📋 次の診断ステップ

### Phase 5: ハードウェア詳細診断

1. **ILA による UART TX 詳細観測**
   ```
   - tx_fifo_data (Frame_Builder出力)
   - tx_data (UART TX入力)  
   - uart_tx (実際のピン出力)
   - クロック/リセット信号品質
   ```

2. **異なる条件での再現性確認**
   ```
   - 115200 baud での同様パターン確認
   - 異なるデータパターンでの変換確認
   - 単発バイト送信での問題再現
   ```

3. **ハードウェア設定見直し**
   ```
   - Vivado制約ファイル (.xdc) のUARTピン設定
   - I/O標準 (LVCMOS33) の確認
   - タイミング制約の検証
   ```

4. **代替ハードウェアでの確認**
   ```
   - 別のUSB-UARTアダプタでの接続テスト
   - オシロスコープによる信号品質測定
   - 異なるボードでの動作確認
   ```

## 🔧 暫定的回避策

現在のプロトコル違反を一時的に回避するため、以下のオプションを検討：

1. **受信側での逆変換実装**
   - PythonスクリプトでRX時に0xAD→0x5A変換
   - 0x48→0x20 CMD_ECHO修正
   - プロトコルテスト継続のための一時的措置

2. **RTLでの予防的修正**
   - 送信時に逆XORを適用
   - ハードウェア問題への対症療法
   - 根本解決後に除去予定

## 📊 調査継続計画

この問題は**ハードウェア実装固有の深い問題**である可能性が高く、
段階的な詳細診断により根本原因を特定し、最終的な解決策を実装する。