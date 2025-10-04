# FPGAハードウェア診断結果とPMOD仕様チェック

## 🔍 現在の状況まとめ

### Pythonスクリプト実行結果
- ❌ **完全無応答**: FPGAから一切の応答なし
- ⚠️  **LEDが点灯しない**: スクリプト実行時にLEDが点灯しない報告

### RTL仕様確認 (AXIUART_Top.sv)

#### UARTピン配置
```systemverilog
// UART interface (external connections)
input  logic        uart_rx,        // UART受信 (PCから受信)
output logic        uart_tx,        // UART送信 (PCへ送信)
output logic        uart_rts_n,     // Request to Send (active low)
input  logic        uart_cts_n      // Clear to Send (active low)
```

#### フロー制御の実装
```systemverilog
// RTS制御ロジック - アクティブロー
uart_rts_n <= rx_fifo_full || rx_fifo_high || !bridge_enable;
```

## 🚨 問題の可能性分析

### 1. FPGAレベルの問題 (最も可能性高)

#### A. ファームウェア未書き込み/破損
- **症状**: 
  - LEDが全く点灯しない
  - 完全無応答状態
  - CTS/DSR信号が反応しない

- **確認方法**:
  ```
  □ FPGA Configuration LEDの状態確認
  □ DONE LEDの点灯確認
  □ Vivadoでの書き込み状況確認
  ```

#### B. クロック供給問題
- **可能性**: 
  - 外部クロック未供給
  - 内部クロック分配不良
  - PLLロック失敗

#### C. リセット状態固定
- **可能性**: 
  - リセット信号がアサートされ続けている
  - リセット回路の不良

### 2. ハードウェア接続問題

#### A. UART信号配線
現在のピンアサインメント確認が必要：
```
Signal      | FPGA Pin | PMOD Pin | 機能
------------|----------|----------|------------------
uart_rx     | ?        | ?        | PCからの受信 (TX)
uart_tx     | ?        | ?        | PCへの送信 (RX)
uart_rts_n  | ?        | ?        | RTS制御
uart_cts_n  | ?        | ?        | CTS入力
GND         | ?        | ?        | 基準電位
```

#### B. PMOD仕様確認事項
PMODコネクタの標準的な配置：
```
PMOD 4-Wire UART 一般的配置:
Pin 1: TXD (FPGA TX -> PC RX)
Pin 2: RXD (FPGA RX <- PC TX)  
Pin 3: RTS (Optional)
Pin 4: CTS (Optional)
Pin 5: GND
Pin 6: VCC (3.3V)
```

⚠️ **接続要確認**: TXとRXのクロス接続が正しいか

### 3. 電気的仕様問題

#### A. 電圧レベル
- **FPGA**: 3.3V CMOS
- **USB-UART**: 通常3.3V (FTDI FT232R)
- **確認**: 信号レベルの互換性

#### B. 信号方向
- **確認必要**: 
  - FPGA TX → USB-UART RX
  - FPGA RX ← USB-UART TX
  - 相互のGND接続

## 💡 診断手順

### Phase 1: FPGA基本状態確認
```
1. 電源LED確認
2. Configuration完了LED確認  
3. リセットボタン状態確認
4. 外部クロック供給確認
```

### Phase 2: ファームウェア確認
```
1. Vivadoプロジェクトでの書き込み状況
2. Bitstreamの生成・書き込み実行
3. JTAGによる動作確認
```

### Phase 3: ピンアサインメント確認
```
1. 制約ファイル (.xdc) の確認
2. PMOD仕様との照合
3. 信号方向の確認
```

### Phase 4: ハードウェア配線確認
```
1. テスター/マルチメーターでの導通確認
2. オシロスコープでの信号確認
3. 電圧レベル測定
```

## 🎯 即座に実行すべき確認項目

### 最優先 (ハードウェア)
1. **FPGAボード上のLED状態**: 電源・動作・configuration
2. **USB接続状態**: しっかり接続されているか
3. **ファームウェア書き込み状態**: Vivadoで最新版が書き込まれているか

### 次優先 (ソフトウェア)
1. **制約ファイル確認**: ピンアサインメントが正しいか
2. **プロジェクト再ビルド**: 最新のRTLで再synthesis/implementation
3. **PMOD仕様との照合**: 信号配置が正しいか

## 📋 結論

現在の症状（LEDも点灯しない、完全無応答）から判断すると、**ソフトウェア（Python）の問題ではなく、ハードウェアレベルの根本的な問題**です。

**通信規格の問題より前に、FPGAが正常に動作していない可能性が高い**です。

次のステップ：
1. FPGA実機の状態確認（LED、電源、configuration）
2. ファームウェアの書き込み状況確認
3. 必要に応じて再書き込み実行