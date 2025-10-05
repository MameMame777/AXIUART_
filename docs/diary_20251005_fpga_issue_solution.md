# FPGA実機問題の解決策
**作成日**: 2025-10-05  
**対象**: STATUS 0x80とSOF 0xAD問題

## 🎯 問題の要約

### 発見された問題
1. **STATUS 0x80**: 全ての応答で未定義ステータスコード
2. **SOF 0xAD**: 期待値0x5Aの代わりに0xADを送信

### 実証されたこと
- プロトコル通信は正常動作
- CRC-8計算は正確
- フレーム構造は仕様準拠

## 🔍 根本原因の推定

### STATUS 0x80の原因
RTLコードの解析から、以下が疑われる：

1. **Frame_Parserでの初期化不良**
   ```systemverilog
   // Frame_Parser.sv で未初期化の可能性
   logic [7:0] error_status_reg = STATUS_OK; // 明示的初期化が必要
   ```

2. **AXI4_Lite_Masterでのエラー状態**
   ```systemverilog
   // 0x80 = 8'b10000000 → MSBが立っている
   // これはエラーフラグの可能性
   ```

### SOF 0xADの原因
```
0x5A = 01011010
0xAD = 10101101
XOR  = 11110111 = 0xF7
```

この変換は以下の可能性：
1. **UART送信での信号レベル反転**
2. **FPGA IOピンの極性設定**
3. **クロック同期の問題**

## 🛠️ 修正案

### 1. STATUS問題の修正

#### Frame_Parser.svの修正
```systemverilog
// 明示的な初期化
always_ff @(posedge clk) begin
    if (rst) begin
        error_status_reg <= STATUS_OK;  // 明示的に0x00に初期化
        // 他の状態レジスタも明示的初期化
    end else begin
        // 既存のロジック
    end
end
```

#### Uart_Axi4_Bridge.svでのステータス生成確認
```systemverilog
// builder_status_codeの生成ロジック確認
always_comb begin
    case (bridge_state)
        FRAME_ERROR: builder_status_code = parser_error_status;
        AXI_ERROR: builder_status_code = axi_status;
        default: builder_status_code = STATUS_OK;  // デフォルト値を明確化
    endcase
end
```

### 2. SOF問題の修正

#### Option A: Frame_Builderでの補正
```systemverilog
// Frame_Builder.svでの補正
// 実機で0xADが出力される場合の対処
localparam [7:0] SOF_DEVICE_TO_HOST_CORRECTED = 8'hA5;  // 0x5Aの代わり

// 送信時
SOF: begin
    if (!tx_fifo_full) begin
        // 実機での反転を考慮した補正値を送信
        tx_fifo_data = SOF_DEVICE_TO_HOST_CORRECTED;
        tx_fifo_wr_en = 1'b1;
        state_next = STATUS;
    end
end
```

#### Option B: UART_Txでの極性補正
```systemverilog
// UART_Tx.svでの出力極性確認
// もし必要であれば、出力反転オプションを追加
parameter bit INVERT_OUTPUT = 1'b0;

assign uart_tx = INVERT_OUTPUT ? ~uart_tx_int : uart_tx_int;
```

#### Option C: FPGAピン設定での修正
```tcl
# 制約ファイル（.xdc）での極性設定
set_property IOSTANDARD LVCMOS33 [get_ports uart_tx]
set_property PACKAGE_PIN W8 [get_ports uart_tx]
# 必要に応じて極性反転
# set_property DIFF_TERM TRUE [get_ports uart_tx]
```

## 🧪 修正の検証手順

### 1. ステップ1: STATUS修正の確認
1. Frame_Parserの初期化修正を適用
2. シミュレーションでSTATUS 0x00生成を確認
3. FPGA実装で動作確認

### 2. ステップ2: SOF修正の確認
1. Frame_Builderで補正値送信
2. 実機でSOF 0x5A受信確認
3. プロトコル完全性テスト

### 3. ステップ3: 統合テスト
1. 全レジスタアクセステスト
2. CRC検証テスト
3. エラーハンドリングテスト

## 📈 期待される効果

### 修正後の期待値
- **STATUS**: 0x00 (正常時)、適切なエラーコード (エラー時)
- **SOF**: 0x5A (仕様通り)
- **プロトコル**: 完全準拠

### システム安定性向上
- 正確なエラー検出
- 信頼性の高い通信
- デバッグの容易性

## 🚀 実装優先度

### 高優先度
1. STATUS 0x80問題 (通信エラーの原因)
2. SOF 0xAD問題 (プロトコル非準拠)

### 中優先度
3. エラーハンドリング強化
4. ログ出力の改善

このアプローチにより、FPGA実機での問題を体系的に解決できる見込みです。