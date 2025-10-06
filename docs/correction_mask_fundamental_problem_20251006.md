# 🚨 補正マスク方式の根本的問題分析

**発見日時**: 2025年10月6日  
**問題**: 補正マスク方式は対症療法であり、根本解決になっていない

---

## ❌ **現在の間違ったアプローチ**

### 💊 **対症療法: 補正マスク**
```systemverilog
// Frame_Builder.sv の間違った実装
localparam [7:0] SOF_CORRECTION_MASK = 8'h31;     // 0x5A ^ 0x31 = 0x6B ≠ 0x2D
localparam [7:0] STATUS_CORRECTION_MASK = 8'h60;  // 0x00 ^ 0x60 = 0x60 ≠ 0x6C  
localparam [7:0] CMD_CORRECTION_MASK = 8'h19;     // 0x20 ^ 0x19 = 0x39 ≠ 0xD6

// 実際の出力
tx_fifo_data = status_reg ^ STATUS_CORRECTION_MASK;  // 0x00 ^ 0x60 = 0x60
tx_fifo_data = cmd_reg ^ CMD_CORRECTION_MASK;        // 0x20 ^ 0x19 = 0x39
```

### 🔍 **実測値との不整合**
```
期待値 (補正マスク):  SOF=0x6B, STATUS=0x60, CMD_ECHO=0x39
実測値:              SOF=0x2D, STATUS=0x6C, CMD_ECHO=0xD6
```

**補正マスクでは実測値を説明できない！**

---

## ✅ **正しいアプローチ: 根本原因解決**

### 🎯 **プロトコル仕様準拠**
```systemverilog
// 正しい実装 (補正マスク削除)
localparam [7:0] SOF_DEVICE_TO_HOST = 8'h5A;    // プロトコル仕様通り
localparam [7:0] STATUS_OK = 8'h00;             // プロトコル仕様通り

// 正しい出力
tx_fifo_data = SOF_DEVICE_TO_HOST;  // 0x5A
tx_fifo_data = STATUS_OK;           // 0x00  
tx_fifo_data = cmd_echo;            // そのまま
```

### 🔍 **実測値0x2D/0x6Cの真の原因**

#### **可能性1: 別の変換処理**
- UART送信部での変換
- CRC計算での干渉
- ビット順序の問題

#### **可能性2: 初期化値の影響**
- レジスタの初期値
- 未初期化信号
- X-state伝播

#### **可能性3: ハードウェア層の問題**
- FPGA設定ファイル問題
- ビットストリーム不整合
- 論理合成エラー

---

## 🚀 **修正アクションプラン**

### 📝 **Phase 1: 補正マスク完全削除**
1. **Frame_Builder.sv**: 全補正マスク削除
2. **定数をプロトコル仕様値に変更**
3. **変換処理を削除**

### 🔍 **Phase 2: 実測値の根本原因特定**
1. **修正後の実測値確認**
2. **0x2D/0x6Cの発生源特定**
3. **信号トレース実行**

### ✅ **Phase 3: プロトコル仕様準拠確認**
1. **SOF=0x5A, STATUS=0x00の確認**
2. **完全プロトコル準拠テスト**
3. **レジスタ書き込み機能の動作確認**

---

## 🎯 **期待される結果**

**修正前**: SOF=0x2D, STATUS=0x6C (謎の値)  
**修正後**: SOF=0x5A, STATUS=0x00 (プロトコル仕様値)  

**これにより、レジスタ書き込みも正常動作する可能性が高い。**