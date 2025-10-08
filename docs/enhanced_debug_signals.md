# Enhanced Debug Signals for Write Enable Triggering

## 問題の分析
`write_enable`信号でトリガーされない問題に対して、包括的なデバッグ信号を追加しました。

## 追加されたデバッグ信号

### 🎯 **基本制御信号**
```systemverilog
(* mark_debug = "true" *) wire write_enable;           // メイン書き込み有効信号
(* mark_debug = "true" *) wire read_enable;            // 読み込み有効信号
(* mark_debug = "true" *) wire axi_state_write_data;   // WRITE_DATA状態フラグ
```

### 🤝 **AXI4-Liteハンドシェイク信号**
```systemverilog
(* mark_debug = "true" *) wire aw_handshake;           // アドレス書き込みハンドシェイク
(* mark_debug = "true" *) wire w_handshake;            // データ書き込みハンドシェイク
(* mark_debug = "true" *) wire ar_handshake;           // アドレス読み込みハンドシェイク
```

### 📡 **AXI4-Lite個別信号**
```systemverilog
(* mark_debug = "true" *) wire axi_awvalid_debug;      // アドレス書き込み有効
(* mark_debug = "true" *) wire axi_awready_debug;      // アドレス書き込み準備完了
(* mark_debug = "true" *) wire axi_wvalid_debug;       // データ書き込み有効
(* mark_debug = "true" *) wire axi_wready_debug;       // データ書き込み準備完了
(* mark_debug = "true" *) wire axi_bvalid_debug;       // 書き込み応答有効
(* mark_debug = "true" *) wire axi_bready_debug;       // 書き込み応答準備完了
```

### 📊 **データ・アドレス信号**
```systemverilog
(* mark_debug = "true" *) wire [31:0] axi_awaddr_debug; // 書き込みアドレス
(* mark_debug = "true" *) wire [31:0] axi_wdata_debug;  // 書き込みデータ
(* mark_debug = "true" *) wire [3:0] axi_wstrb_debug;   // 書き込みストローブ
(* mark_debug = "true" *) wire [1:0] axi_bresp_debug;   // 書き込み応答
```

### 🎯 **専用トリガー信号**
```systemverilog
(* mark_debug = "true" *) wire reg_test_write_trigger;  // REG_TEST書き込み専用トリガー
(* mark_debug = "true" *) wire reg_test_addr_match;     // REG_TESTアドレス範囲マッチ
```

### 📝 **個別レジスタ書き込み検出**
```systemverilog
(* mark_debug = "true" *) logic test_reg_0_write_detect; // REG_TEST_0書き込み検出
(* mark_debug = "true" *) logic test_reg_1_write_detect; // REG_TEST_1書き込み検出
(* mark_debug = "true" *) logic test_reg_2_write_detect; // REG_TEST_2書き込み検出
(* mark_debug = "true" *) logic test_reg_3_write_detect; // REG_TEST_3書き込み検出
```

## ILAトリガー設定推奨事項

### **優先度1: 専用トリガー信号**
```
Trigger: reg_test_write_trigger = 1
これが最も確実なトリガー条件です
```

### **優先度2: 個別レジスタ検出**
```
Trigger: test_reg_0_write_detect = 1 OR
         test_reg_1_write_detect = 1 OR
         test_reg_2_write_detect = 1 OR
         test_reg_3_write_detect = 1
```

### **優先度3: 複合条件**
```
Trigger: write_enable = 1 AND reg_test_addr_match = 1
```

### **優先度4: 基本条件**
```
Trigger: write_enable = 1
```

## トラブルシューティング手順

### 1. **基本信号確認**
- `axi_awvalid_debug`と`axi_awready_debug`が両方High → `aw_handshake` = 1
- `axi_wvalid_debug`と`axi_wready_debug`が両方High → `w_handshake` = 1
- `axi_state_write_data` = 1 かつ `w_handshake` = 1 → `write_enable` = 1

### 2. **アドレス確認**
- `axi_awaddr_debug`が0x00001020-0x0000102Cの範囲にある
- `reg_test_addr_match` = 1であることを確認

### 3. **データ確認**
- `axi_wdata_debug`に期待するデータが設定されている
- `axi_wstrb_debug` = 4'b1111 (全バイト有効)

### 4. **状態マシン確認**
- `axi_state`がIDLE → WRITE_ADDR → WRITE_DATA → WRITE_RESPの順に遷移

## 期待される動作シーケンス

```
1. axi_awvalid_debug = 1, axi_awaddr_debug = 0x00001020
2. aw_handshake = 1 (awvalid && awready)
3. axi_state = WRITE_DATA
4. axi_wvalid_debug = 1, axi_wdata_debug = 0x12345678
5. w_handshake = 1 (wvalid && wready)
6. write_enable = 1
7. reg_test_write_trigger = 1
8. test_reg_0_write_detect = 1
9. test_reg_0 = 0x12345678
```

これらの信号により、`write_enable`がなぜトリガーされないかを詳細に分析できます。