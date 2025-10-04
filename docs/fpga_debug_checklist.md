# FPGA Hardware Debug Checklist
## 🚨 SOF タイムアウト問題 - FPGA側診断チェックリスト

**診断結果**: COM3アクセス ✅ / FPGA応答 ❌  
**問題箇所**: FPGA側ハードウェア/ソフトウェア

---

## 📋 1. 基本ハードウェア確認 (Priority: HIGH)

### 🔌 電源・クロック
- [ ] FPGAボードの電源LED点灯確認
- [ ] システムクロック(通常100MHz)の供給確認 
- [ ] PLLロック状態の確認
- [ ] リセット信号の解除確認

### 🔗 UART物理接続
- [ ] UART TX/RX信号線の接続確認
- [ ] GND接続の確認
- [ ] RTS/CTS信号線の接続確認 (使用している場合)
- [ ] FTDIドライバーの正常動作確認

---

## 📟 2. FPGA内部状態確認 (Priority: HIGH)

### 🧬 FPGA コンフィギュレーション
```bash
# VivadoでFPGAプログラム状態確認
vivado -mode batch -source check_fpga_status.tcl
```

### 🔍 内部信号確認
- [ ] UART_Rx モジュールの動作確認
- [ ] AXI4-Lite バスの動作確認  
- [ ] クロックドメインクロッシング確認
- [ ] リセット信号の伝播確認

### 📊 ILA (Integrated Logic Analyzer) 確認
必要な信号をILAで観測:
```verilog
// 観測対象信号
- uart_rx_data
- uart_rx_valid  
- axi_lite_awvalid
- axi_lite_arvalid
- system_reset_n
- uart_clk
```

---

## ⚙️ 3. UART設定確認 (Priority: MEDIUM)

### 📡 ボーレート設定
現在のFPGA側設定を確認:
```verilog
// FPGA側ボーレート分周設定 
// 100MHz / 115200bps = 868.055... ≈ 868
parameter BAUD_RATE_DIV = 868;
```

- [ ] システムクロック周波数の確認
- [ ] ボーレート分周比の再計算
- [ ] UART_Rx/Tx のクロック設定確認

### 🔄 フロー制御
- [ ] RTS/CTS信号の極性確認
- [ ] フロー制御ロジックの動作確認
- [ ] フロー制御無効設定での動作テスト

---

## 🔧 4. すぐに試せる対策

### A. クイックテスト (推奨)
```bash
# 1. FPGA電源リセット
# 2. より低いボーレートでテスト
python test_lower_baudrate.py  # 38400bps
# 3. フロー制御無効でテスト  
python test_no_flowcontrol.py
```

### B. ハードウェア確認
```bash
# オシロスコープがある場合
# 1. UART_RX信号の確認 (PC → FPGA)
# 2. システムクロックの確認
# 3. リセット信号の確認
```

### C. Vivado デバッグ
```tcl
# Vivado Hardware Manager
open_hw_manager
connect_hw_server
open_hw_target
refresh_hw_device
# FPGAプログラム状態確認
```

---

## 🚨 5. 緊急対策手順

### Option 1: FPGA再プログラム
```bash
cd E:\Nautilus\workspace\fpgawork\AXIUART_\PandR\vivado\AXIUART_
vivado AXIUART_.xpr
# -> Generate Bitstream
# -> Program Device
```

### Option 2: シンプル エコーテスト用ビットストリーム
最小限のUARTエコー機能のみでテスト:
```verilog
// Simple UART Echo Module
// 受信データをそのまま送信し返す
```

### Option 3: LEDテスト
UARTデータ受信時にLEDを点滅させるテスト:
```verilog
// LED debug module
// UART RX活動時にLEDを点灯
```

---

## 📊 6. 問題切り分けマトリックス

| 症状 | 可能性の高い原因 | 対策 |
|------|----------------|------|
| COMアクセス ✅ / FPGA応答 ❌ | FPGA内部問題 | ハードウェア確認 |
| LED消灯 | 電源/クロック問題 | 電源・クロック確認 |  
| LED点灯 / UART応答❌ | UARTモジュール問題 | ボーレート・設定確認 |
| 一部データ受信 | プロトコル問題 | フレーム形式確認 |

---

## 🔄 7. 次のアクション優先順位

1. **最優先**: FPGAボード目視確認 (LED点灯状態)
2. **高優先**: FPGA再プログラム実行
3. **中優先**: ボーレート設定確認・変更
4. **低優先**: オシロスコープ確認

---

## 💡 診断コマンド集

```bash
# Windows COMポート確認
mode COM3

# Python簡易テスト  
python simple_com_test.py

# プロトコル詳細分析
python fpga_protocol_analyzer.py

# Vivado Hardware Manager
vivado -mode gui &
```