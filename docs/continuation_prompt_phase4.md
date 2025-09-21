# AXIUART Emergency Repair Project - Phase 4 Continuation Prompt

## 🚨 **緊急修復プロジェクト継続指示**

**あなたはSystemVerilogエキスパートとして、AXIUART緊急修復プロジェクトのPhase 4を担当します。**

### 📊 **現在の状況**

**Phase 3で重大な進歩を達成**:
- ✅ **タイムアウト削減**: 45個 → 11個（**76%削減**）
- ✅ **Frame_Parser**: CRC検証完全修復（0x76で動作確認済み）
- ✅ **Register_Block**: AXI4-Lite状態マシン仕様適合性修正完了
- ⚠️ **Frame_Builder**: レスポンス生成で11個のタイムアウト残存

**システム通信状態**: 完全無応答から部分的フレーム受信へ回復済み

---

## 🎯 **Phase 4 最優先ミッション**

### **Frame_Builder Response Generation の完全修復**

**問題**: 11個のUVM_ERRORタイムアウトがFrame_Builderコンポーネントに集中
**症状**: UARTモニターでフレーム検出されるが、CRC不一致で失敗
**ターゲット**: **UVM_ERROR: 0**（完全なタイムアウトエラー解決）

### **根本原因仮説**
1. **AXI transaction_done信号からbuild_response信号への経路**
2. **Frame_Builderレスポンスフレーム生成ロジック** 
3. **UART TXへの出力タイミング**

---

## 🔍 **即座に実行すべき診断**

### **Step 1: Frame_Builder診断テスト実行**
```powershell
cd "e:\Nautilus\workspace\fpgawork\AXIUART_\sim\uvm"
.\run_uvm.ps1 -TestName uart_axi4_frame_builder_test -Waves $true
```

**期待する結果**: 11個のUVM_ERRORタイムアウトを確認し、波形解析でFrame_Builder内部動作を詳細調査

### **Step 2: システム統合テスト状況確認**
```powershell
.\run_uvm.ps1 -TestName uart_axi4_basic_test -Waves $true
```

**期待する結果**: 部分的フレーム受信の詳細パターンを波形で解析

---

## 🔧 **調査すべき技術ポイント**

### **AXI Transaction → Response Chain**
```
AXI Request → Register_Block → transaction_done → 
Uart_Axi4_Bridge.build_response → Frame_Builder → UART TX
```

**重点確認項目**:
1. `Axi4_Lite_Master.transaction_done`信号のアサートタイミング
2. `Uart_Axi4_Bridge.build_response`信号の生成ロジック  
3. Frame_Builderの応答データ構築プロセス
4. UART TX FIFOへの書き込み成功率

### **Frame_Builder内部状態解析**
- **build_response信号生成タイミング**
- **Frame_Builder状態マシンの遷移**  
- **CRC計算とフレーム構築プロセス**
- **UART TX FIFO への書き込み完了確認**

---

## 📁 **利用可能なリソース**

### **準備済み診断テスト**
- `sim/uvm/tests/uart_axi4_frame_builder_test.sv`
- `sim/uvm/sequences/uart_axi4_frame_builder_sequence.sv`
- `sim/uvm/tests/uart_axi4_register_block_test.sv`（参考用）

### **修正済みRTLファイル**
- `rtl/Register_Block.sv` - **Phase 3で修正済み（維持必須）**
- `rtl/Frame_Parser.sv` - **完全動作確認済み（維持必須）**

### **修正対象RTLファイル**
- `rtl/Frame_Builder.sv` - **Response generation target**
- `rtl/Uart_Axi4_Bridge.sv` - **build_response control**  
- `rtl/Axi4_Lite_Master.sv` - **transaction_done source**

### **波形解析ファイル**
- `sim/uvm/uart_axi4_frame_builder_test.mxd`（11 timeouts）
- `sim/uvm/uart_axi4_basic_test.mxd`（partial frames detected）

---

## 🚨 **重要な制約事項**

### **Phase 3修正の保護**
- **絶対に変更禁止**: `rtl/Register_Block.sv`のAXI4-Lite状態マシン修正
- **絶対に変更禁止**: `rtl/Frame_Parser.sv`のCRC検証修正
- これらの修正により76%のタイムアウト削減を達成済み

### **実行環境要件**
- **必須**: PowerShellスクリプト`run_uvm.ps1`からシミュレーション実行
- **DSIM v20240422.0.0**使用
- **UVM 1.2**フレームワーク
- **MXD形式**での波形ファイル生成

---

## 🎖️ **Phase 4 成功基準**

### **最終目標**
```
✅ UVM_ERROR: 0（完全なタイムアウトエラー解決）
✅ 全てのテストでレスポンスフレーム受信成功  
✅ CRC検証パス率 100%
✅ Frame coverage > 80%
```

### **中間検証ポイント**
1. Frame_Builder診断テスト: 11個 → 0個
2. System統合テスト: 45個 → 0個
3. UARTモニターでの正常フレーム検出
4. Scoreboard match率向上

---

## 📋 **推奨作業シーケンス**

1. **現状確認**: 波形ファイル解析で現在の11タイムアウトパターンを把握
2. **RTL調査**: Frame_Builder, Uart_Axi4_Bridge, Axi4_Lite_Masterの信号経路確認
3. **原因特定**: build_response生成からUART TX出力までのボトルネック特定
4. **修正実装**: 特定された問題箇所の修正実装
5. **検証実行**: 修正後の診断テスト実行で改善確認
6. **統合テスト**: システム全体での完全動作確認

---

## 💡 **開始時のアクション**

**最初に実行すべきコマンド**:
```powershell
# 現在の状態確認
cd "e:\Nautilus\workspace\fpgawork\AXIUART_\sim\uvm"
git log --oneline -3

# Frame_Builder診断実行
.\run_uvm.ps1 -TestName uart_axi4_frame_builder_test -Waves $true

# 結果確認後、波形解析で具体的問題箇所を特定
```

---

**あなたのミッション**: AXIUART緊急修復プロジェクトの最終段階として、残り11個のタイムアウトエラーを完全に解決し、システム全体の完全動作を実現してください。

**Phase 4 SUCCESS TARGET**: Complete elimination of all timeout errors and full system communication restoration 🚀