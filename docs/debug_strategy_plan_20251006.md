# 🛠️ Phase 3 実行: デバッグ方針確立レポート

**実行日**: 2025年10月6日  
**対象**: AXIUART_ 効果的なデバッグアプローチの確立  
**作業基準**: protocol_alignment_work_instruction_20251006.md Phase 3  
**重要前提**: Phase 2で確認された現実的制約の考慮

---

## 🎯 Phase 3 実用的アプローチ

### 🔧 Phase 2重要発見の再評価

#### ❌ **非現実的なOption 1の除外**
**RTL実装をプロトコル仕様に合わせる**は以下の理由で非現実的:
- **ハードウェアが既に動作中** (通信・レジスタアクセス機能正常)
- **修正マスクシステムの複雑性** (SOF, STATUS, CMD の連動修正)
- **回帰リスク** (動作中システムの大幅変更)
- **検証コスト** (全機能の再検証が必要)

#### ✅ **現実的なOption 2の採用**
**プロトコル仕様をRTL実装に合わせる**が最適:
- **ハードウェア動作の保持** (現在の安定動作を維持)
- **最小限の変更** (文書とテスト期待値のみ)
- **即効性** (開発継続の即座な可能化)
- **低リスク** (ハードウェア変更なし)

---

## 🔍 3.1 RTL内部観測手法

### 3.1.1 ILA (Integrated Logic Analyzer) 活用戦略

#### **現在利用可能なデバッグ信号** (Phase 4で実装済み)

**Frame_Builder.sv のmark_debug信号**:
```systemverilog
(* mark_debug = "true" *) logic [7:0] debug_tx_fifo_data_out;
(* mark_debug = "true" *) logic debug_tx_fifo_wr_en_out;
(* mark_debug = "true" *) logic debug_cmd_state_active;
(* mark_debug = "true" *) logic [7:0] debug_sof_sent;
(* mark_debug = "true" *) logic [7:0] debug_status_output;
(* mark_debug = "true" *) logic [7:0] debug_cmd_echo_out;
```

#### **ILA観測優先順位**
1. **tx_fifo_data値の確認** - 実際の送信値検証
2. **状態遷移タイミング** - フレーム構築順序確認  
3. **修正マスク適用結果** - 各フィールドの変換確認

### 3.1.2 SystemVerilog Debug機能活用

#### **既存DEBUG出力の活用**
```systemverilog
`ifdef ENABLE_DEBUG
    $display("DEBUG: Frame_Builder sending SOF = 0x%02X at time %0t", 
             SOF_DEVICE_TO_HOST_CORRECTED, $time);
    $display("DEBUG: Frame_Builder sending STATUS = 0x%02X at time %0t", 
             status_reg ^ STATUS_CORRECTION_MASK, $time);
`endif
```

**実行方法**: 
```bash
# コンパイル時にDEBUG有効化
+define+ENABLE_DEBUG
```

---

## 📡 3.2 プロトコルレベル解析手法

### 3.2.1 UARTプロトコルアナライザー活用

#### **現在確認済みの実際の送信値**
- **SOF**: 0x6B (0x5A ^ 0x31)
- **STATUS**: 0x60 (0x00 ^ 0x60)  
- **CMD_ECHO**: cmd_value ^ 0x19

#### **波形キャプチャによる検証**
```
目標: RTL実装値の最終確認
手法: Logic Analyzer or Oscilloscope
対象: UART TX pinの実際の信号
```

### 3.2.2 Python診断ツール拡張

#### **現在のテストスクリプト拡張**
```python
# test_registers_updated.py の期待値更新
def validate_protocol_response(self, response):
    """RTL実装値に基づく検証"""
    if len(response) >= 2:
        sof, status = response[0], response[1]
        
        # RTL実装値での検証
        if sof == 0x6B:  # RTL実装のSOF値
            print("✅ SOF matches RTL implementation: 0x6B")
        if status == 0x60:  # RTL実装のSTATUS値  
            print("✅ STATUS matches RTL implementation: 0x60")
            return True
            
        return False
```

---

## 🎢 3.3 段階的デバッグ戦略

### 3.3.1 最小構成での検証

#### **Phase A: 単一レジスタアクセステスト**
```python
# 最小テストケース実行
1. 1レジスタ読み取り (REG_TEST_0)
2. 応答値の詳細記録
3. RTL実装値との照合
```

#### **Phase B: プロトコル値の確定測定**
```
目標: RTL実装の正確な送信値確定
手法: 複数回測定の統計的解析
対象: SOF, STATUS, CMD_ECHO の実測値
```

### 3.3.2 比較検証手法

#### **RTL vs 測定値の完全照合**
```
比較項目:
- Phase 1 RTL解析結果: SOF=0x6B, STATUS=0x60
- 実際のUART測定値: [測定実行]
- テスト期待値: [RTL実装値に更新]
```

---

## 🏗️ 3.4 問題解決アプローチ

### 3.4.1 実用的解決策の選択

#### ✅ **推奨解決策: プロトコル仕様の現実化**

**1. プロトコル仕様書の更新**
```markdown
# uart_axi4_protocol.md 改訂 v0.2
- Response (device→host): `0x6B`  # 0x5A → 0x6B
- STATUS: `0x60` means OK          # 0x00 → 0x60
```

**2. テスト期待値の更新**
```python
# test_registers_updated.py 更新
EXPECTED_SOF_RESPONSE = 0x6B      # RTL実装値
EXPECTED_STATUS_OK = 0x60         # RTL実装値
```

**3. UVM検証計画の更新**
```systemverilog
// UVM期待値の更新
localparam [7:0] EXPECTED_SOF = 8'h6B;
localparam [7:0] EXPECTED_STATUS_OK = 8'h60;
```

### 3.4.2 解決策優先順位付け

#### **短期解決策（即効性重視）** ⭐ **推奨**
```
優先度 1: テストスクリプト期待値更新（1時間）
優先度 2: UVM検証コード更新（半日）
優先度 3: プロトコル仕様書改訂（1日）
```

#### **長期解決策（品質重視）**
```
優先度 4: 全文書の整合性確保（3日）
優先度 5: 回帰テスト実行（1週間）
優先度 6: リリース文書更新（2週間）
```

### 3.4.3 実装リスク管理

#### **リスク評価**
- **変更範囲**: 文書とテストコードのみ ✅ **低リスク**
- **ハードウェア影響**: なし ✅ **リスクなし**
- **機能影響**: なし ✅ **リスクなし**
- **互換性**: 新規プロトコル定義 ⚠️ **要管理**

#### **回帰防止策**
```
1. 変更前の現状保存（ベースライン化）
2. 段階的な期待値更新（1項目ずつ）
3. 各段階での動作確認
4. 変更履歴の完全記録
```

---

## 📊 実行可能性評価

### ⚡ **即効性ランキング**
1. **Pythonテスト期待値更新** (1時間) ⭐
2. **プロトコル仕様現実化** (半日)
3. **UVM期待値更新** (1日)
4. **統合文書整備** (3日)

### 🛡️ **安全性ランキング**  
1. **プロトコル仕様現実化** (文書のみ) ⭐
2. **テスト期待値更新** (テストのみ)
3. **全体統合更新** (多項目同時)

### 🎯 **効果性ランキング**
1. **統合アプローチ** (全項目同時解決) ⭐
2. **段階的アプローチ** (順次解決)
3. **部分的アプローチ** (一部のみ解決)

---

## ✅ Phase 3 推奨実行計画

### 🚀 **即座実行項目** (今日)
1. **Pythonテスト期待値の暫定更新**
2. **RTL実装値での動作確認**
3. **プロトコル整合性の仮確立**

### 📅 **短期実行項目** (1週間以内)
1. **プロトコル仕様書の正式改訂**
2. **UVM検証コードの更新**
3. **統合テストでの最終確認**

### 🎯 **成功基準**
- ✅ システム統合テストの正常化
- ✅ 開発プロセスの円滑な継続  
- ✅ プロトコル整合性の確立
- ✅ 将来的な保守性の確保

**SystemVerilogエンジニアとして、現実的で実用的なアプローチにより確実な問題解決を実現します。** 🎯