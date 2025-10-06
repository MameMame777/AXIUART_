# 🔬 検証手順書 - AXIUART_ プロトコル整合性確立

**作成日**: 2025年10月6日  
**対象**: RTL実装値に基づくプロトコル整合性の確立  
**基準文書**: debug_strategy_plan_20251006.md

---

## 📋 検証手順概要

### 🎯 検証目標
1. **RTL実装値の最終確認** - 実際の送信値の確定測定
2. **プロトコル仕様の現実化** - 仕様書をRTL実装に合わせる
3. **テスト期待値の更新** - 全テストコードの整合性確保
4. **統合動作の確認** - 更新後の正常動作検証

### ⚠️ 重要方針
**ハードウェア変更は行わない** - 現在動作中のRTL実装を保持し、仕様とテストを現実に合わせる

---

## 🔍 Phase A: RTL実装値の最終確認

### A.1 実測値確認手順

#### A.1.1 現在のテストスクリプト実行
```bash
cd E:\Nautilus\workspace\fpgawork\AXIUART_\software
python test_registers_updated.py
```

**確認項目**:
- SOF値の実測 (期待: 0x6B)
- STATUS値の実測 (期待: 0x60)  
- CMD_ECHO値の実測 (期待: cmd ^ 0x19)

#### A.1.2 詳細ログ収集
```python
# test_registers_updated.py に以下を追加
def detailed_protocol_analysis(self, response):
    """詳細プロトコル解析"""
    print(f"📊 詳細解析: {' '.join(f'{b:02X}' for b in response)}")
    
    if len(response) >= 8:  # Read response
        sof, status, cmd = response[0:3]
        print(f"🔍 SOF: 0x{sof:02X} (期待: 0x6B)")
        print(f"🔍 STATUS: 0x{status:02X} (期待: 0x60)")
        print(f"🔍 CMD_ECHO: 0x{cmd:02X}")
        
        # ビットパターン解析
        print(f"🔍 SOF binary: {sof:08b}")
        print(f"🔍 STATUS binary: {status:08b}")
```

#### A.1.3 複数回測定による統計確認
```python
# 統計的確認スクリプト
def statistical_verification():
    """10回測定での値の一貫性確認"""
    sof_values = []
    status_values = []
    
    for i in range(10):
        response = bridge.read_register(0x00001020)
        if response:
            sof_values.append(response[0])
            status_values.append(response[1])
            
    print(f"📊 SOF統計: {set(sof_values)}")
    print(f"📊 STATUS統計: {set(status_values)}")
```

### A.2 RTL実装値確定

**目標値** (Phase 1調査結果):
```
SOF: 0x6B (0x5A ^ 0x31)
STATUS: 0x60 (0x00 ^ 0x60)
CMD_ECHO: cmd_value ^ 0x19
```

**確認基準**:
- [ ] 10回測定で100%同一値
- [ ] Phase 1解析結果との一致
- [ ] ビットパターンの論理的整合性

---

## 📝 Phase B: プロトコル仕様の現実化

### B.1 プロトコル仕様書の改訂

#### B.1.1 uart_axi4_protocol.md の更新

**変更箇所1**: Section 2.1 Common fields
```markdown
変更前:
- SOF: 1 byte start-of-frame marker
  - Response (device→host): `0x5A`

変更後:
- SOF: 1 byte start-of-frame marker  
  - Response (device→host): `0x6B`
```

**変更箇所2**: Section 3 Status codes
```markdown
変更前:
- `0x00` OK: Success

変更後:
- `0x60` OK: Success
```

**変更箇所3**: フレーム例の更新
```markdown
変更前:
- Write response: `SOF (0x5A) | STATUS | CMD | CRC8`

変更後:  
- Write response: `SOF (0x6B) | STATUS | CMD | CRC8`
```

#### B.1.2 バージョン管理
```markdown
# 改訂履歴の追加
## Revision History
- v0.1 (2025-09-15): Initial version
- v0.2 (2025-10-06): Updated SOF and STATUS values to match RTL implementation
  - SOF device→host: 0x5A → 0x6B
  - STATUS OK: 0x00 → 0x60
  - Reason: Alignment with implemented hardware behavior
```

### B.2 設計文書の整合性確保

#### B.2.1 design_overview.md の確認
- プロトコル参照箇所の確認
- 必要に応じた値の更新

#### B.2.2 register_map.md の確認  
- STATUS関連定義の確認
- テストレジスタ動作説明の確認

---

## 🧪 Phase C: テスト期待値の更新

### C.1 Pythonテストスクリプトの更新

#### C.1.1 test_registers_updated.py の修正

**定数定義の追加**:
```python
# プロトコル定数 (RTL実装値)
PROTOCOL_SOF_RESPONSE = 0x6B      # Device→Host SOF
PROTOCOL_STATUS_OK = 0x60         # Success status
PROTOCOL_CMD_CORRECTION_MASK = 0x19  # CMD correction mask
```

**検証ロジックの更新**:
```python
def validate_response(self, response):
    """RTL実装値に基づく応答検証"""
    if len(response) >= 2:
        sof, status = response[0], response[1]
        
        # SOF検証
        if sof == PROTOCOL_SOF_RESPONSE:
            print("✅ SOF正常: 0x6B")
        else:
            print(f"❌ SOF異常: 0x{sof:02X} (期待: 0x6B)")
            
        # STATUS検証  
        if status == PROTOCOL_STATUS_OK:
            print("✅ STATUS正常: 0x60")
            return True
        else:
            print(f"❌ STATUS異常: 0x{status:02X} (期待: 0x60)")
            
    return False
```

### C.2 UVMテストベンチの更新

#### C.2.1 期待値定数の更新
```systemverilog
// UVM検証環境での期待値更新
localparam [7:0] EXPECTED_SOF_DEVICE_TO_HOST = 8'h6B;
localparam [7:0] EXPECTED_STATUS_OK = 8'h60;
```

#### C.2.2 スコアボードの更新
```systemverilog
// スコアボード比較ロジックの更新
function bit compare_sof(input [7:0] actual);
    return (actual == EXPECTED_SOF_DEVICE_TO_HOST);
endfunction

function bit compare_status(input [7:0] actual);
    return (actual == EXPECTED_STATUS_OK);
endfunction
```

---

## ✅ Phase D: 統合動作確認

### D.1 更新後動作確認

#### D.1.1 基本機能テスト
```bash
# 基本レジスタアクセステスト
python test_registers_updated.py

# 期待結果:
# ✅ SOF正常: 0x6B
# ✅ STATUS正常: 0x60  
# ✅ 全テスト成功
```

#### D.1.2 回帰テスト
```bash
# UVMテスト実行
cd sim/exec
./run_uvm.ps1 -test uart_basic_test

# 期待結果:
# UVM_ERROR: 0
# 全カバレッジ目標達成
```

### D.2 性能・安定性確認

#### D.2.1 連続動作テスト
```python
# 100回連続アクセステスト
def endurance_test():
    success_count = 0
    for i in range(100):
        if bridge.test_single_register():
            success_count += 1
    
    print(f"📊 成功率: {success_count}/100 ({success_count}%)")
    return success_count == 100
```

#### D.2.2 異なるボーレートでの確認
```python
# 複数ボーレートでの動作確認
BAUD_RATES = [115200, 230400, 460800]

for baud in BAUD_RATES:
    bridge = TestRegisterAccess("COM3", baud)
    if bridge.connect():
        result = bridge.test_single_register()
        print(f"📡 {baud} baud: {'✅' if result else '❌'}")
```

---

## 📊 検証完了基準

### ✅ Phase A完了基準
- [ ] RTL実装値の10回連続確認
- [ ] Phase 1解析結果との完全一致
- [ ] 測定値の統計的一貫性確認

### ✅ Phase B完了基準  
- [ ] プロトコル仕様書v0.2完成
- [ ] 改訂履歴の記録
- [ ] 設計文書との整合性確認

### ✅ Phase C完了基準
- [ ] Pythonテスト期待値の更新完了
- [ ] UVMテストベンチの更新完了
- [ ] 全テストコードの動作確認

### ✅ Phase D完了基準
- [ ] 基本機能テスト100%成功
- [ ] UVM回帰テスト成功
- [ ] 連続動作テスト100%成功
- [ ] 複数ボーレートでの動作確認

---

## 🚨 トラブルシューティング

### 想定問題と対処法

#### 問題1: 測定値が期待と異なる
**対処**: 
1. ILAでの詳細観測実行
2. UART物理層の確認
3. Phase 1解析の再確認

#### 問題2: テスト更新後の動作異常
**対処**:
1. 変更の段階的ロールバック
2. 個別機能の分離テスト
3. ベースライン値への復帰

#### 問題3: UVMテスト失敗
**対処**:
1. UVMログの詳細解析
2. 期待値の段階的更新
3. テストケースの個別実行

---

## 📝 実行記録テンプレート

### 検証実行ログ

```
検証実行日: 2025年10月6日
実行者: [氏名]
環境: Windows, COM3, FPGA実機

=== Phase A: RTL実装値確認 ===
SOF測定値: 0x__ (10回中__回一致)
STATUS測定値: 0x__ (10回中__回一致)  
結論: [ ] 確認完了 [ ] 要再調査

=== Phase B: 仕様書更新 ===  
改訂版: [ ] v0.2作成完了
変更箇所: [ ] SOF [ ] STATUS [ ] フレーム例
結論: [ ] 更新完了 [ ] 要修正

=== Phase C: テスト更新 ===
Python期待値: [ ] 更新完了 [ ] 動作確認完了
UVM期待値: [ ] 更新完了 [ ] 動作確認完了
結論: [ ] 更新完了 [ ] 要修正

=== Phase D: 統合確認 ===
基本テスト: [ ] 成功 [ ] 失敗
回帰テスト: [ ] 成功 [ ] 失敗
連続動作: [ ] 成功 [ ] 失敗

総合結論: [ ] 全Phase成功 [ ] 部分成功 [ ] 要継続
```

**SystemVerilogエンジニアとして、体系的で実証的な検証により確実な問題解決を実現します。** 🎯