# FPGA Register Debug Work Instructions - 2025-10-07

## 1. 現状の問題点まとめ

### 1.1 確認された動作状況
- ✅ **UVMシミュレーション**: 完全に動作（76/76トランザクション成功）
- ✅ **FPGAでの書き込み**: 成功（正しいステータス応答 0x80）
- ❌ **FPGAでの読み戻し**: 失敗（期待値と異なる固定値が返される）

### 1.2 具体的な問題詳細

#### 問題1: 読み戻し値の不整合
```
期待値（RTL初期値）    → 実際のFPGA応答値
REG_TEST_0: 0xDEADBEEF → 0xF0202248
REG_TEST_1: 0x12345678 → 0xF0202249  
REG_TEST_2: 0xABCDEF00 → 0xF020224A
REG_TEST_3: 0x00000000 → 0xF020224B
```

#### 問題2: 書き込み後の読み戻し不整合
- 書き込み: 0x11111111 → ステータス 0x80（成功）
- 読み戻し: 0xF0202248 （書き込み値が反映されない）

#### 問題3: パターン分析結果
```
読み戻し値のパターン: 0xF02022XX
- XX部分は連続値（0x48, 0x49, 0x4A, 0x4B）
- アドレスに依存した固定値生成パターン
- 実際のレジスタ値ではなく、テストパターン生成器の出力
```

### 1.3 根本原因の推定
1. **FPGAの実装不整合**: Register_Block.svのRTLコードが正しくFPGAに実装されていない
2. **テストパターン生成器の混入**: FPGAにテストパターン生成回路が実装されている
3. **読み出しパスの誤配線**: AXI読み出しが実際のレジスタではなく別のデータソースから取得

## 2. 調査方針と作業指示

### 2.1 Phase 1: FPGA実装状況の詳細調査

#### 作業1-1: レジスタアドレス範囲の網羅的調査
**目的**: FPGAに実装されている実際のメモリマップを確認
**手法**: 全レジスタアドレスでの読み出しテスト

```python
# 実装内容: fpga_memory_map_scan.py
address_ranges = {
    "Standard_Registers": range(0x00001000, 0x00001020, 4),
    "REG_TEST_Registers": range(0x00001020, 0x00001030, 4),
    "Extended_Range": range(0x00001030, 0x00001100, 4)
}
```

**関連ファイル**:
- `rtl/Register_Block.sv` (lines 29-43: アドレスマップ定義)
- `software/fpga_reg_debug.py` (既存のデバッグツール)

#### 作業1-2: 書き込み→読み戻しシーケンステスト
**目的**: 書き込み操作の実際の効果を確認
**手法**: 特定パターンでの連続書き込み・読み戻し

```python
# 実装内容: fpga_write_sequence_test.py  
test_patterns = [
    0x00000000, 0xFFFFFFFF, 0x55555555, 0xAAAAAAAA,
    0x12345678, 0x87654321, 0xDEADBEEF, 0xCAFEBABE
]
```

**関連ファイル**:
- `software/fpga_write_read_test.py` (既存の基本テストツール)
- `rtl/Register_Block.sv` (lines 292-340: 書き込みロジック)

#### 作業1-3: UARTプロトコル詳細解析
**目的**: FPGAとの通信プロトコルが仕様通りか確認
**手法**: バイトレベルでのプロトコル解析

```python
# 実装内容: fpga_protocol_analyzer.py
def analyze_response_pattern(address, response):
    sof = response[0]      # 期待値: 0xAD
    status = response[1]   # 期待値: 0x80  
    cmd = response[2]      # 期待値: 0x68
    data = response[3:7]   # 実際の応答データ
    crc = response[7]      # CRC検証
```

**関連ファイル**:
- `software/test_registers_updated.py` (既存の実装パターン)
- `docs/uart_axi4_protocol.md` (プロトコル仕様)

### 2.2 Phase 2: RTL実装の検証とFPGAデプロイ

#### 作業2-1: Register_Block.sv実装検証
**目的**: RTLコードが正しく動作することを再確認
**手法**: UVMテストベンチでの追加検証

```systemverilog
// 検証項目:
// - test_reg_0-3の初期値確認
// - 書き込み→読み戻しの正確性
// - アドレスデコーディング動作
// - WSTRB マスク動作
```

**関連ファイル**:
- `rtl/Register_Block.sv` (lines 53-56: test_reg定義)
- `sim/uvm/sequences/uart_axi4_reg_test_sequence.sv` (検証シーケンス)
- `sim/uvm/tests/uart_axi4_reg_test_verification_test.sv` (テスト実行)

#### 作業2-2: FPGA合成・実装の確認
**目的**: 最新のRTLがFPGAに正しく実装されているか確認
**手法**: ハードウェアチームとの実装状況確認

**確認項目**:
- Register_Block.svの最終更新日時: 2025-10-05
- FPGAビットストリーム生成日時
- 合成時の警告・エラーメッセージ
- タイミング制約の満足度

**関連ファイル**:
- `PandR/constraint/` (タイミング制約)
- 合成レポートファイル
- 実装レポートファイル

#### 作業2-3: REG_TEST専用検証環境構築
**目的**: REG_TESTレジスタ専用の詳細検証
**手法**: 専用UVMテストシーケンスの作成

```systemverilog
// 実装内容: uart_axi4_reg_test_detailed_sequence.sv
// - 各レジスタへの個別書き込み・読み戻し
// - ビットパターン網羅テスト
// - アドレス境界テスト
// - 同時アクセステスト
```

**関連ファイル**:
- `sim/uvm/sequences/` (新規シーケンス作成)
- `rtl/Register_Block.sv` (lines 402-429: REG_TEST読み出しロジック)

### 2.3 Phase 3: 問題修正と検証

#### 作業3-1: FPGAの再プログラム
**目的**: 最新のRTLでFPGAを更新
**手法**: ハードウェアチームとの連携作業

**実行手順**:
1. 最新のRegister_Block.svでの合成実行
2. タイミング制約の確認
3. FPGAへのビットストリーム書き込み
4. 基本動作確認

#### 作業3-2: 修正後の包括的検証
**目的**: 問題修正後の動作確認
**手法**: 段階的検証アプローチ

```python
# 実装内容: fpga_comprehensive_verification.py
verification_phases = [
    "basic_connectivity",      # 基本通信確認
    "register_initial_values", # 初期値確認  
    "write_operations",        # 書き込み動作
    "read_operations",         # 読み戻し動作
    "pattern_verification",    # パターンテスト
    "stress_testing"          # ストレステスト
]
```

#### 作業3-3: UVMとFPGA結果の整合性確認
**目的**: シミュレーションと実機の完全一致を確認
**手法**: 同一テストパターンでの比較検証

```python
# 比較項目:
# - 初期値 (UVM: 0xDEADBEEF vs FPGA: 期待同値)
# - 書き込み応答 (両方とも成功ステータス)
# - 読み戻し値 (完全一致)
# - エラー処理 (同一エラーコード)
```

## 3. 各スクリプトの実装方針

### 3.1 fpga_memory_map_scan.py
```python
class FPGAMemoryMapScanner:
    def __init__(self):
        self.address_ranges = self._define_scan_ranges()
        
    def _define_scan_ranges(self):
        return {
            "Control_Registers": range(0x1000, 0x1020, 4),
            "REG_TEST_Registers": range(0x1020, 0x1030, 4), 
            "Unknown_Range": range(0x1030, 0x1100, 4)
        }
    
    def scan_all_ranges(self):
        results = {}
        for range_name, addr_range in self.address_ranges.items():
            results[range_name] = self._scan_range(addr_range)
        return results
        
    def _scan_range(self, addr_range):
        # アドレス範囲の読み出し実行
        # パターン分析
        # 応答特性の記録
        pass
```

### 3.2 fpga_write_sequence_test.py
```python
class FPGAWriteSequenceTest:
    def __init__(self):
        self.test_patterns = [
            0x00000000, 0xFFFFFFFF, 0x55555555, 0xAAAAAAAA,
            0x12345678, 0x87654321, 0xDEADBEEF, 0xCAFEBABE
        ]
        
    def run_sequence_test(self, address):
        results = []
        for pattern in self.test_patterns:
            # 1. パターン書き込み
            write_result = self._write_register(address, pattern)
            
            # 2. 即座に読み戻し
            read_result = self._read_register(address)
            
            # 3. 結果記録
            results.append({
                'written': pattern,
                'read_back': read_result,
                'match': pattern == read_result
            })
            
        return results
```

### 3.3 fpga_protocol_analyzer.py
```python
class FPGAProtocolAnalyzer:
    def __init__(self):
        self.expected_sof = 0xAD
        self.expected_status_ok = 0x80
        self.expected_read_cmd = 0x68
        
    def analyze_response(self, command, response):
        analysis = {
            'command_sent': command,
            'response_length': len(response),
            'sof_correct': response[0] == self.expected_sof,
            'status_correct': response[1] == self.expected_status_ok,
            'cmd_echo_correct': response[2] == self.expected_read_cmd,
            'data_bytes': response[3:7].hex(),
            'crc_received': response[7] if len(response) > 7 else None
        }
        
        # データパターン分析
        if len(response) >= 7:
            data_value = int.from_bytes(response[3:7], 'little')
            analysis['data_pattern'] = self._analyze_data_pattern(data_value)
            
        return analysis
```

### 3.4 fpga_comprehensive_verification.py
```python
class FPGAComprehensiveVerification:
    def __init__(self):
        self.test_phases = [
            ('basic_connectivity', self._test_basic_connectivity),
            ('initial_values', self._test_initial_values),
            ('write_operations', self._test_write_operations),
            ('read_operations', self._test_read_operations),
            ('pattern_verification', self._test_pattern_verification)
        ]
        
    def run_full_verification(self):
        results = {}
        for phase_name, phase_func in self.test_phases:
            print(f"=== Phase: {phase_name} ===")
            results[phase_name] = phase_func()
            
            # フェーズ失敗時は停止
            if not results[phase_name]['success']:
                print(f"Phase {phase_name} failed, stopping verification")
                break
                
        return results
```

## 4. 作業スケジュールと担当

### 4.1 Phase 1: 調査 (1-2日)
- **作業1-1**: メモリマップスキャン実装・実行
- **作業1-2**: 書き込みシーケンステスト実装・実行  
- **作業1-3**: プロトコル解析実装・実行

### 4.2 Phase 2: RTL検証 (1日)
- **作業2-1**: UVMでの追加検証実行
- **作業2-2**: ハードウェアチームとの実装状況確認
- **作業2-3**: 専用検証環境構築

### 4.3 Phase 3: 修正・検証 (1-2日)
- **作業3-1**: FPGAの再プログラム (ハードウェアチーム主導)
- **作業3-2**: 修正後の包括的検証
- **作業3-3**: UVMとFPGA結果の整合性確認

## 5. 成功基準

### 5.1 Phase 1 完了基準
- [ ] 全レジスタアドレスの応答特性マップ作成完了
- [ ] パターン書き込み→読み戻しテスト結果の詳細分析完了
- [ ] プロトコル解析による異常箇所の特定完了

### 5.2 Phase 2 完了基準  
- [ ] UVMシミュレーションでのREG_TEST動作再確認（UVM_ERROR=0）
- [ ] FPGA実装状況の詳細把握完了
- [ ] 問題の根本原因特定完了

### 5.3 Phase 3 完了基準
- [ ] FPGA読み戻し値が期待値と完全一致
- [ ] 書き込み→読み戻しシーケンスが100%成功
- [ ] UVMシミュレーション結果とFPGA結果の完全整合

## 6. 関連ファイル一覧

### RTLファイル
- `rtl/Register_Block.sv` - メインのレジスタ実装
- `rtl/AXIUART_Top.sv` - トップレベルモジュール

### UVMファイル
- `sim/uvm/sequences/uart_axi4_reg_test_sequence.sv` - 既存の検証シーケンス
- `sim/uvm/tests/uart_axi4_reg_test_verification_test.sv` - 既存のテスト

### Pythonツール
- `software/test_registers_updated.py` - 動作実績のあるテストツール
- `software/fpga_write_read_test.py` - 書き込み・読み戻しテスト
- `software/fpga_reg_debug.py` - レジスタデバッグツール

### ドキュメント
- `docs/comprehensive_work_instructions_updated_20251007.md` - 包括的作業指示
- `docs/uart_axi4_protocol.md` - プロトコル仕様
- `docs/register_map.md` - レジスタマップ定義

---

**次のアクション**: Phase 1の作業1-1から開始し、fpga_memory_map_scan.pyの実装・実行を行う。