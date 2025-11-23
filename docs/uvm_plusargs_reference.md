# UVM Plusargs リファレンス

## 標準UVMオプション（IEEE 1800.2 LRM準拠）

### +UVM_TESTNAME=<class_name>
**説明**: 実行するuvm_testまたはuvm_componentクラスを指定  
**使用例**: `vsim testbench +UVM_TESTNAME="block_test"`  
**注意**: 複数指定時は最初の値が使用され、以降は警告が出る

---

### +UVM_VERBOSITY=<verbosity>
**説明**: 全コンポーネントの初期verbosityレベルを指定  
**使用例**: `vsim testbench +UVM_VERBOSITY=UVM_HIGH`  
**値**: 
- `UVM_NONE`
- `UVM_LOW`
- `UVM_MEDIUM`
- `UVM_HIGH`
- 整数値も可

**注意**: 複数指定時は最初の値が使用され、以降は警告が出る

---

### +UVM_TIMEOUT=<timeout>,<overridable>
**説明**: UVMフレームワークのグローバルタイムアウトを変更  
**使用例**: `vsim testbench +UVM_TIMEOUT=1000000,NO`

**パラメータ**:
- **`<timeout>`**: 整数値（**ns単位**）
  - ms/us指定は不可
  - 例: `1000000` = 1ms, `10000000` = 10ms
- **`<overridable>`**: `YES` or `NO`
  - `YES` (デフォルト): ユーザーコードから`set_timeout()`で変更可能
  - `NO`: 変更不可、変更試行時に警告発生

**動作**: 
- 指定時間内にすべてのobjectionが解決されない場合、警告メッセージが生成される
- グローバルタイムアウト値の変更を試みると警告が出る（`NO`設定時）

---

## Accellera UVM実装固有のオプション

### +UVM_TIMEOUT=<timeout>,<overridable>
**説明**: （上記と同じ - Accellera実装でも利用可能）  
**使用例**: `vsim testbench +UVM_TIMEOUT=1000000,NO`

**パラメータ**:
- **`<timeout>`**: 整数値（**ns単位**）
- **`<overridable>`**: `YES` or `NO`

**動作詳細**:
- タイムアウト値は整数ns単位で指定
- ms/us等の時間指定子は現在使用不可
- `<overridable>`が`NO`の場合、ユーザーコードからグローバルタイムアウト変更を試みると警告
- デフォルトの`<overridable>`値は`YES`

---

### +UVM_PHASE_TRACE
**説明**: フェーズ実行のトレースを有効化  
**使用例**: `vsim testbench +UVM_PHASE_TRACE`

**動作**:
- 引数不要（コマンドラインに記述するだけ）
- フェーズ実行状況を詳細にトレース
- 出力例:
  ```
  UVM_INFO [PH/TRC/STRT] Phase 'common.run' Starting phase
  UVM_INFO [PH/TRC/SKIP] Phase 'uvm.uvm_sched.reset' No objections raised, skipping phase
  UVM_INFO [PH/TRC/DONE] Phase 'common.run' Completed phase
  ```

---

### +UVM_OBJECTION_TRACE
**説明**: objection動作のトレースを有効化  
**使用例**: `vsim testbench +UVM_OBJECTION_TRACE`

**動作**:
- 引数不要（コマンドラインに記述するだけ）
- objectionのraise/drop時に詳細情報を表示
- descriptionが提供されている場合も表示
- 出力例:
  ```
  UVM_INFO [OBJTN_TRC] Object uvm_test_top raised 1 objection(s) (Executing DUT reset): count=1 total=1
  UVM_INFO [OBJTN_TRC] Object uvm_test_top dropped 1 objection(s) (Reset completed): count=0 total=0
  ```

---

### +UVM_RESOURCE_DB_TRACE
**説明**: リソースDBアクセスのトレースを有効化  
**使用例**: `vsim testbench +UVM_RESOURCE_DB_TRACE`

**動作**:
- 引数不要（コマンドラインに記述するだけ）
- リソースDB（Resource Database）アクセス時にトレース情報を出力

---

### +UVM_CONFIG_DB_TRACE
**説明**: コンフィグDBアクセスのトレースを有効化  
**使用例**: `vsim testbench +UVM_CONFIG_DB_TRACE`

**動作**:
- 引数不要（コマンドラインに記述するだけ）
- コンフィグDB（Configuration Database）アクセス時にトレース情報を出力

---

## 実践的な使用例

### デバッグ用推奨設定（ハング調査）
```bash
vsim testbench \
  +UVM_TESTNAME=uart_axi4_basic_test \
  +UVM_VERBOSITY=UVM_MEDIUM \
  +UVM_TIMEOUT=10000000,NO \
  +UVM_PHASE_TRACE \
  +UVM_OBJECTION_TRACE
```

**効果**:
- 10ms（10,000,000ns）でタイムアウト（上書き不可）
- フェーズ遷移とobjection動作を詳細トレース
- ハング箇所の特定が容易

### 通常実行用設定
```bash
vsim testbench \
  +UVM_TESTNAME=uart_axi4_basic_test \
  +UVM_VERBOSITY=UVM_LOW
```

---

## 注意事項

1. **タイムアウト値の単位**
   - 必ず**ns（ナノ秒）単位の整数値**で指定
   - `1ms`や`10us`等の時間指定子は使用不可
   - 例: 1ms = `1000000`, 10ms = `10000000`

2. **overridableの挙動**
   - `NO`設定時、テストコードから`set_timeout()`を呼ぶと警告が出る
   - グローバルタイムアウトは変更されない

3. **トレースオプションの組み合わせ**
   - `+UVM_PHASE_TRACE`と`+UVM_OBJECTION_TRACE`は併用可能
   - デバッグ時は両方有効化を推奨

4. **verbosityとトレースの違い**
   - `+UVM_VERBOSITY`: テストコード内の`uvm_info`等の出力レベル制御
   - トレースオプション: UVMフレームワーク内部動作の可視化

---

**参考文献**:
- IEEE 1800.2 UVM LRM
- Accellera UVM 1.2 User Guide
- DSIM 2025.1 Documentation

**最終更新**: 2025-11-23
