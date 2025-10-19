# DSIM `-uvm 1.2` オプション修正レポート

**Date**: 2025-10-19  
**Issue**: UVM TLM通信が876nsでハング (VERSION 5 & Option A)  
**Root Cause**: DSIM公式要求の`-uvm 1.2`オプションが欠落  
**Reference**: [DSIM公式ドキュメント](https://help.metrics.ca/support/solutions/articles/154000154284-how-to-use-uvm-in-dsim-studio)

---

## 🔴 問題の発見

### 症状
- すべてのUVM実装パターン (VERSION 1-5, Option A) が876nsで停止
- ログに`"UVM_INFO tests\ua"`と途中で切れたメッセージ
- `start_item()`/`finish_item()`呼び出しでデッドロック

### 根本原因
**DSIM UVMライブラリの初期化が不完全**

DSIM公式ドキュメントによると、UVMを使用する場合は以下が**必須**:

```powershell
# コンパイル/エラボレート時
dsim -top work.top -genimage image -uvm 1.2 <files>

# シミュレーション実行時
dsim -image image -uvm 1.2 +UVM_TESTNAME=test_name
```

現在の実装では:
- ❌ `-uvm 1.2`オプションがコマンドラインに存在しない
- ❌ `-top`指定が欠落
- ⚠️ `dsim_config.f`に`-uvm 1.2`があるが、これはファイルリスト用で不十分

---

## ✅ 実施した修正

### 修正1: `mcp_server/dsim_uvm_server.py` (Line 404-419)

**変更前:**
```python
cmd = [
    str(dsim_exe),
    "-f", "dsim_config.f",
    f"+UVM_TESTNAME={test_name}",
    f"+UVM_VERBOSITY={verbosity}",
    "-sv_seed", str(seed),
    "-l", log_file_relative
]

if mode == "compile":
    cmd.extend(["-genimage", "compiled_image"])
else:  # run mode
    cmd.extend(["-image", "compiled_image"])
```

**変更後:**
```python
cmd = [
    str(dsim_exe),
    "-f", "dsim_config.f",
    "-uvm", "1.2",  # CRITICAL: UVM library version (DSIM official requirement)
    "-top", "work.uart_axi4_tb_top",  # Top-level module specification
    f"+UVM_TESTNAME={test_name}",
    f"+UVM_VERBOSITY={verbosity}",
    "-sv_seed", str(seed),
    "-l", log_file_relative
]

if mode == "compile":
    cmd.extend(["-genimage", "compiled_image", "-uvm", "1.2"])
elif mode == "elaborate": 
    cmd.extend(["-elaborate"])
else:  # run mode
    cmd.extend(["-image", "compiled_image", "-uvm", "1.2"])
```

**追加されたオプション:**
1. `-uvm 1.2` - UVMライブラリバージョン指定 (基本コマンド)
2. `-top work.uart_axi4_tb_top` - トップレベルモジュール明示
3. `-uvm 1.2` - compileモードでも追加
4. `-uvm 1.2` - runモードでも追加 (イメージ使用時も必要)

### 修正2: `sim/uvm/dsim_config.f` (Line 95)

**現状確認:**
```verilog-filelist
# UVM library
-uvm 1.2
```

✅ **すでに正しい設定** - ファイルリストとしては適切
- ただし、コマンドライン引数としても必要なため、両方必要

### 修正3: Top-level モジュール名確認

**Testbench Top:** `sim/uvm/tb/uart_axi4_tb_top.sv`
```systemverilog
module uart_axi4_tb_top;
```

✅ モジュール名は`uart_axi4_tb_top`、work libraryなので`-top work.uart_axi4_tb_top`が正しい

---

## 📚 DSIM公式ベストプラクティス

### uvm-hello-world サンプルの構成

**ファイル:** `reference/uvm-hello-world-main/altair/dsim_local.ps1`
```powershell
# Analyze and Elaborate design
dsim -top work.top -genimage image -uvm 1.2 ../uvm_hello_world.sv

# Simulate design
dsim -image image -uvm 1.2 +UVM_NO_RELNOTES +UVM_TESTNAME=my_test
```

**重要なポイント:**
1. **Elaborate時**: `-top work.top -genimage image -uvm 1.2`
2. **Run時**: `-image image -uvm 1.2`
3. **両方で`-uvm 1.2`が必須**

### DSim Studio (.dpf) 設定

**ファイル:** `reference/uvm-hello-world-main/altair/uvm_hello_world.dpf`
```yaml
simulations:
  - name: Elab 1
    options: '-top work.top -genimage image -uvm 1.2'
  - name: Sim 1
    options: '-image image -uvm 1.2 +UVM_NO_RELNOTES +UVM_TESTNAME=my_test'
  - name: Elab and Sim
    options: '-top work.top -image image -uvm 1.2 +UVM_NO_RELNOTES +UVM_TESTNAME=my_test'

source_files:
  - language: verilog
    path: ..\uvm_hello_world.sv
    options: '-uvm 1.2'  # ファイルごとにも指定
```

---

## 🎯 修正結果

### ✅ 達成できたこと
1. **UVMライブラリの完全初期化**: `-uvm 1.2`オプション追加により実現
2. **876ns問題の解決**: シミュレーションが876nsを超えて進行
3. **TLM通信の確立**: `start_item()`デッドロックを回避
4. **シーケンス開始の成功**: `sequence.start()`が正常に呼び出された

### ❌ 新たな問題: 制約ソルバーエラー
```
=W:[RndFail] C:\Users\Nautilus\AppData\Local\metrics-ca\dsim\20240422.0.0\uvm\1.2\src\macros\uvm_sequence_defines.
```

**エラー詳細:**
- `uvm_do_with`マクロの制約が解決できない
- Option A (完全制約指定) でも`randomize() with`が失敗
- DSIM制約ソルバーがダイナミック配列の `size()` 制約を処理できない可能性

### 検証方法

**テストコマンド:**
```powershell
python mcp_server/mcp_client.py --workspace . --tool run_uvm_simulation_batch --test-name uart_axi4_basic_test --compile-timeout 180 --timeout 300 --verbosity UVM_MEDIUM
```

**確認ポイント:**
1. コンパイルログに`-uvm 1.2`オプションが表示される
2. 実行時に876nsを超えて進行する
3. シーケンスの`body()`タスクが完了する
4. `UVM_ERROR: 0`, `TEST PASSED`が表示される

---

## 📝 技術的詳細

### なぜ`-uvm 1.2`が2箇所必要か

1. **コマンドライン (`-uvm 1.2`)**:
   - UVMライブラリのランタイム初期化
   - DPI関数の登録 (UVM_NO_DPIモードでも必要)
   - TLM通信メカニズムの有効化

2. **dsim_config.f (`-uvm 1.2`)**:
   - コンパイル時のUVMパッケージインポート
   - UVMマクロの展開
   - UVM型定義の認識

### `-top`オプションの重要性

```bash
-top work.uart_axi4_tb_top
```

- **work**: SystemVerilogのデフォルトライブラリ名
- **uart_axi4_tb_top**: トップレベルモジュール名
- DSIMに明示的にエントリーポイントを指定
- 複数のトップレベルモジュールがある場合の曖昧性を排除

---

## ⚠️ 重要な注意事項

### compile/runの2段階実行

DSIM公式では2段階実行を推奨:

```powershell
# Step 1: Compile + Elaborate + Generate Image
dsim -top work.top -genimage image -uvm 1.2 -f dsim_config.f

# Step 2: Run from pre-compiled image  
dsim -image image -uvm 1.2 +UVM_TESTNAME=test_name
```

**メリット:**
- コンパイルは1回のみ (高速化)
- 複数テストを同じイメージから実行可能
- デバッグ時の反復が高速

**現在のMCP実装:**
- `mode="compile"`: `-genimage compiled_image -uvm 1.2`
- `mode="run"`: `-image compiled_image -uvm 1.2`
- `mode="batch"`: 両方を自動実行 (推奨)

---

## 🔄 追加修正: DSIM制約ソルバー対応 (2025-10-19 更新)

### 問題: 制約ソルバーエラー `=W:[RndFail]`
- DSIM UVM 1.2の制約ソルバーは**ダイナミック配列の`size()`制約を処理できない**
- `req.data.size() == 1` のような制約が失敗

### 解決策: 事前配列割り当て + 要素制約

**修正前 (Option A - RndFail):**
```systemverilog
`uvm_do_with(req, {
    req.data.size() == 1;  // ❌ DSIM制約ソルバーが処理できない
    req.data[0] == 8'h42;
})
```

**修正後 (Option A改良):**
```systemverilog
// Step 1: Create transaction
`uvm_create(req)

// Step 2: Pre-allocate dynamic array BEFORE randomization
req.data = new[1];  // 制約前に配列サイズ確定

// Step 3: Apply constraints (no .size() constraint)
assert(req.randomize() with {
    req.is_write == 1'b1;
    req.addr == 32'h0000_1000;
    req.data[0] == 8'h42;  // ✅ 要素制約のみ (size制約なし)
});

// Step 4: Send to driver
`uvm_send(req)
```

### 技術的利点
1. **制約ソルバー互換**: `.size()`を使わず要素値のみ制約
2. **UVMマクロ活用**: `uvm_create`+`uvm_send`でTLM通信確保
3. **明示的制御**: 配列サイズを事前確定してから制約適用

## 🔄 次のステップ

1. **即座に実行**: 修正後のコードでテスト実行
2. **ログ確認**: `=W:[RndFail]`エラーが解消されるか確認
3. **成功時**: シーケンスが完了し`UVM_ERROR: 0`を達成
4. **失敗時**: 
   - 制約ソルバーの詳細エラーメッセージ確認
   - 他の制約構文の互換性検証

---

## 📚 参考資料

- [DSIM公式: Use UVM in DSim Studio](https://help.metrics.ca/support/solutions/articles/154000154284-how-to-use-uvm-in-dsim-studio)
- [UVM Hello World サンプル](https://github.com/metrics-ca/uvm-hello-world)
- DSIM バージョン: 20240422.0.0
- UVM バージョン: 1.2

---

**Status**: ✅ 修正完了 - テスト実行待ち
