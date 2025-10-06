# デバッグ作業開始ガイド - October 7, 2025

## 🚀 **即座に開始可能な作業手順**

### 準備作業（5分）
```powershell
# 1. 作業ディレクトリ移動
cd E:\Nautilus\workspace\fpgawork\AXIUART_

# 2. Todo状態確認
# (manage_todo_list toolで現在の状態を確認)

# 3. Git状態確認
git status
git log --oneline -5
```

### Phase 1 開始 - CRCエラー解決

#### Step 1-1: エラー詳細分析（10分）
```powershell
# UVMログファイルでCRCエラー確認
cd sim\uvm
type dsim.log | findstr /i "crc"
type dsim.log | findstr /i "expected.*received"

# 結果を記録
# - recv=0x44 exp=0x12
# - recv=0x78 exp=0x4a
```

#### Step 1-2: RTL実装確認（15分）
```powershell
# Frame_Parser.sv のCRC実装確認
cd ..\..\rtl
findstr /n /i "crc" Frame_Parser.sv
# 発見した行番号周辺を詳細確認
```

#### Step 1-3: 参照実装作成（20分）
```powershell
# Python参照実装作成
cd ..\temporary
# crc_reference.py を作成
```

Python参照実装テンプレート：
```python
def crc8_calc(data, polynomial=0x07, init=0x00):
    """CRC8計算 - 多項式0x07"""
    crc = init
    for byte in data:
        crc ^= byte
        for _ in range(8):
            if crc & 0x80:
                crc = (crc << 1) ^ polynomial
            else:
                crc <<= 1
            crc &= 0xFF
    return crc

# テストケース
test_data = [0x5A, 0x01, 0x04, 0x44, 0x44, 0x44, 0x44]  # UVMで使用しているデータ
expected_crc = crc8_calc(test_data)
print(f"Expected CRC: 0x{expected_crc:02X}")
```

### 効率的な作業のポイント

#### 1. チェックリスト活用
- [ ] 各Stepの作業開始前に該当チェックリストを開く
- [ ] 1項目ずつ確実に実行・記録
- [ ] 完了項目にチェックマークを付ける

#### 2. 問題発見時の対応
```powershell
# 即座に現象を記録
echo "問題: [具体的な内容]" >> debug_log.txt
echo "発生時刻: $(Get-Date)" >> debug_log.txt
echo "条件: [再現条件]" >> debug_log.txt
```

#### 3. 修正作業時の安全対策
```powershell
# バックアップ作成（必須）
copy Frame_Parser.sv Frame_Parser.sv.backup_$(Get-Date -Format "yyyyMMdd_HHmm")

# 修正後の検証
cd ..\sim\uvm
.\run_uvm.ps1 -mode compile
# コンパイル成功を確認してから次の作業
```

#### 4. 進捗管理
```powershell
# 作業完了時
git add -A
git commit -m "Phase1 Step1-1: CRCエラー詳細分析完了 - [具体的な発見事項]"

# Todo更新
# manage_todo_list toolで進捗を更新
```

### 緊急時のロールバック手順
```powershell
# 最新のバックアップに戻す
cd rtl
copy Frame_Parser.sv.backup Frame_Parser.sv

# 前回の動作確認済み状態に戻す
git reset --hard HEAD~1

# 環境再確認
cd ..\sim\uvm
.\run_uvm.ps1 -mode compile
```

### 成功判定の明確な基準

#### Phase 1 成功条件
- [ ] CRCエラーが発生しない（dsim.logで確認）
- [ ] UVM_ERROR: 0 で実行完了
- [ ] フレーム検証が全て成功
- [ ] 新たなエラーが発生していない

#### 品質確認項目
- [ ] コンパイルエラーなし
- [ ] 波形ファイル正常生成
- [ ] Git管理済み
- [ ] チェックリスト全項目完了

### 次Phase移行のタイミング
1. **現Phase完了条件**をすべて満たす
2. **品質確認項目**をすべてクリア
3. **Todo管理**で完了状態に更新
4. **Git commit**で作業内容を保存
5. **次Phaseのin-progress**に変更

---

## 📞 **サポート情報**

### よくある問題と対処法
1. **コンパイルエラー**: バックアップからロールバック後、段階的修正
2. **UVMテスト失敗**: 前回成功時の状態に戻して比較分析
3. **波形ファイル未生成**: DSIM環境変数とディスク容量を確認
4. **Git競合**: 作業前にpullして最新状態で作業開始

### 効率化のコツ
- **小さな変更**: 1度に大量修正せず、小刻みに確認
- **ログ活用**: dsim.logを常に確認し、変化を追跡
- **波形確認**: 期待動作と実際の動作を波形で比較
- **文書化**: 発見事項を即座に記録

---

**準備完了。Phase 1 Step 1-1 からデバッグ作業を開始してください！**