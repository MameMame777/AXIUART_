# 🎯 **新規作業者への具体的指示**

## **🚨 最重要：この環境は完成している**

**あなたがすべきこと：** この環境を**そのまま使用**することです。  
**避けるべきこと：** 環境を再構築することです。

---

## **⚡ 60秒で作業開始**

### **1. VSCodeでワークスペースを開く**
```bash
code e:\Nautilus\workspace\fpgawork\AXIUART_
```
→ MCPサーバーが自動起動します

### **2. 環境確認（必須コマンド）**
**Ctrl+Shift+P** → **"Tasks: Run Task"** → **"🚀 DSIM: Check Environment (Recommended)"**

または：
```bash
python mcp_server/mcp_client.py --workspace . --tool check_dsim_environment
```

### **3. 基本テスト実行**
**Ctrl+Shift+P** → **"Tasks: Run Task"** → **"🚀 DSIM: Compile Design (Agent AI)"**

---

## **📋 作業別指示**

### **A. RTL検証作業をする場合**

**手順：**
1. **利用可能テスト確認**
   ```bash
   python mcp_server/mcp_client.py --workspace . --tool list_available_tests
   ```

2. **テスト実行**
   ```bash
   python mcp_server/mcp_client.py --workspace . --tool compile_design --test-name uart_axi4_basic_test
   python mcp_server/mcp_client.py --workspace . --tool run_simulation --test-name uart_axi4_basic_test
   ```

3. **結果確認**
   ```bash
   # ログ確認
   cat sim/exec/logs/latest.log
   
   # 波形確認（必要に応じて）
   python mcp_server/mcp_client.py --workspace . --tool generate_waveforms --test-name uart_axi4_basic_test
   ```

### **B. 新しいテストを追加する場合**

**手順：**
1. **既存テスト参照** - `sim/tests/` ディレクトリ
2. **新テスト作成** - UVM形式で作成
3. **テスト登録** - `sim/tests/`に配置
4. **動作確認** - MCP Client経由で実行

### **C. RTLを修正する場合**

**手順：**
1. **現在の状態確認** - 基本テストでベースライン取得
2. **RTL修正** - `rtl/`ディレクトリ内
3. **即座に検証** - 修正後すぐにテスト実行
4. **問題対応** - エラーは即座に修正

---

## **⚠️ 絶対にやってはいけないこと**

### **❌ 環境を壊すアクション**
- **PowerShell環境の変更**
- **DSIM環境変数の変更**
- **MCPサーバーの停止**
- **Python依存関係の変更**

### **❌ 非推奨方法の使用**
- **直接スクリプト実行**: `python mcp_server/run_uvm_simulation.py` 
- **レガシータスク**: `⚠️`マーク付きタスク
- **手動コンパイル**: dsim直接実行

### **❌ ファイル構造の変更**
- **mcp_server/の移動・削除**
- **.vscode/tasks.jsonの変更**
- **環境設定ファイルの削除**

---

## **🛠️ トラブルシューティング**

### **問題1: コマンドが動かない**
**対処手順：**
1. VSCode再起動
2. MCPサーバー自動起動確認
3. 環境確認コマンド実行

### **問題2: テストが失敗する**
**対処手順：**
1. **環境確認**
   ```bash
   python mcp_server/mcp_client.py --workspace . --tool check_dsim_environment
   ```
2. **基本テスト実行**
   ```bash
   python mcp_server/mcp_client.py --workspace . --tool compile_design --test-name uart_axi4_basic_test
   ```
3. **ログ確認**
   ```bash
   cat sim/exec/logs/latest.log
   ```

### **問題3: 何をすればいいかわからない**
**確認順序：**
1. **QUICK_START.md** - 基本手順
2. **README.md** - プロジェクト概要
3. **この指示書** - 具体的作業手順

---

## **🎯 作業目標の設定**

### **短期目標（今日中）**
- [ ] 環境確認完了
- [ ] 基本テスト実行成功
- [ ] 利用可能テスト把握
- [ ] 作業計画策定

### **中期目標（1週間）**
- [ ] 対象テスト範囲の実行
- [ ] 問題点の特定
- [ ] 修正方針の決定
- [ ] 進捗報告準備

### **長期目標（プロジェクト全体）**
- [ ] 検証目標達成
- [ ] カバレッジ目標達成
- [ ] ドキュメント整備
- [ ] 成果物完成

---

## **📞 エスカレーション手順**

### **Level 1: 自己解決**
1. **QUICK_START.md**確認
2. **環境確認コマンド**実行
3. **基本的なトラブルシューティング**

### **Level 2: ドキュメント確認**
1. **README.md**の該当セクション
2. **docs/**内の関連文書
3. **実装レポート**確認

### **Level 3: 上位者相談**
- **環境が根本的に動作しない**
- **プロジェクト要件が不明**
- **技術的判断が必要**

---

## **✅ 最終チェックリスト**

### **作業開始前の確認**
- [ ] VSCodeでワークスペースが開かれている
- [ ] MCPサーバーが起動している
- [ ] 環境確認コマンドで全項目OK
- [ ] 基本テストが実行できる

### **日々の作業での確認**
- [ ] MCP Client経由で操作している
- [ ] 非推奨方法を使用していない
- [ ] 結果をログで確認している
- [ ] 進捗を記録している

### **完了時の確認**
- [ ] 目標達成状況の確認
- [ ] 成果物の整理
- [ ] ドキュメント更新
- [ ] 次回作業への引き継ぎ準備

---

## **🚀 成功の秘訣**

**この環境は92%ベストプラクティス準拠で設計されています。**

**成功の鍵：**
1. **環境をそのまま信頼して使用する**
2. **MCP Client方式を一貫して使用する**
3. **問題が起きたら即座に基本確認を行う**
4. **ドキュメントを活用する**

**あなたの仕事は「環境構築」ではなく「実際の検証作業」です。この完成された環境を活用して、効率的に成果を出してください。**