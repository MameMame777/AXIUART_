# AXIUART Simplified UVM Environment (UBUS Style)

## 概要

UBUSリファレンス実装を参考に、AXIUART UVM環境を大幅に簡素化しました。

## ディレクトリ構造

```
sim/uvm_simplified/
├── sv/                           # すべてのUVMコンポーネント (UBUSスタイル)
│   ├── axiuart_pkg.sv           # メインパッケージ (1ファイル)
│   ├── uart_transaction.sv      # トランザクション
│   ├── uart_monitor.sv          # UARTモニター
│   ├── uart_driver.sv           # UARTドライバー
│   ├── uart_sequencer.sv        # UARTシーケンサー
│   ├── uart_agent.sv            # UARTエージェント
│   ├── axi4_lite_monitor.sv     # AXIモニター (観測のみ)
│   ├── axiuart_scoreboard.sv    # スコアボード
│   └── axiuart_env.sv           # トップ環境
└── tb/                          # テストベンチ
    ├── axiuart_tb_top.sv        # トップモジュール
    └── axiuart_basic_test.sv    # 基本テスト
```

## 主な簡素化ポイント

### 1. ファイル数の削減
- **旧環境**: 49個のSystemVerilogファイル (agents/, env/, scoreboard/, analysis/ などに分散)
- **新環境**: 10個のファイル (sv/ と tb/ に集約)

### 2. 削除したコンポーネント

#### 重複スコアボード
- `uart_axi4_enhanced_scoreboard.sv` → 削除
- `uart_axi4_scoreboard.sv` → 統合
- `correlation_engine.sv` → 統合

#### 重複カバレッジ
- `uart_axi4_phase3_coverage.sv` → 削除
- `system_coverage.sv` → 削除  
- `axiuart_cov_pkg.sv` → 削除

#### 過剰な分離
- `uart_axi4_predictor.sv` → 削除
- `uart_axi4_error_detector.sv` → 削除
- `bridge_status_monitor.sv` → 削除
- `independent_verification_monitor.sv` → 削除

#### 設定クラス
- `uart_axi4_env_config.sv` → 削除 (シンプルなVIF設定のみ使用)

### 3. トランザクションの簡素化
- **旧**: 158行 (20個以上のフィールド、複雑な制約)
- **新**: 47行 (基本フィールドのみ)

### 4. モニターの簡素化
- **旧**: 890行 (RX/TXの複雑なステートマシン)
- **新**: 78行 (シンプルなフレーム収集)

### 5. ドライバーの簡素化
- **旧**: 351行 (baud rate動的変更、reset処理、複雑なフロー制御)
- **新**: 98行 (8N1フォーマットの基本送信)

### 6. 環境の簡素化
- **旧**: 191行 (複数のanalysisコンポーネント、複雑な接続)
- **新**: 68行 (Agent + Monitor + Scoreboardのみ)

## UBUS参考ポイント

1. **1パッケージファイル**: すべてのコンポーネントを`axiuart_pkg.sv`に集約
2. **シンプルな階層**: Agent → Driver/Monitor/Sequencer → Env
3. **VIF設定**: `uvm_config_db`でVirtual Interfaceを渡すだけ
4. **スコアボード**: FIFOベースの単純な比較
5. **テスト**: Sequence→Agent→Driverの明確なフロー

## 既存環境との比較

| 項目 | 旧環境 | 新環境 (UBUS Style) |
|------|--------|---------------------|
| ファイル数 | 49個 | 10個 |
| 総行数 | ~5000行 | ~600行 |
| ディレクトリ数 | 10個 | 2個 |
| スコアボード | 3個 | 1個 |
| カバレッジ | 3個 | 0個 (必要に応じて追加) |
| 設定クラス | 複雑 | なし (VIFのみ) |

## 使用方法

### コンパイル
```bash
dsim -work work \
     +incdir+sv \
     sv/axiuart_pkg.sv \
     tb/axiuart_tb_top.sv \
     tb/axiuart_basic_test.sv
```

### 実行
```bash
dsim -work work \
     +UVM_TESTNAME=axiuart_basic_test \
     tb_top
```

## 今後の拡張

必要に応じて以下を追加:
1. **カバレッジ**: UBUSの`ubus_example_scoreboard.sv`を参考
2. **複数シーケンス**: `seq_lib`パターン
3. **設定**: 必要最小限のconfigクラス

## 削除対象の旧環境ファイル

以下のディレクトリは削除推奨:
- `sim/uvm/analysis/`
- `sim/uvm/components/`
- `sim/uvm/scoreboard/` (重複スコアボード)
- `sim/uvm/env/` (重複ファイル)

保持推奨:
- `rtl/interfaces/uart_if.sv` (interface定義)
- `rtl/interfaces/axi4_lite_if.sv` (interface定義)

## 参考文献
- UBUSリファレンス: `reference/Accellera/uvm/distrib/examples/integrated/ubus`
- UVM Cookbook: Simple agent pattern
