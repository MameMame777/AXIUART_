# FPGA Register Access Scripts Usage Guide

このディレクトリには、UART-AXI4-Lite Bridge Protocol v0.1に準拠したFPGAレジスタアクセス用のPythonスクリプトが含まれています。

## 必要な環境

- Python 3.7以上
- pyserial ライブラリ

```bash
pip install pyserial
```

## スクリプト一覧

### 1. uart_axi_register_access.py
基本的なUART-AXI4ブリッジライブラリです。プロトコル仕様に完全準拠した実装。

**主要機能:**
- 32/16/8ビットレジスタアクセス
- バーストリード（最大16レジスタ）
- CRC8による通信エラー検出
- 自動リトライ機能
- プロトコル準拠のフレーム構築・解析

**基本的な使用例:**
```python
from uart_axi_register_access import UartAxiBridge, AccessSize

# 接続
bridge = UartAxiBridge("COM3", 115200)
bridge.connect()

# レジスタ読み取り
value = bridge.read_register(0x00001000)  # 32ビット読み取り
print(f"Register value: 0x{value:08X}")

# レジスタ書き込み
bridge.write_register(0x00001000, 0x12345678)

# バーストリード
values = bridge.read_burst(0x00001000, 4)  # 4つのレジスタを連続読み取り

bridge.disconnect()
```

### 2. fpga_register_test.py
包括的なレジスタテストスイートです。FPGA実装の動作確認に使用。

**テスト項目:**
- 基本レジスタアクセス（読み取り専用/読み書き可能）
- データ幅テスト（8/16/32ビット）
- バーストリードテスト
- エラー条件テスト（不正アドレス、アライメント等）
- パフォーマンステスト

**実行方法:**
```bash
# デフォルト（COM3）で実行
python fpga_register_test.py

# 別のポートを指定
python fpga_register_test.py COM4
```

### 3. crc8_validation.py
CRC8実装の検証スクリプトです。プロトコル仕様のテストベクターで検証。

**実行方法:**
```bash
python crc8_validation.py
```

## インタラクティブ使用

uart_axi_register_access.pyを直接実行すると、インタラクティブモードになります：

```bash
python uart_axi_register_access.py
```

**使用可能コマンド:**
- `r <addr>` - 32ビットレジスタ読み取り
- `w <addr> <value>` - 32ビットレジスタ書き込み  
- `rb <addr> <count>` - バーストリード
- `test` - 基本動作テスト
- `quit` - 終了

**例:**
```
> r 0x1000              # アドレス0x1000を読み取り
> w 0x1000 0x12345678   # アドレス0x1000に0x12345678を書き込み
> rb 0x1000 4           # アドレス0x1000から4つのレジスタを読み取り
> test                  # 基本テスト実行
```

## レジスタマップ

プロジェクトで定義されているレジスタアドレス：

| アドレス | レジスタ名 | アクセス | 説明 |
|----------|------------|----------|------|
| 0x00001000 | CONTROL | RW | コントロールレジスタ |
| 0x00001004 | STATUS | RO | ステータスレジスタ |
| 0x00001008 | CONFIG | RW | 設定レジスタ |
| 0x0000100C | DEBUG | RW | デバッグコントロール |
| 0x00001010 | TX_COUNT | RO | TX カウンタ |
| 0x00001014 | RX_COUNT | RO | RX カウンタ |
| 0x00001018 | FIFO_STAT | RO | FIFO ステータス |
| 0x0000101C | VERSION | RO | バージョンレジスタ |

## エラーコード

プロトコル仕様で定義されているエラーコード：

| コード | 名前 | 説明 |
|--------|------|------|
| 0x00 | OK | 成功 |
| 0x01 | CRC_ERR | CRCエラー |
| 0x02 | CMD_INV | 無効なコマンド |
| 0x03 | ADDR_ALIGN | アドレスアライメントエラー |
| 0x04 | TIMEOUT | タイムアウト |
| 0x05 | AXI_SLVERR | AXIスレーブエラー |
| 0x06 | BUSY | デバイスビジー |
| 0x07 | LEN_RANGE | 長さ範囲エラー |

## トラブルシューティング

### 接続エラー
- COMポートが正しく指定されているか確認
- 他のアプリケーションがポートを使用していないか確認
- FPGAが正しく設定されているか確認

### 通信エラー
- ボーレートが正しく設定されているか確認（デフォルト：115200）
- UARTケーブル接続を確認
- FPGAのクロック設定を確認

### CRCエラー
- UART通信の信号品質を確認
- ケーブル長やノイズの影響を確認
- ボーレート設定を下げて試行

### タイムアウトエラー
- FPGAのAXI4-Liteバスの応答を確認
- レジスタアドレスが正しいか確認
- システムクロックが正常に動作しているか確認

## 開発・デバッグ

### ログの有効化
```python
import logging
logging.basicConfig(level=logging.DEBUG)
```

### フレーム内容の確認
```python
# 送信フレームの表示
frame = bridge.build_read_frame(0x1000, 1, AccessSize.DWORD)
print("TX Frame:", " ".join(f"{b:02X}" for b in frame))

# 受信フレームの表示  
response = bridge.send_frame_with_retry(frame)
print("RX Frame:", " ".join(f"{b:02X}" for b in response))
```

### パフォーマンス測定
```python
import time

# レイテンシ測定
start = time.time()
value = bridge.read_register(0x1000)
latency = time.time() - start
print(f"Read latency: {latency*1000:.1f} ms")
```

## プロトコル仕様参照

詳細な仕様については、`docs/uart_axi4_protocol.md`を参照してください。