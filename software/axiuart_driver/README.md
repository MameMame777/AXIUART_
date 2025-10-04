# AXIUART Driver

AXIUART COMポート通信ドライバーソフトウェア

## 概要

FPGA上に実装されたAXIUARTシステムとPC間でのCOMポート経由通信を実現するPythonライブラリです。

## 機能

- UART-AXI4プロトコル実装
- レジスタアクセス（読み取り/書き込み）
- RTS/CTSフロー制御対応
- GUI版・CLI版両対応
- 包括的なテスト機能

## インストール

```bash
pip install -r requirements.txt
```

## 使用例

### 基本的なレジスタアクセス

```python
from core.com_manager import COMManager
from core.uart_protocol import UARTProtocol
from core.register_map import RegisterMap

# 接続
com = COMManager()
com.connect("COM3", 115200)
protocol = UARTProtocol(com)

# レジスタ読み取り
version = protocol.register_read(RegisterMap.VERSION)
print(f"Version: 0x{version:08X}")

# レジスタ書き込み
protocol.register_write(RegisterMap.CONTROL, RegisterMap.CONTROL_BRIDGE_ENABLE)
```

### GUI版起動

```bash
python gui/main_window.py
```

### CLI版使用

```bash
python cli/cli_main.py --port COM3 --read 0x1000
python cli/cli_main.py --port COM3 --write 0x1000 0x00000001
```

## ディレクトリ構成

- `core/`: コアライブラリ
- `gui/`: GUI実装
- `cli/`: CLI実装  
- `tests/`: テストコード
- `examples/`: 使用例

## 開発状況

- [x] プロジェクト構造
- [ ] コア機能実装
- [ ] GUI実装
- [ ] テスト実装