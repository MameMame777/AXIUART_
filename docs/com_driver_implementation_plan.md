# AXIUART COMドライバー実装計画書

## 技術選択の決定

### 開発言語・フレームワーク選択

**決定**: **Python 3.9+ with tkinter/PyQt5**

**理由**:
1. **クロスプラットフォーム対応**: Windows, macOS, Linux対応
2. **シリアル通信ライブラリ**: pyserialの安定性と豊富な機能
3. **開発効率**: プロトタイピングから製品化まで短期間で実現
4. **保守性**: 可読性が高く、今後の機能拡張が容易
5. **テスト環境**: pytestによる包括的テスト実装

### アーキテクチャ設計

```python
axiuart_driver/
├── core/                    # コアライブラリ
│   ├── __init__.py
│   ├── uart_protocol.py     # UART-AXI4プロトコル実装
│   ├── com_manager.py       # COMポート管理
│   ├── register_map.py      # レジスタマップ定義
│   └── crc_calculator.py    # CRC-8計算
├── gui/                     # GUI実装
│   ├── __init__.py
│   ├── main_window.py       # メインウィンドウ
│   ├── register_panel.py    # レジスタアクセスパネル
│   ├── monitor_panel.py     # ステータス監視パネル
│   └── test_panel.py        # テスト実行パネル
├── cli/                     # CLI実装
│   ├── __init__.py
│   └── cli_main.py          # コマンドライン版
├── tests/                   # テストコード
│   ├── test_protocol.py
│   ├── test_crc.py
│   └── test_registers.py
├── examples/                # 使用例
│   ├── basic_access.py
│   ├── flow_control_test.py
│   └── performance_test.py
├── requirements.txt         # 依存関係
├── setup.py                # インストールスクリプト
└── README.md               # 使用方法
```

## Phase 1: 基本通信機能実装

### 必要なライブラリ

```python
# requirements.txt
pyserial>=3.5
tkinter  # 標準ライブラリ
matplotlib>=3.5.0
numpy>=1.21.0
pytest>=7.0.0
```

### 1.1 COMポート管理クラス

**実装ファイル**: `core/com_manager.py`

**主要機能**:
- 利用可能ポートの自動検出
- シリアルポート接続・切断
- 通信パラメータ設定
- RTS/CTS制御

**主要メソッド**:
```python
class COMManager:
    def __init__(self):
        self.port = None
        self.is_connected = False
        
    def scan_ports(self) -> List[str]:
        """利用可能なCOMポートをスキャン"""
        
    def connect(self, port_name: str, baudrate: int = 115200) -> bool:
        """指定ポートに接続"""
        
    def disconnect(self) -> None:
        """接続を切断"""
        
    def set_flow_control(self, rts: bool, cts: bool) -> None:
        """フロー制御設定"""
        
    def write_data(self, data: bytes) -> int:
        """データ送信"""
        
    def read_data(self, timeout: float = 0.1) -> bytes:
        """データ受信"""
```

### 1.2 UART-AXI4プロトコルクラス

**実装ファイル**: `core/uart_protocol.py`

**主要機能**:
- フレーム構築・解析
- CRC計算・検証
- コマンド生成
- エラーハンドリング

**主要メソッド**:
```python
class UARTProtocol:
    SOF_REQUEST = 0xA5
    SOF_RESPONSE = 0x5A
    
    def __init__(self, com_manager: COMManager):
        self.com = com_manager
        
    def build_read_frame(self, addr: int, size: int, length: int) -> bytes:
        """READフレーム構築"""
        
    def build_write_frame(self, addr: int, size: int, data: bytes) -> bytes:
        """WRITEフレーム構築"""
        
    def parse_response(self, frame: bytes) -> Tuple[int, bytes]:
        """応答フレーム解析"""
        
    def register_read(self, addr: int, size: int = 32) -> int:
        """レジスタ読み取り"""
        
    def register_write(self, addr: int, value: int, size: int = 32) -> bool:
        """レジスタ書き込み"""
```

### 1.3 CRC-8計算クラス

**実装ファイル**: `core/crc_calculator.py`

```python
class CRC8:
    POLYNOMIAL = 0x07
    
    @staticmethod
    def calculate(data: bytes, offset: int = 0, length: int = None) -> int:
        """CRC-8計算 (多項式0x07, init=0x00)"""
        if length is None:
            length = len(data) - offset
            
        crc = 0x00
        for i in range(offset, offset + length):
            crc ^= data[i]
            for _ in range(8):
                if crc & 0x80:
                    crc = ((crc << 1) ^ CRC8.POLYNOMIAL) & 0xFF
                else:
                    crc = (crc << 1) & 0xFF
        return crc
    
    @staticmethod
    def verify(data: bytes, expected_crc: int) -> bool:
        """CRC検証"""
        calculated = CRC8.calculate(data[:-1])  # CRC以外の部分
        return calculated == expected_crc
```

### 1.4 レジスタマップ定義

**実装ファイル**: `core/register_map.py`

```python
class RegisterMap:
    BASE_ADDR = 0x1000
    
    # レジスタ定義
    CONTROL = BASE_ADDR + 0x000
    STATUS = BASE_ADDR + 0x004
    CONFIG = BASE_ADDR + 0x008
    DEBUG = BASE_ADDR + 0x00C
    TX_COUNT = BASE_ADDR + 0x010
    RX_COUNT = BASE_ADDR + 0x014
    FIFO_STAT = BASE_ADDR + 0x018
    VERSION = BASE_ADDR + 0x01C
    
    # フィールド定義
    CONTROL_BRIDGE_ENABLE = 0x01
    CONTROL_RESET_STATS = 0x02
    
    # ステータスコード
    STATUS_SUCCESS = 0x00
    STATUS_CRC_ERR = 0x01
    STATUS_TIMEOUT = 0x02
    STATUS_INVALID_CMD = 0x03
    STATUS_AXI_ERROR = 0x04
    STATUS_BUSY = 0x80
    
    @staticmethod
    def get_register_name(addr: int) -> str:
        """アドレスからレジスタ名を取得"""
        register_names = {
            RegisterMap.CONTROL: "CONTROL",
            RegisterMap.STATUS: "STATUS",
            RegisterMap.CONFIG: "CONFIG",
            RegisterMap.DEBUG: "DEBUG",
            RegisterMap.TX_COUNT: "TX_COUNT",
            RegisterMap.RX_COUNT: "RX_COUNT",
            RegisterMap.FIFO_STAT: "FIFO_STAT",
            RegisterMap.VERSION: "VERSION"
        }
        return register_names.get(addr, f"0x{addr:08X}")
```

## Phase 2: GUI実装

### 2.1 メインウィンドウ設計

**実装ファイル**: `gui/main_window.py`

```python
import tkinter as tk
from tkinter import ttk, messagebox
from core.com_manager import COMManager
from core.uart_protocol import UARTProtocol
from core.register_map import RegisterMap

class MainWindow:
    def __init__(self):
        self.root = tk.Tk()
        self.root.title("AXIUART COM通信ツール v1.0")
        self.root.geometry("800x600")
        
        self.com_manager = COMManager()
        self.protocol = UARTProtocol(self.com_manager)
        
        self.setup_ui()
        
    def setup_ui(self):
        """UI構築"""
        # 接続設定フレーム
        self.create_connection_frame()
        
        # レジスタアクセスフレーム
        self.create_register_frame()
        
        # ステータス表示フレーム
        self.create_status_frame()
        
        # ログ表示フレーム
        self.create_log_frame()
        
    def create_connection_frame(self):
        """接続設定UI"""
        frame = ttk.LabelFrame(self.root, text="接続設定")
        frame.pack(fill="x", padx=5, pady=5)
        
        # COMポート選択
        ttk.Label(frame, text="COMポート:").grid(row=0, column=0, sticky="w")
        self.port_var = tk.StringVar()
        self.port_combo = ttk.Combobox(frame, textvariable=self.port_var)
        self.port_combo.grid(row=0, column=1, padx=5)
        
        # ボーレート選択
        ttk.Label(frame, text="ボーレート:").grid(row=0, column=2, sticky="w")
        self.baud_var = tk.StringVar(value="115200")
        baud_combo = ttk.Combobox(frame, textvariable=self.baud_var,
                                 values=["115200", "230400", "460800", "921600"])
        baud_combo.grid(row=0, column=3, padx=5)
        
        # 接続ボタン
        self.connect_btn = ttk.Button(frame, text="接続", command=self.connect)
        self.connect_btn.grid(row=0, column=4, padx=5)
        
        self.disconnect_btn = ttk.Button(frame, text="切断", command=self.disconnect, state="disabled")
        self.disconnect_btn.grid(row=0, column=5, padx=5)
        
        # ポート更新
        ttk.Button(frame, text="更新", command=self.update_ports).grid(row=0, column=6, padx=5)
        
        self.update_ports()
        
    def create_register_frame(self):
        """レジスタアクセスUI"""
        frame = ttk.LabelFrame(self.root, text="レジスタアクセス")
        frame.pack(fill="x", padx=5, pady=5)
        
        # アドレス入力
        ttk.Label(frame, text="アドレス:").grid(row=0, column=0, sticky="w")
        self.addr_var = tk.StringVar(value="0x1000")
        ttk.Entry(frame, textvariable=self.addr_var, width=10).grid(row=0, column=1, padx=5)
        
        # 値入力
        ttk.Label(frame, text="値:").grid(row=0, column=2, sticky="w")
        self.value_var = tk.StringVar(value="0x00000001")
        ttk.Entry(frame, textvariable=self.value_var, width=12).grid(row=0, column=3, padx=5)
        
        # 操作ボタン
        ttk.Button(frame, text="読み取り", command=self.read_register).grid(row=0, column=4, padx=5)
        ttk.Button(frame, text="書き込み", command=self.write_register).grid(row=0, column=5, padx=5)
        
    def connect(self):
        """COMポート接続"""
        port = self.port_var.get()
        baud = int(self.baud_var.get())
        
        if self.com_manager.connect(port, baud):
            self.connect_btn.config(state="disabled")
            self.disconnect_btn.config(state="normal")
            self.log_message(f"接続成功: {port} @ {baud}bps")
        else:
            messagebox.showerror("エラー", f"接続失敗: {port}")
            
    def disconnect(self):
        """COMポート切断"""
        self.com_manager.disconnect()
        self.connect_btn.config(state="normal")
        self.disconnect_btn.config(state="disabled")
        self.log_message("接続を切断しました")
        
    def read_register(self):
        """レジスタ読み取り"""
        try:
            addr = int(self.addr_var.get(), 16)
            value = self.protocol.register_read(addr)
            self.value_var.set(f"0x{value:08X}")
            reg_name = RegisterMap.get_register_name(addr)
            self.log_message(f"READ {reg_name}(0x{addr:04X}) = 0x{value:08X}")
        except Exception as e:
            messagebox.showerror("エラー", f"読み取り失敗: {e}")
            
    def write_register(self):
        """レジスタ書き込み"""
        try:
            addr = int(self.addr_var.get(), 16)
            value = int(self.value_var.get(), 16)
            if self.protocol.register_write(addr, value):
                reg_name = RegisterMap.get_register_name(addr)
                self.log_message(f"WRITE {reg_name}(0x{addr:04X}) = 0x{value:08X}")
            else:
                messagebox.showerror("エラー", "書き込み失敗")
        except Exception as e:
            messagebox.showerror("エラー", f"書き込み失敗: {e}")
```

## 実装スケジュール

### Week 1: コア機能
- [x] ✅ プロジェクト構造作成
- [ ] COMManager実装
- [ ] UARTProtocol基本機能
- [ ] CRC計算クラス
- [ ] 基本テスト作成

### Week 2: GUI開発
- [ ] メインウィンドウ作成
- [ ] レジスタアクセス機能
- [ ] ステータス表示
- [ ] ログ機能

### Week 3: 高度機能
- [ ] フロー制御対応
- [ ] テスト自動化
- [ ] パフォーマンス測定

### Week 4: 仕上げ
- [ ] CLI版作成
- [ ] ドキュメント整備
- [ ] パッケージング

次のステップとして、Phase 1のコア機能から実装を開始することを提案します。まず、COMManagerクラスの実装から始めましょうか？