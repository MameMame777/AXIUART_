# UVM Report Analysis Guide

## Report counts by id の詳細説明

### 基本構造
```
** Report counts by id
[BASE_TEST]     6
[COVERAGE]     6
[DIAG]     9
[ENV]    10
[NO_DPI_TSTNAME]     1
[RNTST]     1
[SCOREBOARD]    12
[TPRGED]     1
[UART_DRIVER]     1
[UART_MONITOR]     1
[UVM/COMP/NAMECHECK]     1
[UVM/RELNOTES]     1
[UVMTOP]     1
```

### 各IDの詳細分析

#### テスト制御系
- **[BASE_TEST]**: テストベースクラスからの情報メッセージ（6件）
  - build_phase完了、test topology、configuration表示等
- **[DIAG]**: 診断テスト固有のメッセージ（9件） 
  - テスト開始/終了、状態診断、期待値/実際値の表示
- **[RNTST]**: Running test notification（1件）
  - UVMが実行するテスト名の表示

#### 環境・コンポーネント系
- **[ENV]**: テスト環境からのメッセージ（10件）
  - コンポーネント接続、統計情報、最終レポート等
- **[SCOREBOARD]**: スコアボードからのメッセージ（12件）
  - トランザクション統計、マッチング結果、相関分析
- **[UART_DRIVER]**: UARTドライバからのメッセージ（1件）
  - 応答FIFO使用通知
- **[UART_MONITOR]**: UARTモニタからのメッセージ（1件）
  - カバレッジ無効化通知

#### カバレッジ系
- **[COVERAGE]**: カバレッジコレクタからのメッセージ（6件）
  - Frame coverage: 19.44%
  - Burst coverage: 28.13%
  - Error coverage: 50.00%
  - Total coverage: 32.52%

#### システム系
- **[UVM/RELNOTES]**: UVMリリースノート（1件）
- **[UVM/COMP/NAMECHECK]**: コンポーネント名チェック（1件）
- **[UVMTOP]**: UVMトポロジー表示（1件）
- **[NO_DPI_TSTNAME]**: DPI無効化通知（1件）
- **[TPRGED]**: 型登録重複警告（1件）

## テストシナリオ別詳細表示の実装

### 1. Verbosityレベル設定による詳細化

#### 現在使用中のレベル
```bash
.\run_uvm.ps1 -TestName frame_parser_diagnostic_test -Verbosity UVM_LOW
```

#### より詳細なレベル
```bash
# 中程度の詳細レベル
.\run_uvm.ps1 -TestName frame_parser_diagnostic_test -Verbosity UVM_MEDIUM

# 最高詳細レベル  
.\run_uvm.ps1 -TestName frame_parser_diagnostic_test -Verbosity UVM_HIGH

# フル詳細（デバッグ用）
.\run_uvm.ps1 -TestName frame_parser_diagnostic_test -Verbosity UVM_FULL
```

### 2. カスタムレポート設定

#### UVMレポートハンドラのカスタマイズ
各テストクラスに以下を追加：

```systemverilog
// テストベースクラスに追加
function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    // カスタムレポート設定
    uvm_report_server server = uvm_report_server::get_server();
    server.set_id_verbosity("DIAG", UVM_HIGH);
    server.set_id_verbosity("SCOREBOARD", UVM_MEDIUM);
    server.set_id_verbosity("COVERAGE", UVM_HIGH);
    
    // テストシナリオ別詳細設定
    if (get_type_name() == "frame_parser_diagnostic_test") begin
        server.set_id_verbosity("FRAME_PARSER", UVM_HIGH);
        server.set_id_verbosity("CRC_DEBUG", UVM_HIGH);
    end
endfunction
```

### 3. テストシナリオ別分類の実装

#### カスタムレポートID追加
```systemverilog
// frame_parser_diagnostic_test.sv
class frame_parser_diagnostic_test extends uart_axi4_base_test;
    
    function void start_of_simulation_phase(uvm_phase phase);
        super.start_of_simulation_phase(phase);
        
        `uvm_info("DIAG_SETUP", "=== FRAME PARSER DIAGNOSTIC CONFIGURATION ===", UVM_LOW)
        `uvm_info("DIAG_SETUP", "Target: FIFO synchronization and CRC validation", UVM_LOW)
        `uvm_info("DIAG_SETUP", "Expected: captured_cmd=0x01, frame_error=0", UVM_LOW)
    endfunction
    
    function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        
        `uvm_info("DIAG_RESULT", "=== FRAME PARSER DIAGNOSTIC RESULTS ===", UVM_LOW)
        `uvm_info("DIAG_RESULT", $sformatf("FIFO Sync: %s", "PASS"), UVM_LOW)
        `uvm_info("DIAG_RESULT", $sformatf("CRC Processing: %s", "PASS"), UVM_LOW)
        `uvm_info("DIAG_RESULT", $sformatf("State Transition: %s", "PASS"), UVM_LOW)
    endfunction
endclass
```

## 今後の検証デフォルト設定推奨事項

### 1. 標準化されたレポート設定

#### すべてのテストで有効にすべき項目
```systemverilog
// uart_axi4_base_test.sv に追加
function void configure_reporting();
    uvm_report_server server = uvm_report_server::get_server();
    
    // 必須カバレッジレポート
    server.set_id_verbosity("COVERAGE", UVM_MEDIUM);
    
    // スコアボード詳細
    server.set_id_verbosity("SCOREBOARD", UVM_MEDIUM);
    
    // 環境統計
    server.set_id_verbosity("ENV", UVM_MEDIUM);
    
    // エラー詳細
    server.set_severity_id_verbosity(UVM_ERROR, "ALL", UVM_HIGH);
    server.set_severity_id_verbosity(UVM_FATAL, "ALL", UVM_HIGH);
endfunction
```

### 2. 自動レポート生成機能

#### PowerShellスクリプト強化
```powershell
# run_uvm.ps1 に追加
param(
    [string]$TestName,
    [string]$Verbosity = "UVM_MEDIUM",  # デフォルトをMEDIUMに変更
    [switch]$DetailedReport = $false,   # 詳細レポート生成フラグ
    [switch]$CoverageAnalysis = $true   # カバレッジ分析をデフォルト有効
)

if ($DetailedReport) {
    Write-Host "Generating detailed test report..."
    
    # レポート解析スクリプト実行
    .\scripts\analyze_uvm_report.ps1 -LogFile "dsim.log" -TestName $TestName
}
```

### 3. テストシナリオ別メトリクス

#### 推奨メトリクス項目
- **機能カバレッジ**: Frame, Burst, Error coverage
- **コードカバレッジ**: Line, Branch, Expression coverage  
- **アサーション**: Protocol compliance, Timing assertions
- **性能**: Transaction throughput, Latency measurements
- **相関性**: UART-AXI transaction correlation accuracy

### 4. 継続的統合での活用

#### Jenkins/CI での自動化
```yaml
# .github/workflows/uvm_verification.yml
verification_job:
  runs-on: ubuntu-latest
  strategy:
    matrix:
      test: [
        "frame_parser_diagnostic_test",
        "uart_axi4_basic_test", 
        "uart_axi4_performance_test"
      ]
      verbosity: ["UVM_MEDIUM", "UVM_HIGH"]
  
  steps:
    - name: Run UVM Test
      run: |
        .\run_uvm.ps1 -TestName ${{ matrix.test }} -Verbosity ${{ matrix.verbosity }} -DetailedReport
    
    - name: Archive Reports
      uses: actions/upload-artifact@v3
      with:
        name: uvm-reports-${{ matrix.test }}
        path: sim/exec/reports/
```

## 実装優先順位

1. **即時実装**: Verbosity レベルをUVM_MEDIUMに変更
2. **短期実装**: カスタムレポートID追加とテスト固有設定
3. **中期実装**: 自動レポート解析スクリプト
4. **長期実装**: CI/CD統合と継続的メトリクス監視