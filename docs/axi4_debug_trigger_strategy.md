# AXI4 Debug Trigger Strategy
# 段階的トリガ戦略でwrite→read遷移問題を解析

## Phase 1: Command Analysis Triggers (基本コマンド解析)

### Primary Trigger 1: start_transaction Rising Edge
**Target**: `uart_bridge_instrm_master/start_transaction`
**Condition**: Rising Edge (0→1)
**Purpose**: UARTブリッジからAXIマスターへのトランザクション開始を捕捉
**Expected**: Writeコマンド送信時に1になる

### Secondary Trigger 1a: rw_bit Analysis  
**Target**: `uart_bridge_instrm_master/rw_bit`
**Condition**: `rw_bit == 1'b0` (Write command)
**Purpose**: コマンドがWriteとして正しく解析されているか確認
**Expected**: 0x20コマンド時にrw_bit=0であること

### Secondary Trigger 1b: Command Debug
**Target**: `uart_bridge_instrm_master/cmd`
**Condition**: `cmd == 8'h20` (Write command)
**Purpose**: UARTブリッジから正しいWriteコマンドが送信されているか
**Expected**: 0x20 (Write, 32-bit, single beat)

## Phase 2: State Machine Transition Triggers (状態遷移解析)

### Primary Trigger 2: State Transition Monitor
**Target**: `uart_bridge_instrm_master/state`
**Condition**: `state == 4'd2` (CHECK_ALIGNMENT) OR `state == 4'd5` (READ_ADDR)
**Purpose**: ステートマシンがどの状態に遷移するかを監視
**Expected**: WriteコマンドならCHECK_ALIGNMENT→WRITE_ADDRの順序

### Critical Trigger 2a: Incorrect State Transition
**Target**: `uart_bridge_instrm_master/state`
**Condition**: `state == 4'd5` (READ_ADDR state)
**Purpose**: 問題の核心：WriteコマンドなのにREAD_ADDR状態に遷移
**Alert**: この状態になったら根本問題発生

## Phase 3: AXI Signal Generation Triggers (AXI信号生成解析)

### Primary Trigger 3: awvalid Generation Failure
**Target**: `uart_bridge_instrm_master/awvalid_int`
**Condition**: `start_transaction == 1'b1 && awvalid_int == 1'b0`
**Purpose**: start_transactionが来てもawvalidが生成されない問題
**Critical**: これが0のままなら根本原因

### Secondary Trigger 3a: Write Valid Signals
**Target**: `uart_bridge_instrm_master/wvalid_int`
**Condition**: `start_transaction == 1'b1 && wvalid_int == 1'b0`
**Purpose**: wvalidも同様に生成されない可能性
**Expected**: writeコマンド時に1になるべき

## Phase 4: AXI Handshake Verification (AXIハンドシェイク検証)

### Master Side Handshake Triggers
**Target**: `uart_bridge_instrm_master/aw_handshake`
**Condition**: `aw_handshake == 1'b1`
**Purpose**: Masterからのwrite addressハンドシェイクが成功するか
**Expected**: awvalid && awready時に1

**Target**: `uart_bridge_instrm_master/w_handshake`
**Condition**: `w_handshake == 1'b1`
**Purpose**: Masterからのwrite dataハンドシェイクが成功するか
**Expected**: wvalid && wready時に1

### Slave Side Reception Triggers
**Target**: `register_block_inst/axi_awvalid_debug`
**Condition**: `axi_awvalid_debug == 1'b1`
**Purpose**: AXI MasterからSlaveにawvalidが到達するか
**Critical**: Masterで生成されてもSlaveに届かない可能性

**Target**: `register_block_inst/axi_wvalid_debug`
**Condition**: `axi_wvalid_debug == 1'b1`
**Purpose**: AXI MasterからSlaveにwvalidが到達するか
**Critical**: 同様にwvalidも届かない可能性

## Phase 5: Register Write Completion (レジスタライト完了検証)

### Final Write Trigger
**Target**: `register_block_inst/reg_test_write_trigger`
**Condition**: `reg_test_write_trigger == 1'b1`
**Purpose**: 最終的にREG_TESTレジスタへの書き込みが実行されるか
**Success**: この信号が1になれば全体が正常動作

### Address Range Verification
**Target**: `register_block_inst/axi_awaddr_debug`
**Condition**: `axi_awaddr_debug >= 32'h00001020 && axi_awaddr_debug <= 32'h0000102C`
**Purpose**: REG_TESTアドレス範囲への書き込み確認
**Expected**: 0x1020-0x102Cの範囲

### Data Verification
**Target**: `register_block_inst/axi_wdata_debug`
**Condition**: `axi_wdata_debug != 32'h00000000`
**Purpose**: 実際の書き込みデータが送信されているか
**Expected**: テストパターン(0x55AA55AA等)

## Trigger Strategy Implementation Priority

### Step 1: Primary Problem Identification
1. **start_transaction rising edge** → トランザクション開始捕捉
2. **state == READ_ADDR** → 問題の核心状態捕捉

### Step 2: Root Cause Analysis  
1. **rw_bit == 1** → コマンド解析エラーの確認
2. **awvalid_int == 0** → AXI信号生成失敗の確認

### Step 3: Signal Propagation Verification
1. **axi_awvalid_debug** → Master→Slave信号伝播確認
2. **aw_handshake** → ハンドシェイク成功確認

### Step 4: Final Verification
1. **reg_test_write_trigger** → 最終書き込み成功確認

## Conditional Trigger Logic

### Complex Trigger 1: Write Command But Read State
```
Trigger Condition: 
  (uart_bridge_instrm_master/cmd == 8'h20) &&           // Write command
  (uart_bridge_instrm_master/rw_bit == 1'b0) &&         // Parsed as write  
  (uart_bridge_instrm_master/state == 4'd5)             // But in READ_ADDR state
```
**Purpose**: 直接問題を捕捉する複合条件

### Complex Trigger 2: Transaction Start But No AXI
```
Trigger Condition:
  (uart_bridge_instrm_master/start_transaction == 1'b1) &&  // Transaction requested
  (uart_bridge_instrm_master/awvalid_int == 1'b0) &&        // But no awvalid
  (uart_bridge_instrm_master/wvalid_int == 1'b0)            // And no wvalid
```
**Purpose**: AXI信号生成失敗を直接検出

### Complex Trigger 3: Master Generated But Slave Missing
```
Trigger Condition:
  (uart_bridge_instrm_master/awvalid_int == 1'b1) &&        // Master generates
  (register_block_inst/axi_awvalid_debug == 1'b0)           // But slave doesn't see
```
**Purpose**: Master-Slave間の信号伝播問題検出