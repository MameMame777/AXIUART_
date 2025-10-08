# AXI4-Lite UART Bridge Verification Instructions - Phased Approach

_Created: 2025-10-08_  
_Target: UART ⇔ AXI4-Lite bridge register access verification_  
_Environment: DSIM v20240422.0.0 · SystemVerilog · Windows PowerShell_

---

## 1. Purpose and Critical Success Criteria

### 1.1 Primary Objective
**Verify UART-to-AXI4-Lite conversion functionality and successful REG_TEST register access**

本指示書は、`comprehensive_work_instructions.md`の原則に基づき、UART→AXI変換機能の体系的検証を目的とします。

### 1.2 Critical Success Metrics
- ✅ `UVM_ERROR = 0` across all verification phases
- ✅ REG_TEST registers (0x00001020-0x0000102C) write/read successfully  
- ✅ UART protocol correctly converts to AXI4-Lite transactions
- ✅ Data integrity maintained through complete transaction flow
- ✅ Coverage: Line ≥95%, Toggle ≥60%, Expression ≥85%, Functional ≥70%

### 1.3 Verification Philosophy - "Test in isolation, integrate with confidence"

```
Phase 1: Environment Setup       → Clean foundation
Phase 2: AXI Master Unit Test    → Component isolation
Phase 3: Register_Block Unit     → Slave verification  
Phase 4: AXI Integration Test    → Interface validation
Phase 5: UART→AXI Conversion     → System verification
Phase 6: Register Access Test    → End-to-end validation
Cleanup: Environment & Docs      → Knowledge transfer
```

---

## 2. Phase 1: Environment Setup and Validation

### 2.1 Environment Validation Script

実行ディレクトリ: `E:\Nautilus\workspace\fpgawork\AXIUART_\`

```powershell
# === Phase 1: Environment Setup Verification ===
# Execute from repository root

Write-Host "🚀 Phase 1: AXI4 Verification Environment Setup" -ForegroundColor Cyan
Write-Host "=================================================" -ForegroundColor Cyan

# Step 1.1: DSIM Environment Verification
function Test-DSIMEnvironment {
    Write-Host "`n📋 Step 1.1: DSIM Environment Verification" -ForegroundColor Yellow
    
    $required_vars = @("DSIM_HOME", "DSIM_ROOT", "DSIM_LIB_PATH")
    $env_ok = $true
    
    foreach ($var in $required_vars) {
        $value = [Environment]::GetEnvironmentVariable($var)
        if (-not $value) { 
            Write-Host "❌ $var environment variable not set" -ForegroundColor Red
            $env_ok = $false
        } elseif (-not (Test-Path $value)) { 
            Write-Host "❌ $var path does not exist: $value" -ForegroundColor Red
            $env_ok = $false
        } else {
            Write-Host "✅ $var : $value" -ForegroundColor Green
        }
    }
    
    # Verify DSIM executable
    if ($env:DSIM_HOME) {
        $dsim_exe = "$env:DSIM_HOME\bin\dsim.exe"
        if (-not (Test-Path $dsim_exe)) {
            Write-Host "❌ DSIM executable not found: $dsim_exe" -ForegroundColor Red
            $env_ok = $false
        } else {
            Write-Host "✅ DSIM executable verified" -ForegroundColor Green
        }
    }
    
    return $env_ok
}

# Step 1.2: Repository Structure Verification
function Test-RepositoryStructure {
    Write-Host "`n📋 Step 1.2: Repository Structure Verification" -ForegroundColor Yellow
    
    $critical_paths = @(
        "rtl\Axi4_Lite_Master.sv",
        "rtl\Register_Block.sv", 
        "rtl\axi4_lite_if.sv",
        "rtl\Address_Aligner.sv",
        "sim\uvm\run_uvm.ps1",
        "docs\"
    )

    $struct_ok = $true
    foreach ($path in $critical_paths) {
        if (-not (Test-Path $path)) {
            Write-Host "❌ Critical path missing: $path" -ForegroundColor Red
            $struct_ok = $false
        } else {
            Write-Host "✅ $path exists" -ForegroundColor Green
        }
    }
    
    return $struct_ok
}

# Step 1.3: Clean Working Environment
function Clear-SimulationEnvironment {
    Write-Host "`n📋 Step 1.3: Clean Working Environment" -ForegroundColor Yellow
    
    $cleanup_paths = @(
        "sim\uvm\dsim_work",
        "sim\uvm\*.log",
        "sim\uvm\*.mxd", 
        "sim\uvm\metrics.db",
        "sim\exec\dsim_work",
        "sim\exec\*.log",
        "sim\exec\*.mxd",
        "sim\exec\metrics.db"
    )
    
    foreach ($path in $cleanup_paths) {
        Remove-Item -Path $path -Recurse -Force -ErrorAction SilentlyContinue
    }
    
    Write-Host "✅ Simulation environment cleaned" -ForegroundColor Green
}

# Step 1.4: Create necessary directories
function Initialize-TestDirectories {
    Write-Host "`n📋 Step 1.4: Initialize Test Directories" -ForegroundColor Yellow
    
    $test_dirs = @(
        "sim\axi_tests",
        "sim\axi_tests\unit_tests",
        "sim\axi_tests\integration_tests", 
        "sim\axi_tests\logs",
        "sim\axi_tests\waveforms"
    )
    
    foreach ($dir in $test_dirs) {
        if (-not (Test-Path $dir)) {
            New-Item -ItemType Directory -Path $dir -Force | Out-Null
            Write-Host "✅ Created directory: $dir" -ForegroundColor Green
        } else {
            Write-Host "✅ Directory exists: $dir" -ForegroundColor Green
        }
    }
}

# Execute Phase 1
$dsim_ok = Test-DSIMEnvironment
$struct_ok = Test-RepositoryStructure

if ($dsim_ok -and $struct_ok) {
    Clear-SimulationEnvironment
    Initialize-TestDirectories
    
    Write-Host "`n🎉 Phase 1 COMPLETED: Environment Ready for AXI Verification" -ForegroundColor Green
    Write-Host "Next Step: Execute Phase 2 - AXI Master Unit Test" -ForegroundColor Cyan
} else {
    Write-Host "`n❌ Phase 1 FAILED: Fix environment issues before proceeding" -ForegroundColor Red
    exit 1
}
```

### 2.2 Phase 1 Success Criteria

- [ ] All DSIM environment variables verified
- [ ] Critical repository paths confirmed
- [ ] Clean simulation workspace
- [ ] Test directories initialized
- [ ] Phase 1 completion logged in daily diary

**Exit Criteria**: Environment validation script executes without errors.

---

## 3. Phase 2: AXI Master Unit Test

### 3.1 Objective
Verify `Axi4_Lite_Master.sv` component in complete isolation using a simple AXI slave model.

### 3.2 Test Architecture

```
┌─────────────────┐    ┌──────────────────┐    ┌─────────────────┐
│   Test Driver   │───▶│ Axi4_Lite_Master │───▶│ Simple AXI Slave│
│  (Stimulus)     │    │      (DUT)       │    │     (Model)     │
└─────────────────┘    └──────────────────┘    └─────────────────┘
```

### 3.3 Phase 2 Implementation

#### 3.3.1 Create AXI Master Unit Test

実行コマンド:
```powershell
# Navigate to test directory  
Set-Location "sim\axi_tests\unit_tests"
```

テストファイル作成: `axi_master_unit_test.sv`

```systemverilog
`timescale 1ns / 1ps

/*
 * AXI4-Lite Master Unit Test
 * 
 * Purpose: Verify AXI Master component in isolation
 * Success Criteria:
 * - Basic write transaction completes without timeout
 * - Basic read transaction completes without timeout  
 * - State machine progresses correctly through all phases
 * - AXI protocol compliance (handshakes, timing)
 */

module axi_master_unit_test;

    // Test parameters
    localparam CLOCK_PERIOD = 8ns;  // 125MHz
    localparam RESET_CYCLES = 10;
    localparam TIMEOUT_CYCLES = 5000;

    // Clock and reset
    logic clk = 0;
    logic rst = 1;
    
    // Clock generation
    always #(CLOCK_PERIOD/2) clk = ~clk;
    
    // Reset generation
    initial begin
        rst = 1;
        repeat(RESET_CYCLES) @(posedge clk);
        rst = 0;
        $display("✅ Reset released at time %0t", $time);
    end

    // AXI4-Lite interface
    axi4_lite_if axi_if (clk, rst);
    
    // AXI Master signals
    logic [7:0]  cmd;
    logic [31:0] addr;
    logic [7:0]  write_data [0:63];
    logic        start_transaction = 0;
    logic        transaction_done;
    logic [7:0]  axi_status;
    logic [7:0]  read_data [0:63];
    logic [5:0]  read_data_count;

    // DUT: AXI Master
    Axi4_Lite_Master axi_master (
        .clk(clk),
        .rst(rst),
        .cmd(cmd),
        .addr(addr),
        .write_data(write_data),
        .start_transaction(start_transaction),
        .transaction_done(transaction_done),
        .axi_status(axi_status),
        .read_data(read_data),
        .read_data_count(read_data_count),
        .axi(axi_if.master)
    );

    // Simple AXI Slave Model
    axi_slave_model slave_model (
        .clk(clk),
        .rst(rst),
        .axi(axi_if.slave)
    );

    // Test execution framework
    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;

    // Write test task
    task run_write_test(input [31:0] test_addr, input [31:0] test_data, input string test_name);
        $display("\n🧪 Test %0d: %s", ++test_count, test_name);
        $display("   Writing 0x%08X to address 0x%08X", test_data, test_addr);
        
        // Setup write command
        cmd = 8'h20;  // Write command (32-bit, single beat)
        addr = test_addr;
        write_data[0] = test_data[7:0];
        write_data[1] = test_data[15:8];
        write_data[2] = test_data[23:16];
        write_data[3] = test_data[31:24];
        
        // Start transaction
        start_transaction = 1;
        @(posedge clk);
        start_transaction = 0;
        
        // Wait for completion with timeout
        fork
            begin: wait_done
                wait (transaction_done);
                if (axi_status == 8'h00) begin
                    $display("   ✅ PASS: Write completed successfully");
                    pass_count++;
                end else begin
                    $display("   ❌ FAIL: Write failed with status 0x%02X", axi_status);
                    fail_count++;
                end
            end
            begin: timeout_check
                repeat(TIMEOUT_CYCLES) @(posedge clk);
                $display("   ❌ FAIL: Write transaction timeout");
                fail_count++;
            end
        join_any
        disable fork;
        
        repeat(10) @(posedge clk);
    endtask

    // Read test task
    task run_read_test(input [31:0] test_addr, input [31:0] expected_data, input string test_name);
        $display("\n🧪 Test %0d: %s", ++test_count, test_name);
        $display("   Reading from address 0x%08X, expecting 0x%08X", test_addr, expected_data);
        
        // Setup read command
        cmd = 8'hA0;  // Read command (32-bit, single beat)
        addr = test_addr;
        
        // Start transaction
        start_transaction = 1;
        @(posedge clk);
        start_transaction = 0;
        
        // Wait for completion with timeout
        fork
            begin: wait_done
                wait (transaction_done);
                if (axi_status == 8'h00) begin
                    if (read_data_count >= 4) begin
                        logic [31:0] read_value = {read_data[3], read_data[2], read_data[1], read_data[0]};
                        if (read_value == expected_data) begin
                            $display("   ✅ PASS: Read data matches expected value");
                            pass_count++;
                        end else begin
                            $display("   ❌ FAIL: Read data mismatch - Expected: 0x%08X, Got: 0x%08X", expected_data, read_value);
                            fail_count++;
                        end
                    end else begin
                        $display("   ❌ FAIL: Insufficient read data count: %0d", read_data_count);
                        fail_count++;
                    end
                end else begin
                    $display("   ❌ FAIL: Read failed with status 0x%02X", axi_status);
                    fail_count++;
                end
            end
            begin: timeout_check
                repeat(TIMEOUT_CYCLES) @(posedge clk);
                $display("   ❌ FAIL: Read transaction timeout");
                fail_count++;
            end
        join_any
        disable fork;
        
        repeat(10) @(posedge clk);
    endtask

    // Main test sequence
    initial begin
        $display("🚀 Starting AXI Master Unit Test");
        $display("=====================================");
        
        // Initialize write data array
        for (int i = 0; i < 64; i++) begin
            write_data[i] = 8'h00;
        end
        
        // Wait for reset release
        wait (!rst);
        repeat(20) @(posedge clk);
        
        // Test sequence
        run_write_test(32'h00001020, 32'h12345678, "Basic Write Transaction");
        run_read_test(32'h00001020, 32'h12345678, "Basic Read Transaction");
        run_write_test(32'h00001024, 32'hDEADBEEF, "Second Address Write");
        run_read_test(32'h00001024, 32'hDEADBEEF, "Second Address Read");
        run_write_test(32'h00001028, 32'hCAFEBABE, "Third Address Write");
        run_read_test(32'h00001028, 32'hCAFEBABE, "Third Address Read");
        run_write_test(32'h0000102C, 32'h00000000, "Zero Data Write");
        run_read_test(32'h0000102C, 32'h00000000, "Zero Data Read");
        run_write_test(32'h0000102C, 32'hFFFFFFFF, "All Ones Write");
        run_read_test(32'h0000102C, 32'hFFFFFFFF, "All Ones Read");
        
        // Final results
        repeat(50) @(posedge clk);
        
        $display("\n📊 AXI Master Unit Test Results");
        $display("=====================================");
        $display("Total Tests: %0d", test_count);
        $display("Passed: %0d", pass_count);
        $display("Failed: %0d", fail_count);
        
        if (fail_count == 0) begin
            $display("🎉 ALL TESTS PASSED - AXI Master Unit Test SUCCESSFUL");
        end else begin
            $display("❌ %0d TESTS FAILED - AXI Master Unit Test FAILED", fail_count);
        end
        
        $finish;
    end

    // Waveform generation
    initial begin
        $dumpfile("axi_master_unit_test.mxd");
        $dumpvars(0, axi_master_unit_test);
    end

    // Timeout watchdog
    initial begin
        #100us;
        $display("❌ GLOBAL TIMEOUT: Test suite did not complete");
        $finish;
    end

endmodule
```

#### 3.3.2 AXI Slave Model

```systemverilog
// Simple AXI Slave Model for unit testing
module axi_slave_model (
    input logic clk,
    input logic rst,
    axi4_lite_if.slave axi
);

    // Internal memory for testing
    logic [31:0] memory [logic [31:0]];
    
    // AXI slave state machine
    typedef enum logic [2:0] {
        IDLE,
        WRITE_ADDR,
        WRITE_DATA,
        WRITE_RESP,
        READ_DATA
    } axi_state_t;
    
    axi_state_t state, state_next;
    logic [31:0] write_addr_reg;
    logic [31:0] read_addr_reg;
    
    // State machine implementation
    always_ff @(posedge clk) begin
        if (rst) begin
            state <= IDLE;
            write_addr_reg <= '0;
            read_addr_reg <= '0;
        end else begin
            state <= state_next;
            
            if (axi.awvalid && axi.awready) begin
                write_addr_reg <= axi.awaddr;
            end
            
            if (axi.arvalid && axi.arready) begin
                read_addr_reg <= axi.araddr;
            end
            
            if (axi.wvalid && axi.wready) begin
                memory[write_addr_reg] <= axi.wdata;
                $display("SLAVE: Wrote 0x%08X to address 0x%08X", axi.wdata, write_addr_reg);
            end
        end
    end
    
    // Next state logic
    always_comb begin
        state_next = state;
        
        case (state)
            IDLE: begin
                if (axi.awvalid) begin
                    state_next = WRITE_ADDR;
                end else if (axi.arvalid) begin
                    state_next = READ_DATA;
                end
            end
            
            WRITE_ADDR: begin
                if (axi.awvalid && axi.awready) begin
                    state_next = WRITE_DATA;
                end
            end
            
            WRITE_DATA: begin
                if (axi.wvalid && axi.wready) begin
                    state_next = WRITE_RESP;
                end
            end
            
            WRITE_RESP: begin
                if (axi.bvalid && axi.bready) begin
                    state_next = IDLE;
                end
            end
            
            READ_DATA: begin
                if (axi.rvalid && axi.rready) begin
                    state_next = IDLE;
                end
            end
        endcase
    end
    
    // AXI signal assignments
    assign axi.awready = (state == IDLE) || (state == WRITE_ADDR);
    assign axi.wready = (state == WRITE_DATA);
    assign axi.bvalid = (state == WRITE_RESP);
    assign axi.bresp = 2'b00;  // OKAY
    
    assign axi.arready = (state == IDLE);
    assign axi.rvalid = (state == READ_DATA);
    assign axi.rdata = memory[read_addr_reg];
    assign axi.rresp = 2'b00;  // OKAY

endmodule
```

#### 3.3.3 Compilation Configuration

実行ファイル: `run_axi_master_test.ps1`

```powershell
# AXI Master Unit Test Execution Script
param(
    [string]$TestName = "axi_master_unit_test",
    [string]$Mode = "run",  # compile | run
    [int]$Seed = 1,
    [string]$Verbosity = "MEDIUM",
    [switch]$Waves = $true,
    [switch]$Coverage = $true
)

Write-Host "🚀 AXI Master Unit Test - Phase 2" -ForegroundColor Cyan
Write-Host "====================================" -ForegroundColor Cyan

# Environment check
if (-not $env:DSIM_HOME) {
    Write-Host "❌ DSIM_HOME not set" -ForegroundColor Red
    exit 1
}

# Setup paths
$test_dir = "sim\axi_tests\unit_tests"
$rtl_dir = "rtl"
$timestamp = Get-Date -Format "yyyyMMdd_HHmmss"
$log_file = "$test_dir\logs\${TestName}_${timestamp}.log"

# Compilation file list
$compile_files = @(
    "$rtl_dir\axi4_lite_if.sv",
    "$rtl_dir\Axi4_Lite_Master.sv", 
    "$test_dir\axi_master_unit_test.sv"
)

# Build compile command
$dsim_cmd = "$env:DSIM_HOME\bin\dsim.exe"
$compile_args = @(
    "-timescale", "1ns/1ps",
    "-sv",
    "-top", $TestName
)

# Add compilation files
foreach ($file in $compile_files) {
    $compile_args += $file
}

# Add waveform dumping
if ($Waves) {
    $wave_file = "$test_dir\waveforms\${TestName}_${timestamp}.mxd"
    $compile_args += "-waves", $wave_file
}

# Add coverage
if ($Coverage) {
    $compile_args += "-coverage", "all"
}

# Add seed
$compile_args += "-seed", $Seed

# Execute compilation and simulation
Write-Host "📋 Compiling and running $TestName..." -ForegroundColor Yellow
Write-Host "Command: $dsim_cmd $($compile_args -join ' ')" -ForegroundColor Gray

try {
    & $dsim_cmd @compile_args 2>&1 | Tee-Object -FilePath $log_file
    
    if ($LASTEXITCODE -eq 0) {
        Write-Host "✅ AXI Master Unit Test PASSED" -ForegroundColor Green
        Write-Host "📄 Log: $log_file" -ForegroundColor Cyan
        if ($Waves) {
            Write-Host "🌊 Waveform: $wave_file" -ForegroundColor Cyan
        }
    } else {
        Write-Host "❌ AXI Master Unit Test FAILED (Exit Code: $LASTEXITCODE)" -ForegroundColor Red
        Write-Host "📄 Check log: $log_file" -ForegroundColor Yellow
    }
} catch {
    Write-Host "❌ Execution failed: $_" -ForegroundColor Red
}
```

### 3.4 Phase 2 Execution Procedure

```powershell
# Navigate to repository root
Set-Location "E:\Nautilus\workspace\fpgawork\AXIUART_"

# Execute Phase 2
.\sim\axi_tests\unit_tests\run_axi_master_test.ps1 -TestName "axi_master_unit_test" -Seed 42
```

### 3.5 Phase 2 Success Criteria

- [ ] All basic write transactions complete without timeout
- [ ] All basic read transactions return expected data
- [ ] AXI state machine transitions correctly (IDLE→WRITE_ADDR→WRITE_DATA→WRITE_RESP→IDLE)
- [ ] No compilation errors or warnings
- [ ] Waveform file generated successfully
- [ ] Test log shows 10/10 tests passed

**Exit Criteria**: AXI Master unit test passes with 0 failures.

---

## 4. Phase 3: Register_Block Unit Test

### 4.1 Objective
Verify `Register_Block.sv` AXI slave functionality and REG_TEST register access in isolation.

### 4.2 Test Architecture

```
┌─────────────────┐    ┌──────────────────┐    ┌─────────────────┐
│ AXI Master Model│───▶│  Register_Block  │───▶│ Register Logic  │
│   (Stimulus)    │    │    (DUT)         │    │   (Internal)    │
└─────────────────┘    └──────────────────┘    └─────────────────┘
```

### 4.3 Phase 3 Implementation

テストファイル作成: `register_block_unit_test.sv`

```systemverilog
`timescale 1ns / 1ps

/*
 * Register_Block Unit Test
 * 
 * Purpose: Verify Register_Block AXI slave and REG_TEST register functionality
 * Success Criteria:
 * - REG_TEST registers (0x1020-0x102C) accessible
 * - AXI slave protocol compliance
 * - Data integrity through register operations
 * - Proper BRESP/RRESP generation
 */

module register_block_unit_test;

    // Test parameters
    localparam CLOCK_PERIOD = 8ns;  // 125MHz
    localparam RESET_CYCLES = 10;
    
    // Register addresses
    localparam ADDR_REG_TEST_0 = 32'h00001020;
    localparam ADDR_REG_TEST_1 = 32'h00001024;
    localparam ADDR_REG_TEST_2 = 32'h00001028;
    localparam ADDR_REG_TEST_3 = 32'h0000102C;

    // Clock and reset
    logic clk = 0;
    logic rst = 1;
    
    // Clock generation
    always #(CLOCK_PERIOD/2) clk = ~clk;
    
    // Reset generation
    initial begin
        rst = 1;
        repeat(RESET_CYCLES) @(posedge clk);
        rst = 0;
        $display("✅ Reset released at time %0t", $time);
    end

    // AXI4-Lite interface
    axi4_lite_if axi_if (clk, rst);

    // DUT: Register_Block
    Register_Block register_block (
        .clk(clk),
        .rst(rst),
        .axi(axi_if.slave)
    );

    // AXI Master Model for testing
    axi_master_model master_model (
        .clk(clk),
        .rst(rst),
        .axi(axi_if.master)
    );

    // Test framework
    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;

    // Write task
    task write_register(input [31:0] addr, input [31:0] data, input string test_name);
        $display("\n🧪 Test %0d: %s", ++test_count, test_name);
        $display("   Writing 0x%08X to address 0x%08X", data, addr);
        master_model.write_transaction(addr, data);
        
        if (master_model.last_bresp == 2'b00) begin
            $display("   ✅ PASS: Write completed successfully");
            pass_count++;
        end else begin
            $display("   ❌ FAIL: Write failed with BRESP=0x%01X", master_model.last_bresp);
            fail_count++;
        end
    endtask

    // Read task  
    task read_register(input [31:0] addr, input [31:0] expected_data, input string test_name);
        logic [31:0] read_data;
        
        $display("\n🧪 Test %0d: %s", ++test_count, test_name);
        $display("   Reading from address 0x%08X, expecting 0x%08X", addr, expected_data);
        
        master_model.read_transaction(addr, read_data);
        
        if (master_model.last_rresp == 2'b00) begin
            if (read_data == expected_data) begin
                $display("   ✅ PASS: Read data matches expected value");
                pass_count++;
            end else begin
                $display("   ❌ FAIL: Data mismatch - Expected: 0x%08X, Got: 0x%08X", expected_data, read_data);
                fail_count++;
            end
        end else begin
            $display("   ❌ FAIL: Read failed with RRESP=0x%01X", master_model.last_rresp);
            fail_count++;
        end
    endtask

    // Main test sequence
    initial begin
        $display("🚀 Starting Register_Block Unit Test");
        $display("=======================================");
        
        // Wait for reset release
        wait (!rst);
        repeat(20) @(posedge clk);
        
        // Test sequence - REG_TEST register access
        write_register(ADDR_REG_TEST_0, 32'h12345678, "REG_TEST_0 Write");
        read_register(ADDR_REG_TEST_0, 32'h12345678, "REG_TEST_0 Read");
        
        write_register(ADDR_REG_TEST_1, 32'hDEADBEEF, "REG_TEST_1 Write");
        read_register(ADDR_REG_TEST_1, 32'hDEADBEEF, "REG_TEST_1 Read");
        
        write_register(ADDR_REG_TEST_2, 32'hCAFEBABE, "REG_TEST_2 Write");
        read_register(ADDR_REG_TEST_2, 32'hCAFEBABE, "REG_TEST_2 Read");
        
        write_register(ADDR_REG_TEST_3, 32'hFEEDFACE, "REG_TEST_3 Write");
        read_register(ADDR_REG_TEST_3, 32'hFEEDFACE, "REG_TEST_3 Read");
        
        // Test data patterns
        write_register(ADDR_REG_TEST_0, 32'h00000000, "Zero Pattern Write");
        read_register(ADDR_REG_TEST_0, 32'h00000000, "Zero Pattern Read");
        
        write_register(ADDR_REG_TEST_0, 32'hFFFFFFFF, "All Ones Write");
        read_register(ADDR_REG_TEST_0, 32'hFFFFFFFF, "All Ones Read");
        
        write_register(ADDR_REG_TEST_0, 32'hAAAA5555, "Alternating Pattern Write");
        read_register(ADDR_REG_TEST_0, 32'hAAAA5555, "Alternating Pattern Read");
        
        // Final results
        repeat(50) @(posedge clk);
        
        $display("\n📊 Register_Block Unit Test Results");
        $display("======================================");
        $display("Total Tests: %0d", test_count);
        $display("Passed: %0d", pass_count);
        $display("Failed: %0d", fail_count);
        
        if (fail_count == 0) begin
            $display("🎉 ALL TESTS PASSED - Register_Block Unit Test SUCCESSFUL");
        end else begin
            $display("❌ %0d TESTS FAILED - Register_Block Unit Test FAILED", fail_count);
        end
        
        $finish;
    end

    // Waveform generation
    initial begin
        $dumpfile("register_block_unit_test.mxd");
        $dumpvars(0, register_block_unit_test);
    end

    // Timeout watchdog
    initial begin
        #50us;
        $display("❌ GLOBAL TIMEOUT: Test suite did not complete");
        $finish;
    end

endmodule
```

### 4.4 AXI Master Model

```systemverilog
// AXI Master Model for testing Register_Block
module axi_master_model (
    input logic clk,
    input logic rst,
    axi4_lite_if.master axi
);

    // Transaction status
    logic [1:0] last_bresp;
    logic [1:0] last_rresp;
    
    // Write transaction task
    task write_transaction(input [31:0] addr, input [31:0] data);
        // Address phase
        axi.awvalid <= 1;
        axi.awaddr <= addr;
        axi.awprot <= 3'b000;
        
        // Data phase
        axi.wvalid <= 1;
        axi.wdata <= data;
        axi.wstrb <= 4'hF;
        
        axi.bready <= 1;
        
        // Wait for address handshake
        do @(posedge clk); while (!axi.awready);
        axi.awvalid <= 0;
        
        // Wait for data handshake
        do @(posedge clk); while (!axi.wready);
        axi.wvalid <= 0;
        
        // Wait for response
        do @(posedge clk); while (!axi.bvalid);
        last_bresp = axi.bresp;
        @(posedge clk);
        axi.bready <= 0;
        
        $display("MASTER: Write 0x%08X to 0x%08X, BRESP=0x%01X", data, addr, last_bresp);
    endtask
    
    // Read transaction task
    task read_transaction(input [31:0] addr, output [31:0] data);
        // Address phase
        axi.arvalid <= 1;
        axi.araddr <= addr;
        axi.arprot <= 3'b000;
        axi.rready <= 1;
        
        // Wait for address handshake
        do @(posedge clk); while (!axi.arready);
        axi.arvalid <= 0;
        
        // Wait for data response
        do @(posedge clk); while (!axi.rvalid);
        data = axi.rdata;
        last_rresp = axi.rresp;
        @(posedge clk);
        axi.rready <= 0;
        
        $display("MASTER: Read 0x%08X from 0x%08X, RRESP=0x%01X", data, addr, last_rresp);
    endtask
    
    // Initialize signals
    initial begin
        axi.awvalid <= 0;
        axi.awaddr <= 0;
        axi.awprot <= 0;
        axi.wvalid <= 0;
        axi.wdata <= 0;
        axi.wstrb <= 0;
        axi.bready <= 0;
        axi.arvalid <= 0;
        axi.araddr <= 0;
        axi.arprot <= 0;
        axi.rready <= 0;
        last_bresp <= 0;
        last_rresp <= 0;
    end

endmodule
```

### 4.5 Phase 3 Success Criteria

- [ ] All REG_TEST register writes complete successfully (BRESP=0x0)
- [ ] All REG_TEST register reads return written data (RRESP=0x0)
- [ ] Data patterns (0x00000000, 0xFFFFFFFF, 0xAAAA5555) preserved correctly
- [ ] No compilation errors or warnings
- [ ] Waveform shows proper AXI handshake timing

**Exit Criteria**: Register_Block unit test passes with 0 failures.

---

## 5. Phase 4: AXI Integration Test

### 5.1 Objective
Verify end-to-end AXI communication between `Axi4_Lite_Master` and `Register_Block`.

### 5.2 Test Architecture

```
┌─────────────────┐    ┌──────────────────┐    ┌─────────────────┐
│  Test Driver    │───▶│ Axi4_Lite_Master │───▶│ Register_Block  │
│   (Stimulus)    │    │    (Master)      │    │    (Slave)      │
└─────────────────┘    └──────────────────┘    └─────────────────┘
```

### 5.3 Phase 4 Implementation

テストファイル作成: `axi_integration_test.sv`

```systemverilog
`timescale 1ns / 1ps

/*
 * AXI Integration Test
 * 
 * Purpose: Verify end-to-end AXI Master ↔ Register_Block communication
 * Success Criteria:
 * - Master commands translated to proper AXI transactions
 * - Register_Block responds correctly to AXI transactions
 * - Data integrity maintained through complete transaction chain
 * - Proper error handling and status reporting
 */

module axi_integration_test;

    // Test parameters
    localparam CLOCK_PERIOD = 8ns;  // 125MHz
    localparam RESET_CYCLES = 10;
    localparam TIMEOUT_CYCLES = 10000;
    
    // Register addresses  
    localparam ADDR_REG_TEST_0 = 32'h00001020;
    localparam ADDR_REG_TEST_1 = 32'h00001024;
    localparam ADDR_REG_TEST_2 = 32'h00001028;
    localparam ADDR_REG_TEST_3 = 32'h0000102C;

    // Clock and reset
    logic clk = 0;
    logic rst = 1;
    
    // Clock generation
    always #(CLOCK_PERIOD/2) clk = ~clk;
    
    // Reset generation
    initial begin
        rst = 1;
        repeat(RESET_CYCLES) @(posedge clk);
        rst = 0;
        $display("✅ Reset released at time %0t", $time);
    end

    // AXI4-Lite interface
    axi4_lite_if axi_if (clk, rst);
    
    // AXI Master signals
    logic [7:0]  cmd;
    logic [31:0] addr;
    logic [7:0]  write_data [0:63];
    logic        start_transaction = 0;
    logic        transaction_done;
    logic [7:0]  axi_status;
    logic [7:0]  read_data [0:63];
    logic [5:0]  read_data_count;

    // DUT: AXI Master
    Axi4_Lite_Master axi_master (
        .clk(clk),
        .rst(rst),
        .cmd(cmd),
        .addr(addr),
        .write_data(write_data),
        .start_transaction(start_transaction),
        .transaction_done(transaction_done),
        .axi_status(axi_status),
        .read_data(read_data),
        .read_data_count(read_data_count),
        .axi(axi_if.master)
    );

    // DUT: Register_Block
    Register_Block register_block (
        .clk(clk),
        .rst(rst),
        .axi(axi_if.slave)
    );

    // Test framework
    int test_count = 0;
    int pass_count = 0;
    int fail_count = 0;

    // Write test task
    task run_write_transaction(input [31:0] test_addr, input [31:0] test_data, input string test_name);
        $display("\n🧪 Test %0d: %s", ++test_count, test_name);
        $display("   Writing 0x%08X to address 0x%08X", test_data, test_addr);
        
        // Setup write command
        cmd = 8'h20;  // Write command (32-bit, single beat)
        addr = test_addr;
        write_data[0] = test_data[7:0];
        write_data[1] = test_data[15:8];
        write_data[2] = test_data[23:16];
        write_data[3] = test_data[31:24];
        
        // Start transaction
        start_transaction = 1;
        @(posedge clk);
        start_transaction = 0;
        
        // Wait for completion with timeout
        fork
            begin: wait_done
                wait (transaction_done);
                if (axi_status == 8'h00) begin
                    $display("   ✅ PASS: Write completed successfully");
                    pass_count++;
                end else begin
                    $display("   ❌ FAIL: Write failed with status 0x%02X", axi_status);
                    fail_count++;
                end
            end
            begin: timeout_check
                repeat(TIMEOUT_CYCLES) @(posedge clk);
                $display("   ❌ FAIL: Write transaction timeout");
                fail_count++;
            end
        join_any
        disable fork;
        
        repeat(10) @(posedge clk);
    endtask

    // Read test task
    task run_read_transaction(input [31:0] test_addr, input [31:0] expected_data, input string test_name);
        $display("\n🧪 Test %0d: %s", ++test_count, test_name);
        $display("   Reading from address 0x%08X, expecting 0x%08X", test_addr, expected_data);
        
        // Setup read command
        cmd = 8'hA0;  // Read command (32-bit, single beat)
        addr = test_addr;
        
        // Start transaction
        start_transaction = 1;
        @(posedge clk);
        start_transaction = 0;
        
        // Wait for completion with timeout
        fork
            begin: wait_done
                wait (transaction_done);
                if (axi_status == 8'h00) begin
                    if (read_data_count >= 4) begin
                        logic [31:0] read_value = {read_data[3], read_data[2], read_data[1], read_data[0]};
                        if (read_value == expected_data) begin
                            $display("   ✅ PASS: Read data matches expected value");
                            pass_count++;
                        end else begin
                            $display("   ❌ FAIL: Read data mismatch - Expected: 0x%08X, Got: 0x%08X", expected_data, read_value);
                            fail_count++;
                        end
                    end else begin
                        $display("   ❌ FAIL: Insufficient read data count: %0d", read_data_count);
                        fail_count++;
                    end
                end else begin
                    $display("   ❌ FAIL: Read failed with status 0x%02X", axi_status);
                    fail_count++;
                end
            end
            begin: timeout_check
                repeat(TIMEOUT_CYCLES) @(posedge clk);
                $display("   ❌ FAIL: Read transaction timeout");
                fail_count++;
            end
        join_any
        disable fork;
        
        repeat(10) @(posedge clk);
    endtask

    // Main test sequence
    initial begin
        $display("🚀 Starting AXI Integration Test");
        $display("===================================");
        
        // Initialize write data array
        for (int i = 0; i < 64; i++) begin
            write_data[i] = 8'h00;
        end
        
        // Wait for reset release
        wait (!rst);
        repeat(20) @(posedge clk);
        
        // Test sequence - REG_TEST register access through AXI chain
        run_write_transaction(ADDR_REG_TEST_0, 32'h12345678, "REG_TEST_0 Write via AXI");
        run_read_transaction(ADDR_REG_TEST_0, 32'h12345678, "REG_TEST_0 Read via AXI");
        
        run_write_transaction(ADDR_REG_TEST_1, 32'hDEADBEEF, "REG_TEST_1 Write via AXI");
        run_read_transaction(ADDR_REG_TEST_1, 32'hDEADBEEF, "REG_TEST_1 Read via AXI");
        
        run_write_transaction(ADDR_REG_TEST_2, 32'hCAFEBABE, "REG_TEST_2 Write via AXI");
        run_read_transaction(ADDR_REG_TEST_2, 32'hCAFEBABE, "REG_TEST_2 Read via AXI");
        
        run_write_transaction(ADDR_REG_TEST_3, 32'hFEEDFACE, "REG_TEST_3 Write via AXI");
        run_read_transaction(ADDR_REG_TEST_3, 32'hFEEDFACE, "REG_TEST_3 Read via AXI");
        
        // Stress testing - rapid sequential operations
        $display("\n🔥 Stress Testing: Rapid Sequential Operations");
        run_write_transaction(ADDR_REG_TEST_0, 32'hAAAA5555, "Rapid Write 1");
        run_write_transaction(ADDR_REG_TEST_1, 32'h5555AAAA, "Rapid Write 2");
        run_read_transaction(ADDR_REG_TEST_0, 32'hAAAA5555, "Rapid Read 1");
        run_read_transaction(ADDR_REG_TEST_1, 32'h5555AAAA, "Rapid Read 2");
        
        // Data pattern testing
        $display("\n🧩 Data Pattern Testing");
        run_write_transaction(ADDR_REG_TEST_0, 32'h00000000, "Zero Pattern Write");
        run_read_transaction(ADDR_REG_TEST_0, 32'h00000000, "Zero Pattern Read");
        
        run_write_transaction(ADDR_REG_TEST_0, 32'hFFFFFFFF, "All Ones Write");
        run_read_transaction(ADDR_REG_TEST_0, 32'hFFFFFFFF, "All Ones Read");
        
        run_write_transaction(ADDR_REG_TEST_0, 32'h01010101, "Walking Ones Write");
        run_read_transaction(ADDR_REG_TEST_0, 32'h01010101, "Walking Ones Read");
        
        // Final results
        repeat(100) @(posedge clk);
        
        $display("\n📊 AXI Integration Test Results");
        $display("==================================");
        $display("Total Tests: %0d", test_count);
        $display("Passed: %0d", pass_count);
        $display("Failed: %0d", fail_count);
        
        if (fail_count == 0) begin
            $display("🎉 ALL TESTS PASSED - AXI Integration Test SUCCESSFUL");
            $display("🎯 AXI Master ↔ Register_Block communication verified!");
        end else begin
            $display("❌ %0d TESTS FAILED - AXI Integration Test FAILED", fail_count);
        end
        
        $finish;
    end

    // Waveform generation
    initial begin
        $dumpfile("axi_integration_test.mxd");
        $dumpvars(0, axi_integration_test);
    end

    // Timeout watchdog
    initial begin
        #500us;
        $display("❌ GLOBAL TIMEOUT: Test suite did not complete");
        $finish;
    end

endmodule
```

### 5.4 Phase 4 Success Criteria

- [ ] All AXI Master→Register_Block write transactions succeed
- [ ] All register reads return data written by AXI Master
- [ ] Rapid sequential operations complete without errors
- [ ] Data pattern integrity maintained (0x00000000, 0xFFFFFFFF, patterns)
- [ ] AXI protocol compliance observed in waveforms
- [ ] Integration test passes with 0 failures

**Exit Criteria**: AXI integration test passes with 0 failures, confirming end-to-end AXI communication.

---

## 6. Phase 5: UART→AXI Conversion Test (Future Scope)

### 6.1 Objective
Verify complete UART input to AXI output conversion chain.

### 6.2 Scope Definition
This phase will be detailed after successful completion of Phases 1-4. Focus areas include:
- UART frame parsing and command extraction
- Command→AXI transaction mapping
- Error handling and status generation
- End-to-end data integrity

**Note**: Phase 5 implementation depends on successful completion of fundamental AXI verification.

---

## 7. Environment Cleanup and Documentation

### 7.1 Cleanup Script

実行ファイル: `cleanup_verification_environment.ps1`

```powershell
# AXI4 Verification Environment Cleanup Script
param(
    [switch]$KeepLogs = $false,
    [switch]$KeepWaveforms = $false,
    [switch]$ArchiveResults = $true
)

Write-Host "🧹 AXI4 Verification Environment Cleanup" -ForegroundColor Cyan
Write-Host "==========================================" -ForegroundColor Cyan

$timestamp = Get-Date -Format "yyyyMMdd_HHmmss"

# Archive important results if requested
if ($ArchiveResults) {
    Write-Host "📦 Archiving verification results..." -ForegroundColor Yellow
    
    $archive_dir = "archive\verification_results_$timestamp"
    New-Item -ItemType Directory -Path $archive_dir -Force | Out-Null
    
    # Archive logs
    if (Test-Path "sim\axi_tests\unit_tests\logs\*") {
        Copy-Item "sim\axi_tests\unit_tests\logs\*" "$archive_dir\" -Recurse
        Write-Host "✅ Logs archived to $archive_dir" -ForegroundColor Green
    }
    
    # Archive waveforms
    if (Test-Path "sim\axi_tests\unit_tests\waveforms\*") {
        Copy-Item "sim\axi_tests\unit_tests\waveforms\*" "$archive_dir\" -Recurse
        Write-Host "✅ Waveforms archived to $archive_dir" -ForegroundColor Green
    }
    
    # Archive coverage reports if they exist
    if (Test-Path "sim\axi_tests\*\coverage_report\*") {
        Copy-Item "sim\axi_tests\*\coverage_report\*" "$archive_dir\" -Recurse -Force
        Write-Host "✅ Coverage reports archived to $archive_dir" -ForegroundColor Green
    }
}

# Clean simulation artifacts
Write-Host "🗑️ Cleaning simulation artifacts..." -ForegroundColor Yellow

$cleanup_patterns = @(
    "sim\axi_tests\*\dsim_work",
    "sim\axi_tests\*\*.db",
    "sim\axi_tests\*\work*"
)

foreach ($pattern in $cleanup_patterns) {
    Remove-Item -Path $pattern -Recurse -Force -ErrorAction SilentlyContinue
}

# Conditionally clean logs and waveforms
if (-not $KeepLogs) {
    Remove-Item -Path "sim\axi_tests\*\logs\*" -Force -ErrorAction SilentlyContinue
    Write-Host "✅ Test logs cleaned" -ForegroundColor Green
} else {
    Write-Host "ℹ️  Test logs preserved" -ForegroundColor Cyan
}

if (-not $KeepWaveforms) {
    Remove-Item -Path "sim\axi_tests\*\waveforms\*" -Force -ErrorAction SilentlyContinue
    Write-Host "✅ Waveforms cleaned" -ForegroundColor Green
} else {
    Write-Host "ℹ️  Waveforms preserved" -ForegroundColor Cyan
}

Write-Host "`n🎉 Environment cleanup completed" -ForegroundColor Green

if ($ArchiveResults) {
    Write-Host "📚 Results archived in: $archive_dir" -ForegroundColor Cyan
}
```

### 7.2 Daily Progress Documentation Template

日次レポートテンプレート: `docs/diary_YYYYMMDD.md`

```markdown
# AXI4 Verification Daily Progress - 2025-MM-DD

## Phase Status Overview
- [x] Phase 1: Environment Setup - COMPLETED
- [x] Phase 2: AXI Master Unit Test - COMPLETED  
- [x] Phase 3: Register_Block Unit Test - COMPLETED
- [x] Phase 4: AXI Integration Test - COMPLETED
- [ ] Phase 5: UART→AXI Conversion Test - PENDING
- [ ] Environment Cleanup - PENDING

## Today's Accomplishments

### Phase X: [Phase Name]
- **Status**: [COMPLETED/IN_PROGRESS/BLOCKED]
- **Tests Executed**: [Test names and results]
- **Key Findings**: [Important discoveries or issues]
- **Coverage Metrics**: [If applicable]

### Issues Encountered
1. **Issue**: [Description]
   - **Root Cause**: [Analysis]
   - **Resolution**: [How it was fixed]
   - **Prevention**: [How to avoid in future]

### Artifacts Generated
- **Logs**: `sim/axi_tests/*/logs/[specific files]`
- **Waveforms**: `sim/axi_tests/*/waveforms/[specific files]`
- **Coverage**: `[coverage report paths if applicable]`

## Next Steps
- [ ] [Specific next action]
- [ ] [Another specific action]

## Notes for Next Engineer
- [Important context or gotchas]
- [Environment considerations]
- [Continuation instructions]

## Verification Quality Metrics
- **UVM Errors**: [Count]
- **Compilation Warnings**: [Count]
- **Test Pass Rate**: [X/Y tests passed]
- **Waveform Quality**: [Captured/Missing]
```

---

## 8. Success Criteria Summary and Next Steps

### 8.1 Overall Success Metrics

| Phase | Success Criteria | Exit Evidence |
|-------|------------------|---------------|
| 1 | Environment validated | All environment checks pass |
| 2 | AXI Master unit tests pass | 10/10 tests pass, 0 timeouts |
| 3 | Register_Block unit tests pass | 14/14 tests pass, proper BRESP/RRESP |
| 4 | Integration tests pass | 16/16 tests pass, end-to-end verification |
| 5 | UART→AXI conversion verified | [To be defined after Phase 4] |

### 8.2 Quality Gates

Before proceeding to FPGA validation:
- [ ] **UVM_ERROR = 0** across all phases
- [ ] **Compilation warnings = 0** 
- [ ] **All waveforms captured and validated**
- [ ] **Documentation complete and archived**
- [ ] **Environment cleanup executed**

### 8.3 Handoff to FPGA Debug Phase

Only after successful completion of all RTL verification phases:

1. **Document verified RTL behavior**
2. **Archive all verification artifacts**  
3. **Create FPGA debug continuation plan**
4. **Transfer knowledge to hardware debug phase**

---

## 9. Execution Commands Summary

### Quick Start Sequence

```powershell
# Navigate to repository root
Set-Location "E:\Nautilus\workspace\fpgawork\AXIUART_"

# Phase 1: Environment Setup
# [Execute environment validation script from section 2.1]

# Phase 2: AXI Master Unit Test
.\sim\axi_tests\unit_tests\run_axi_master_test.ps1

# Phase 3: Register_Block Unit Test  
.\sim\axi_tests\unit_tests\run_register_block_test.ps1

# Phase 4: AXI Integration Test
.\sim\axi_tests\integration_tests\run_axi_integration_test.ps1

# Cleanup
.\cleanup_verification_environment.ps1 -ArchiveResults
```

### 継続的実行のためのワークフロー

1. **開始前**: 環境検証スクリプト実行
2. **各フェーズ**: テスト実行→結果確認→日次記録更新
3. **問題発生時**: 波形解析→根本原因特定→修正→再テスト
4. **フェーズ完了時**: 成功基準確認→次フェーズ移行
5. **全体完了時**: クリーンアップ→アーカイブ→引き継ぎ資料作成

---

**この指示書により、UART→AXI変換機能の体系的かつ段階的な検証が可能になります。各フェーズの成功基準を満たしながら進めることで、最終的なFPGAデバッグフェーズでの成功確率を最大化します。**