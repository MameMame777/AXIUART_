# UART Clocking Block Migration - Quick Reference DIFF

## 📌 Before/After Comparison

### 1. Interface (`uart_if.sv` → `uart_if_clocking.sv`)

#### BEFORE (BROKEN):
```systemverilog
interface uart_if (input logic clk, input logic rst);
    logic uart_tx;
    logic uart_rx;
    
    // NO clocking blocks - drivers use direct @(posedge clk)
    
    modport driver (
        output uart_rx,
        input  uart_tx
    );
endinterface
```

#### AFTER (DSIM-SAFE):
```systemverilog
interface uart_if_clocking (input logic clk, input logic rst);
    logic uart_tx;
    logic uart_rx;
    
    // MANDATORY clocking blocks
    clocking cb_drv @(posedge clk);
        default input #1step output #0;
        output uart_rx;
        input  uart_tx;
    endclocking
    
    clocking cb_mon @(posedge clk);
        default input #1step;
        input uart_tx;
        input uart_rx;
    endclocking
    
    // Modport enforces clocking block usage
    modport driver (
        clocking cb_drv,
        input clk, input rst
    );
    
    modport monitor (
        clocking cb_mon,
        input clk, input rst
    );
endinterface
```

**KEY CHANGES:**
- ✅ Added `cb_drv` and `cb_mon` clocking blocks
- ✅ `#1step` timing for NBA-safe sampling
- ✅ Modports provide only clocking block access
- ✅ Direct `clk` access restricted (diagnostics only)

---

### 2. Driver (`uart_driver.sv` → `uart_driver_clocking.sv`)

#### BEFORE (永久HANGS):
```systemverilog
class uart_driver extends uvm_driver #(uart_frame_transaction);
    virtual uart_if vif;  // ← Direct interface access
    
    task drive_uart_byte(logic [7:0] data);
        // START BIT
        vif.uart_rx = 1'b0;
        repeat(bit_time_cycles) @(posedge vif.clk);  // ← DSIM BUG: 永久blocks
        
        // DATA BITS
        for (int i = 0; i < 8; i++) begin
            vif.uart_rx = data[i];
            repeat(bit_time_cycles) @(posedge vif.clk);  // ← 永久hang risk
        end
        
        // STOP BIT
        vif.uart_rx = 1'b1;
        repeat(bit_time_cycles) @(posedge vif.clk);  // ← OBSERVED永久HANG
    endtask
endclass
```

#### AFTER (WORKS IN DSIM):
```systemverilog
class uart_driver_clocking extends uvm_driver #(uart_frame_transaction);
    virtual uart_if_clocking.driver vif;  // ← Modport enforcement
    
    task drive_uart_byte_cb(logic [7:0] data);
        // START BIT
        vif.cb_drv.uart_rx <= 1'b0;              // ← NBA assignment
        repeat(bit_time_cycles) @(vif.cb_drv);   // ← Clocking block (SAFE)
        
        // DATA BITS
        for (int i = 0; i < 8; i++) begin
            vif.cb_drv.uart_rx <= data[i];
            repeat(bit_time_cycles) @(vif.cb_drv);  // ← NO MORE @(posedge)
        end
        
        // STOP BIT
        vif.cb_drv.uart_rx <= 1'b1;
        repeat(bit_time_cycles) @(vif.cb_drv);   // ← NEVER HANGS
    endtask
endclass
```

**KEY CHANGES:**
- ❌ Removed: `@(posedge vif.clk)` (30+ occurrences)
- ✅ Replaced with: `@(vif.cb_drv)`
- ❌ Removed: `vif.uart_rx = value` (blocking assignment)
- ✅ Replaced with: `vif.cb_drv.uart_rx <= value` (NBA)
- ✅ Changed interface type: `virtual uart_if_clocking.driver vif`

---

### 3. Response Collection (Driver - Critical Section)

#### BEFORE (BROKEN):
```systemverilog
task collect_response(uart_frame_transaction tr);
    // Wait for DUT response start bit
    fork
        begin
            @(negedge vif.uart_tx);  // ← DSIM BUG: edge event lost
            response_detected = 1;
        end
        begin
            #(timeout_ns);
            response_detected = 0;
        end
    join_any
    disable fork;
    
    if (response_detected) begin
        collect_uart_byte(temp_byte);  // Uses @(posedge vif.clk)
    end
endtask
```

#### AFTER (WORKS):
```systemverilog
task collect_response_cb(uart_frame_transaction tr);
    // Wait for DUT response start bit via polling
    fork
        begin
            // Level-based edge detection (no @(negedge) dependency)
            while (vif.cb_drv.uart_tx == 1'b1) begin
                @(vif.cb_drv);  // ← Poll via clocking block
                if (($time - start_time) > timeout_ns) break;
            end
            response_detected = (vif.cb_drv.uart_tx == 1'b0);
        end
    join
    
    if (response_detected) begin
        collect_uart_byte_cb(temp_byte);  // Uses @(vif.cb_drv)
    end
endtask
```

**KEY CHANGES:**
- ❌ Removed: `@(negedge vif.uart_tx)` (edge-sensitive, broken)
- ✅ Replaced with: `while (signal == 1) @(cb)` (level-polling, reliable)
- ✅ Inline timeout check (fork/join_any unreliable in DSIM)
- ✅ All sampling via `vif.cb_drv.uart_tx`

---

### 4. Monitor (`uart_monitor.sv` → `uart_monitor_clocking.sv`)

#### BEFORE (UNSTABLE):
```systemverilog
class uart_monitor extends uvm_monitor;
    virtual uart_if vif;
    
    task collect_uart_byte(output logic [7:0] data);
        // Wait for start bit
        @(negedge vif.uart_tx);  // ← DSIM edge event bug
        
        // Sample bits
        repeat(cfg.bit_time_cycles / 2) @(posedge vif.clk);  // ← 永久hang risk
        for (int i = 0; i < 8; i++) begin
            repeat(cfg.bit_time_cycles) @(posedge vif.clk);
            data[i] = vif.uart_tx;  // ← Race condition
        end
    endtask
endclass
```

#### AFTER (STABLE):
```systemverilog
class uart_monitor_clocking extends uvm_monitor;
    virtual uart_if_clocking.monitor vif;
    
    task collect_uart_byte_cb(output logic [7:0] data, input uart_direction_e dir);
        // No @(negedge) - caller already detected edge via polling
        
        // Sample bits via clocking block
        repeat(cfg.bit_time_cycles / 2) @(vif.cb_mon);  // ← Clocking block
        for (int i = 0; i < 8; i++) begin
            repeat(cfg.bit_time_cycles) @(vif.cb_mon);  // ← SAFE
            data[i] = vif.cb_mon.uart_tx;  // ← #1step sampled (race-free)
        end
    endtask
endclass
```

**KEY CHANGES:**
- ❌ Removed: `@(posedge vif.clk)` (20+ occurrences)
- ✅ Replaced with: `@(vif.cb_mon)`
- ❌ Removed: `@(negedge vif.uart_tx)` (edge detection)
- ✅ Replaced with: Level polling in caller (see below)
- ✅ All sampling: `vif.cb_mon.signal` (#1step timing)

#### Edge Detection Pattern (Monitor):
```systemverilog
// BEFORE:
@(negedge vif.uart_tx);  // ← Broken in DSIM

// AFTER:
while (vif.cb_mon.uart_tx == 1'b1) @(vif.cb_mon);  // Wait for idle
while (vif.cb_mon.uart_tx == 1'b0) @(vif.cb_mon);  // Falling edge detected
```

---

### 5. Watchdog Pattern

#### BEFORE (NON-FUNCTIONAL):
```systemverilog
fork
    begin
        drive_uart_byte(data);
    end
    begin
        #(watchdog_ns);
        `uvm_fatal("TIMEOUT", "Byte transmission timeout")  // ← NEVER FIRES
    end
join_any
disable fork;
```

#### AFTER (FUNCTIONAL):
```systemverilog
task drive_uart_byte_cb(logic [7:0] data);
    time start_time = $time;
    time watchdog_ns = cfg.byte_time_ns * 4;
    
    // Inline watchdog checks (no fork/join_any)
    for (int i = 0; i < 8; i++) begin
        vif.cb_drv.uart_rx <= data[i];
        repeat(bit_time_cycles) @(vif.cb_drv);
        
        // Check timeout inline
        if (($time - start_time) > watchdog_ns) begin
            `uvm_fatal("TIMEOUT", "Byte transmission timeout")  // ← NOW WORKS
        end
    end
endtask
```

**KEY CHANGES:**
- ❌ Removed: fork/join_any watchdog pattern (broken in DSIM)
- ✅ Replaced with: Inline `$time` checks after each `@(cb)`
- ✅ Reliable timeout detection (no dependency on #delay delivery)

---

## 📊 Pattern Summary Table

| Pattern | BEFORE (Broken) | AFTER (Fixed) | Occurrences |
|---------|----------------|---------------|-------------|
| Clock sync | `@(posedge vif.clk)` | `@(vif.cb_drv/cb_mon)` | 50+ |
| Falling edge | `@(negedge vif.signal)` | `while(sig==1) @(cb)` | 10+ |
| Rising edge | `@(posedge vif.signal)` | `while(sig==0) @(cb)` | 5+ |
| Signal output | `vif.signal = val` | `vif.cb.signal <= val` | 30+ |
| Signal input | `data = vif.signal` | `data = vif.cb.signal` | 20+ |
| Watchdog | `fork #delay join_any` | Inline `$time` check | 8+ |

---

## 🚀 Quick Migration Steps

1. **Copy interface:**
   ```bash
   cp uart_if.sv uart_if_clocking.sv
   ```

2. **Add clocking blocks** to `uart_if_clocking.sv`

3. **Copy driver:**
   ```bash
   cp uart_driver.sv uart_driver_clocking.sv
   ```

4. **Find/replace in driver:**
   ```
   Find: @\(posedge vif\.clk\)
   Replace: @(vif.cb_drv)
   
   Find: vif\.uart_rx\s*=
   Replace: vif.cb_drv.uart_rx <=
   
   Find: @\(negedge vif\.uart_tx\)
   Replace: while(vif.cb_drv.uart_tx==1) @(vif.cb_drv);
   ```

5. **Repeat for monitor**

6. **Run self-test:**
   ```bash
   dsim uart_clocking_block_selftest.sv
   ```

---

## ✅ Verification Checklist

After migration, verify:

- [ ] No `@(posedge vif.clk)` in driver (use `grep -n`)
- [ ] No `@(negedge` anywhere in driver/monitor
- [ ] All signal assignments use `<=` (NBA)
- [ ] All signal reads use `vif.cb.signal`
- [ ] Watchdogs use inline `$time` checks
- [ ] Self-test passes all 5 tests
- [ ] Basic UVM test completes without永久hang
- [ ] Bit timing matches expected baud rate (<5% error)

---

**END OF QUICK REFERENCE**
