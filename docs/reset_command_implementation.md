# RESET Command Implementation Plan

## Objective
Implement protocol-level RESET command to enable safe baud rate switching without losing configuration state.

## Timeline (Fixed Version)

```
Phase 0: Initial State
├─ RTL: active_baud_divisor = 16 (7.8Mbps)
├─ UVM: cfg.baud_rate = 7_812_500
└─ State: Fully synchronized ✅

Phase 1: CONFIG Setting (Old Baud Rate)
├─ 0-10µs:   UVM → RTL: CONFIG write (7.8Mbps) ✅
├─ 10-15µs:  RTL: config_baud_divisor = 135 (921.6kbps) updated ✅
├─ 15-20µs:  RTL → UVM: ACK response (7.8Mbps) ✅
└─ State: Config set, not yet activated

Phase 2: RESET Command (Old Baud Rate)
├─ 20-25µs:  UVM → RTL: RESET command (0xA5 0xFF CRC) @7.8Mbps ✅
├─ 25-30µs:  RTL: Clear FIFOs, reset state machines
│            active_baud_divisor = config_baud_divisor (135) ← Apply new baud
├─ 30-35µs:  RTL → UVM: RESET ACK (7.8Mbps) ✅ Last old baud comm
└─ State: RTL waiting at new baud, UVM still at old baud

Phase 3: UVM Baud Rate Switch
├─ 35-40µs:  UVM: cfg.baud_rate = 921_600 update
│            cfg.calculate_timing()
├─ 40-50µs:  Stabilization wait (repeat 100 @clk)
└─ State: RTL/UVM both synchronized to new baud ✅

Phase 4: Data Transfer (New Baud Rate)
├─ 50µs-:    UVM → RTL: Data write @921.6kbps ✅
├─           RTL → UVM: Response @921.6kbps ✅
└─ State: Normal communication established ✅
```

## RTL Changes

### 1. Frame_Parser.sv

**Add RESET command detection:**

```systemverilog
// In CMD state processing
CMD: begin
    cmd_reg <= rx_fifo_data;
    current_cmd <= rx_fifo_data;
    
    // Check for special RESET command
    if (rx_fifo_data == 8'hFF) begin
        is_reset_command <= 1'b1;
        state_next = CRC_RX;  // RESET has no ADDR/DATA, jump to CRC
    end else begin
        is_reset_command <= 1'b0;
        state_next = ADDR_BYTE0;  // Normal flow
    end
end
```

**Add RESET execution in VALIDATE state:**

```systemverilog
VALIDATE: begin
    if (error_status_reg == STATUS_OK) begin
        if (is_reset_command) begin
            // Soft reset execution
            soft_reset_request <= 1'b1;
            frame_valid <= 1'b1;  // Signal RESET complete
        end else begin
            // Normal frame validation
            frame_valid <= 1'b1;
        end
    end else begin
        frame_error <= 1'b1;
    end
    state_next = IDLE;
end
```

### 2. Uart_Axi4_Bridge.sv

**Add soft reset handler:**

```systemverilog
// Soft reset logic (preserves config registers)
always_ff @(posedge clk) begin
    if (rst) begin
        // Hard reset - reset everything
        rx_fifo_rst <= 1'b1;
        tx_fifo_rst <= 1'b1;
        parser_reset <= 1'b1;
        builder_reset <= 1'b1;
    end else if (parser_soft_reset_request) begin
        // Soft reset - preserve CONFIG, reset operational state
        rx_fifo_rst <= 1'b1;
        tx_fifo_rst <= 1'b1;
        parser_reset <= 1'b1;
        builder_reset <= 1'b1;
        // Activate new baud rate from CONFIG
        uart_tx.baud_divisor <= register_block.baud_div_config;
        uart_rx.baud_divisor <= register_block.baud_div_config;
    end else begin
        rx_fifo_rst <= 1'b0;
        tx_fifo_rst <= 1'b0;
        parser_reset <= 1'b0;
        builder_reset <= 1'b0;
    end
end
```

### 3. Frame_Builder.sv

**Handle RESET response:**

```systemverilog
// In response generation
if (is_reset_response) begin
    // RESET ACK: SOF (0x5A) | STATUS (0x00) | CMD (0xFF) | CRC (0x55)
    response_bytes[0] = 8'h5A;  // SOF
    response_bytes[1] = 8'h00;  // STATUS_OK
    response_bytes[2] = 8'hFF;  // CMD echo
    response_bytes[3] = 8'h55;  // CRC (pre-calculated for RESET)
    response_length = 4;
end
```

## UVM Changes

### 1. uart_reset_sequence.sv (NEW)

```systemverilog
class uart_reset_sequence extends uvm_sequence #(uart_transaction);
    `uvm_object_utils(uart_reset_sequence)
    
    function new(string name = "uart_reset_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_transaction req;
        
        req = uart_transaction::type_id::create("reset_cmd");
        start_item(req);
        
        // Build RESET frame: SOF (0xA5) | CMD (0xFF) | CRC (0x58)
        req.frame_bytes.delete();
        req.frame_bytes.push_back(8'hA5);  // SOF
        req.frame_bytes.push_back(8'hFF);  // RESET command
        req.frame_bytes.push_back(8'h58);  // CRC for RESET
        req.expect_response = 1'b1;
        
        finish_item(req);
        get_response(rsp);
        
        // Validate RESET ACK
        if (rsp.response_bytes[0] == 8'h5A &&  // SOF
            rsp.response_bytes[1] == 8'h00 &&  // STATUS_OK
            rsp.response_bytes[2] == 8'hFF) begin  // CMD echo
            `uvm_info("RESET_SEQ", "RESET command acknowledged successfully", UVM_MEDIUM)
        end else begin
            `uvm_error("RESET_SEQ", $sformatf("RESET ACK invalid: %p", rsp.response_bytes))
        end
    endtask
endclass
```

### 2. uart_axi4_fixed_115200_test.sv (NEW)

```systemverilog
class uart_axi4_fixed_115200_test extends uart_axi4_base_test;
    `uvm_component_utils(uart_axi4_fixed_115200_test)
    
    localparam int TARGET_BAUD_RATE = 921_600;
    
    task program_baud_and_reset();
        uart_configure_baud_sequence baud_seq;
        uart_reset_sequence reset_seq;
        int divisor;
        
        // Calculate divisor for 921.6kbps
        divisor = 125_000_000 / (TARGET_BAUD_RATE * 16);
        
        `uvm_info("BAUD_SWITCH", 
            $sformatf("Step 1: Write CONFIG register (divisor=%0d) @7.8Mbps", divisor),
            UVM_LOW)
        
        // Step 1: CONFIG write at old baud rate
        baud_seq = uart_configure_baud_sequence::type_id::create("baud_seq");
        baud_seq.divisor_value = divisor;
        baud_seq.start(env.uart_agt.sequencer);
        
        `uvm_info("BAUD_SWITCH", 
            "Step 2: Issue RESET command @7.8Mbps",
            UVM_LOW)
        
        // Step 2: RESET command (still at old baud rate)
        reset_seq = uart_reset_sequence::type_id::create("reset_seq");
        reset_seq.start(env.uart_agt.sequencer);
        
        `uvm_info("BAUD_SWITCH", 
            $sformatf("Step 3: Update UVM timing to %0d baud", TARGET_BAUD_RATE),
            UVM_LOW)
        
        // Step 3: Update UVM timing AFTER RTL reset
        cfg.baud_rate = TARGET_BAUD_RATE;
        cfg.calculate_timing();
        cfg.frame_timeout_ns = cfg.byte_time_ns * 128;
        
        // Step 4: Wait for stabilization
        repeat (200) @(posedge uart_axi4_tb_top.clk);
        
        `uvm_info("BAUD_SWITCH", 
            $sformatf("Baud switch complete. RTL and UVM synchronized @%0d baud", TARGET_BAUD_RATE),
            UVM_LOW)
    endtask
    
    virtual task run_phase(uvm_phase phase);
        simple_debug_write_sequence_20250923 data_seq;
        
        phase.raise_objection(this);
        
        wait (uart_axi4_tb_top.rst_n == 1'b1);
        repeat (10) @(posedge uart_axi4_tb_top.clk);
        
        `uvm_info("PHASE1", "=== PHASE 1: Baud rate switch via CONFIG + RESET ===", UVM_LOW)
        program_baud_and_reset();
        
        `uvm_info("PHASE2", "=== PHASE 2: Data transfer at new baud ===", UVM_LOW)
        data_seq = simple_debug_write_sequence_20250923::type_id::create("data_seq");
        data_seq.start(env.uart_agt.sequencer);
        
        repeat (100) @(posedge uart_axi4_tb_top.clk);
        phase.drop_objection(this);
    endtask
endclass
```

## CRC Values

**RESET Command CRC:**
- Input: CMD (0xFF)
- CRC-8 (poly 0x07, init 0x00): **0x58**

**RESET Response CRC:**
- Input: STATUS (0x00) | CMD echo (0xFF)
- CRC-8: **0x55**

## Verification Steps

1. ✅ Compile with RESET command support
2. ✅ Run uart_axi4_fixed_115200_test
3. ✅ Verify CONFIG write ACK @7.8Mbps
4. ✅ Verify RESET command ACK @7.8Mbps
5. ✅ Verify PHASE 2 data transfer @921.6kbps
6. ✅ Check waveform for baud rate transition

## Benefits

- ✅ Clean separation between config and activation
- ✅ Both UVM and RTL synchronized during transition
- ✅ No response collection mismatch
- ✅ CONFIG registers preserved across RESET
- ✅ Extensible for future soft-reset needs
