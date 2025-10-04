# Hardware Debug Checklist for UART Communication Issue

## Problem Statement
- Logic analyzer trigger `rx ≠ 1` does not fire
- This indicates NO UART communication is occurring in actual hardware
- Simulation shows UART working correctly

## Immediate Debug Steps

### 1. FPGA Programming Verification
- [ ] Confirm latest 125MHz RTL bitstream is loaded to FPGA
- [ ] Check synthesis/implementation completed without errors
- [ ] Verify no timing violations in implementation

### 2. Basic Hardware Connectivity
- [ ] Verify UART RX pin connection to logic analyzer
- [ ] Check UART TX pin with oscilloscope/logic analyzer
- [ ] Confirm power supply to FPGA (3.3V/1.2V rails)
- [ ] Verify 125MHz clock is present and stable

### 3. Software/Driver Status
- [ ] Confirm UART driver/application is running
- [ ] Check if any error messages in software
- [ ] Verify software is trying to send data
- [ ] Check COM port configuration (115200 8N1)

### 4. FPGA Internal Signals
- [ ] Add debug LEDs to monitor:
   - Clock presence
   - Reset status
   - UART TX busy signal
   - AXI transaction activity
   - Bridge enable status

### 5. Pin Assignment Verification
- [ ] Double-check constraint file vs actual connections
- [ ] Verify UART pins are not conflicting with other I/O
- [ ] Check pull-up/pull-down settings

## Quick Test Methods

### Method 1: Force UART Activity
```systemverilog
// Add to testbench or create simple test module
always @(posedge clk) begin
    if (counter == 125_000_000) begin  // 1 second
        force_uart_tx <= 1'b1;
        counter <= 0;
    end else begin
        force_uart_tx <= 1'b0;
        counter <= counter + 1;
    end
end
```

### Method 2: LED Heartbeat
```systemverilog
// Add to top module
reg [26:0] led_counter;
always @(posedge clk) begin
    if (rst) 
        led_counter <= 0;
    else 
        led_counter <= led_counter + 1;
end
assign debug_led = led_counter[26]; // ~1Hz blink
```

### Method 3: GPIO Toggle Test
- Configure unused GPIO as output
- Toggle at known frequency
- Verify with logic analyzer

## Expected Results
- If UART communication starts working → Logic analyzer should trigger
- If still no trigger → Hardware/connectivity issue
- If trigger works but data is wrong → Timing/protocol issue