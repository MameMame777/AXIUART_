// UART Interface Definition
// Target Board: Zybo Z7-20
// Date: July 26, 2025
// Description: SystemVerilog interface for UART with MXD waveform dump support

`ifndef UART_IF_SV
`define UART_IF_SV

interface uart_if(input logic clk, input logic rst);
    
    // UART signals
    logic tx;        // Transmit data
    logic rx;        // Receive data
    logic rts_n;     // Request to Send (active low)
    logic cts_n;     // Clear to Send (active low)
    
    // Additional debug signals
    logic tx_busy;   // Transmitter busy
    logic rx_ready;  // Receiver ready
    logic frame_error;
    logic parity_error;
    logic overrun_error;
    
    // Master clocking block (for driving)
    clocking master_cb @(posedge clk);
        default input #1 output #1;
        output tx, rts_n;
        input  rx, cts_n;
        input  tx_busy, rx_ready;
        input  frame_error, parity_error, overrun_error;
    endclocking
    
    // Slave clocking block (for receiving)
    clocking slave_cb @(posedge clk);
        default input #1 output #1;
        input  tx, rts_n;
        output rx, cts_n;
        output tx_busy, rx_ready;
        output frame_error, parity_error, overrun_error;
    endclocking
    
    // Monitor clocking block
    clocking monitor_cb @(posedge clk);
        default input #1;
        input tx, rx, rts_n, cts_n;
        input tx_busy, rx_ready;
        input frame_error, parity_error, overrun_error;
    endclocking
    
    // Modports
    modport master  (clocking master_cb, input clk, rst);
    modport slave   (clocking slave_cb, input clk, rst);
    modport monitor (clocking monitor_cb, input clk, rst);
    
    // UART Protocol Assertions
    property tx_idle_high;
        @(posedge clk) disable iff (rst)
        !tx_busy |-> tx == 1'b1;
    endproperty
    
    property rx_idle_high;
        @(posedge clk) disable iff (rst)
        !rx_ready |-> rx == 1'b1;
    endproperty
    
    property rts_cts_flow_control;
        @(posedge clk) disable iff (rst)
        (rts_n == 1'b0) && (cts_n == 1'b0) |-> ##[1:10] tx_busy;
    endproperty
    
    // Bind assertions
    assert property (tx_idle_high) else $warning("UART TX not idle high");
    assert property (rx_idle_high) else $warning("UART RX not idle high");
    assert property (rts_cts_flow_control) else $warning("Flow control timing violation");
    
    // MXD waveform dump support
    `ifdef DSIM
        initial begin
            $dumpfile("uart_interface_waves.mxd");
            $dumpvars(0, uart_if);
        end
    `endif
    
    // Debug tasks
    task wait_for_tx_complete();
        @(posedge clk);
        wait(!tx_busy);
        @(posedge clk);
    endtask
    
    task wait_for_rx_data();
        @(posedge clk);
        wait(rx_ready);
        @(posedge clk);
    endtask
    
    // Protocol checker functions
    function bit is_start_bit(bit signal_value);
        return (signal_value == 1'b0);
    endfunction
    
    function bit is_stop_bit(bit signal_value);
        return (signal_value == 1'b1);
    endfunction
    
    function bit is_flow_control_active();
        return (rts == 1'b0) && (cts == 1'b0);
    endfunction

endinterface

`endif // UART_IF_SV
