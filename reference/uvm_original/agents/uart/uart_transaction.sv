// UART UVM Transaction
// Target Board: Zybo Z7-20
// Date: July 26, 2025
// Description: UVM transaction item for UART interface

`ifndef UART_TRANSACTION_SV
`define UART_TRANSACTION_SV

class uart_transaction extends uvm_sequence_item;
    
    // Transaction types
    typedef enum {
        TX,         // Transmit operation
        RX          // Receive operation
    } trans_type_e;
    
    // Transaction fields
    rand trans_type_e trans_type;
    rand bit [UART_DATA_WIDTH-1:0] data;
    rand bit parity_error;
    rand bit frame_error;
    rand bit overrun_error;
    
    // Timing constraints
    rand int bit_period;
    rand int frame_gap;      // Gap between frames
    
    // Flow control
    rand bit use_flow_control;
    rand bit rts_assert;
    rand bit cts_ready;
    
    // Constraints
    constraint valid_data_c {
        data inside {[8'h00:8'hFF]};
    }
    
    constraint timing_c {
        bit_period >= 1;
        bit_period <= 10;
        frame_gap >= 0;
        frame_gap <= 100;
    }
    
    constraint error_rates_c {
        parity_error dist {0 := 95, 1 := 5};      // 5% parity errors
        frame_error dist {0 := 98, 1 := 2};       // 2% frame errors
        overrun_error dist {0 := 99, 1 := 1};     // 1% overrun errors
    }
    
    constraint flow_control_c {
        use_flow_control dist {0 := 70, 1 := 30}; // 30% with flow control
        rts_assert dist {0 := 20, 1 := 80};       // Usually assert RTS
        cts_ready dist {0 := 10, 1 := 90};        // Usually CTS ready
    }
    
    // UVM registration
    `uvm_object_utils_begin(uart_transaction)
        `uvm_field_enum(trans_type_e, trans_type, UVM_DEFAULT)
        `uvm_field_int(data, UVM_DEFAULT | UVM_HEX)
        `uvm_field_int(parity_error, UVM_DEFAULT)
        `uvm_field_int(frame_error, UVM_DEFAULT)
        `uvm_field_int(overrun_error, UVM_DEFAULT)
        `uvm_field_int(bit_period, UVM_DEFAULT)
        `uvm_field_int(frame_gap, UVM_DEFAULT)
        `uvm_field_int(use_flow_control, UVM_DEFAULT)
        `uvm_field_int(rts_assert, UVM_DEFAULT)
        `uvm_field_int(cts_ready, UVM_DEFAULT)
    `uvm_object_utils_end
    
    // Constructor
    function new(string name = "uart_transaction");
        super.new(name);
        bit_period = 1;
        frame_gap = 0;
        use_flow_control = 0;
        rts_assert = 1;
        cts_ready = 1;
        parity_error = 0;
        frame_error = 0;
        overrun_error = 0;
    endfunction
    
    // Convert to string
    virtual function string convert2string();
        string s;
        s = $sformatf("UART Transaction: %s", trans_type.name());
        s = {s, $sformatf(", data=0x%02h", data)};
        s = {s, $sformatf(", bit_period=%0d", bit_period)};
        s = {s, $sformatf(", frame_gap=%0d", frame_gap)};
        if (use_flow_control) begin
            s = {s, $sformatf(", flow_ctrl(rts=%b,cts=%b)", rts_assert, cts_ready)};
        end
        if (parity_error || frame_error || overrun_error) begin
            s = {s, $sformatf(", errors(p=%b,f=%b,o=%b)", parity_error, frame_error, overrun_error)};
        end
        return s;
    endfunction
    
    // Compare function
    virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        uart_transaction tr;
        if (!$cast(tr, rhs)) return 0;
        
        return (trans_type == tr.trans_type) &&
               (data == tr.data) &&
               (parity_error == tr.parity_error) &&
               (frame_error == tr.frame_error) &&
               (overrun_error == tr.overrun_error);
    endfunction
    
    // Utility functions for common patterns
    function void set_normal_tx(bit [UART_DATA_WIDTH-1:0] tx_data);
        trans_type = TX;
        data = tx_data;
        parity_error = 0;
        frame_error = 0;
        overrun_error = 0;
        bit_period = 1;
        frame_gap = 2;
    endfunction
    
    function void set_error_tx(bit [UART_DATA_WIDTH-1:0] tx_data, bit p_err = 0, bit f_err = 0, bit o_err = 0);
        trans_type = TX;
        data = tx_data;
        parity_error = p_err;
        frame_error = f_err;
        overrun_error = o_err;
        bit_period = 1;
        frame_gap = 2;
    endfunction
    
    function void set_flow_control_tx(bit [UART_DATA_WIDTH-1:0] tx_data, bit rts = 1, bit cts = 1);
        trans_type = TX;
        data = tx_data;
        use_flow_control = 1;
        rts_assert = rts;
        cts_ready = cts;
        parity_error = 0;
        frame_error = 0;
        overrun_error = 0;
        bit_period = 1;
        frame_gap = 2;
    endfunction

endclass

`endif // UART_TRANSACTION_SV
