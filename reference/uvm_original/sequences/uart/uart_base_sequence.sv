// UART UVM Base Sequence
// Target Board: Zybo Z7-20
// Date: July 26, 2025
// Description: Base sequence for UART transactions

`ifndef UART_BASE_SEQUENCE_SV
`define UART_BASE_SEQUENCE_SV

class uart_base_sequence extends uvm_sequence #(uart_transaction);
    
    // UVM registration
    `uvm_object_utils(uart_base_sequence)
    
    // Constructor
    function new(string name = "uart_base_sequence");
        super.new(name);
    endfunction
    
    // Pre-body task for setup
    virtual task pre_body();
        if (starting_phase != null) begin
            starting_phase.raise_objection(this);
        end
    endtask
    
    // Post-body task for cleanup
    virtual task post_body();
        if (starting_phase != null) begin
            starting_phase.drop_objection(this);
        end
    endtask
    
    // Utility task for single byte transmission
    virtual task send_byte(bit [7:0] data, bit use_flow_ctrl = 0);
        uart_transaction tr;
        
        tr = uart_transaction::type_id::create("tx_tr");
        
        if (!tr.randomize() with {
            trans_type == uart_transaction::TX;
            data == local::data;
            use_flow_control == local::use_flow_ctrl;
            parity_error == 0;
            frame_error == 0;
            overrun_error == 0;
        }) begin
            `uvm_error("UART_SEQ", "Failed to randomize TX transaction")
        end
        
        start_item(tr);
        finish_item(tr);
        
        `uvm_info("UART_SEQ", $sformatf("Sent byte: 0x%02h", data), UVM_MEDIUM)
    endtask
    
    // Utility task for error injection
    virtual task send_byte_with_error(bit [7:0] data, bit parity_err = 0, bit frame_err = 0, bit overrun_err = 0);
        uart_transaction tr;
        
        tr = uart_transaction::type_id::create("tx_err_tr");
        
        if (!tr.randomize() with {
            trans_type == uart_transaction::TX;
            data == local::data;
            parity_error == local::parity_err;
            frame_error == local::frame_err;
            overrun_error == local::overrun_err;
        }) begin
            `uvm_error("UART_SEQ", "Failed to randomize error TX transaction")
        end
        
        start_item(tr);
        finish_item(tr);
        
        `uvm_info("UART_SEQ", $sformatf("Sent byte with errors: 0x%02h (p=%b,f=%b,o=%b)", 
                 data, parity_err, frame_err, overrun_err), UVM_MEDIUM)
    endtask
    
    // Utility task for string transmission
    virtual task send_string(string str);
        for (int i = 0; i < str.len(); i++) begin
            send_byte(str[i]);
        end
        `uvm_info("UART_SEQ", $sformatf("Sent string: \"%s\"", str), UVM_LOW)
    endtask
    
    // Utility task for receive setup
    virtual task setup_receive(bit use_flow_ctrl = 0);
        uart_transaction tr;
        
        tr = uart_transaction::type_id::create("rx_setup_tr");
        
        if (!tr.randomize() with {
            trans_type == uart_transaction::RX;
            use_flow_control == local::use_flow_ctrl;
        }) begin
            `uvm_error("UART_SEQ", "Failed to randomize RX setup transaction")
        end
        
        start_item(tr);
        finish_item(tr);
        
        `uvm_info("UART_SEQ", "RX setup completed", UVM_MEDIUM)
    endtask

endclass

`endif // UART_BASE_SEQUENCE_SV
