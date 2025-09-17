// AXI4-Lite UVM Transaction
// Target Board: Zybo Z7-20
// Date: July 26, 2025
// Description: UVM transaction class for AXI4-Lite operations

`ifndef AXI4_LITE_TRANSACTION_SV
`define AXI4_LITE_TRANSACTION_SV

class axi4_lite_transaction extends uvm_sequence_item;
    
    // Transaction fields
    typedef enum {READ, WRITE} trans_type_e;
    
    rand trans_type_e           trans_type;     // Transaction type
    rand bit [ADDR_WIDTH-1:0]   addr;           // Address
    rand bit [DATA_WIDTH-1:0]   data;           // Data (write data or expected read data)
    rand bit [(DATA_WIDTH/8)-1:0] strb;        // Write strobes
    rand bit [2:0]              prot;           // Protection type
    
    // Response fields
    bit [DATA_WIDTH-1:0]        rdata;          // Actual read data
    bit [1:0]                   resp;           // Response code
    bit                         error;          // Transaction error flag
    
    // Timing control
    rand int                    addr_delay;     // Address channel delay
    rand int                    data_delay;     // Data channel delay
    rand int                    resp_delay;     // Response channel delay
    
    // Constraints
    constraint addr_c {
        addr inside {ADDR_CONTROL_REG, ADDR_STATUS_REG, ADDR_TX_DATA_REG, 
                    ADDR_RX_DATA_REG, ADDR_FIFO_STATUS, ADDR_ERROR_STATUS, 
                    ADDR_FIFO_THRESH};
        addr[1:0] == 2'b00;  // 32-bit alignment
    }
    
    constraint strb_c {
        trans_type == WRITE -> strb != 4'b0000;  // At least one byte enable for writes
        trans_type == READ  -> strb == 4'b0000;  // No strobes for reads
    }
    
    constraint timing_c {
        addr_delay inside {[0:5]};
        data_delay inside {[0:5]};
        resp_delay inside {[0:5]};
    }
    
    constraint prot_c {
        prot == 3'b000;  // Normal, secure, data access
    }
    
    // UVM registration
    `uvm_object_utils_begin(axi4_lite_transaction)
        `uvm_field_enum(trans_type_e, trans_type, UVM_ALL_ON)
        `uvm_field_int(addr, UVM_ALL_ON | UVM_HEX)
        `uvm_field_int(data, UVM_ALL_ON | UVM_HEX)
        `uvm_field_int(strb, UVM_ALL_ON | UVM_BIN)
        `uvm_field_int(prot, UVM_ALL_ON | UVM_BIN)
        `uvm_field_int(rdata, UVM_ALL_ON | UVM_HEX)
        `uvm_field_int(resp, UVM_ALL_ON | UVM_HEX)
        `uvm_field_int(error, UVM_ALL_ON)
        `uvm_field_int(addr_delay, UVM_ALL_ON)
        `uvm_field_int(data_delay, UVM_ALL_ON)
        `uvm_field_int(resp_delay, UVM_ALL_ON)
    `uvm_object_utils_end
    
    // Constructor
    function new(string name = "axi4_lite_transaction");
        super.new(name);
    endfunction
    
    // Convert to string for debugging
    virtual function string convert2string();
        string s;
        s = $sformatf("Type: %s, Addr: 0x%02h, Data: 0x%08h, Strb: %4b, Resp: %2b", 
                     trans_type.name(), addr, data, strb, resp);
        if (trans_type == READ) begin
            s = $sformatf("%s, RData: 0x%08h", s, rdata);
        end
        return s;
    endfunction
    
    // Compare function for data checking
    virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        axi4_lite_transaction tr;
        if (!$cast(tr, rhs)) return 0;
        
        return (tr.trans_type == trans_type) &&
               (tr.addr == addr) &&
               (tr.data == data) && 
               (tr.strb == strb) &&
               (tr.resp == resp) &&
               (tr.rdata == rdata);
    endfunction
    
    // Copy function
    virtual function void do_copy(uvm_object rhs);
        axi4_lite_transaction tr;
        if (!$cast(tr, rhs)) return;
        
        trans_type = tr.trans_type;
        addr = tr.addr;
        data = tr.data;
        strb = tr.strb;
        prot = tr.prot;
        rdata = tr.rdata;
        resp = tr.resp;
        error = tr.error;
        addr_delay = tr.addr_delay;
        data_delay = tr.data_delay;
        resp_delay = tr.resp_delay;
    endfunction
    
    // Utility functions for specific register access
    function void setup_control_write(bit uart_en = 1, bit tx_en = 1, bit rx_en = 1);
        trans_type = WRITE;
        addr = ADDR_CONTROL_REG;
        data = {16'h0000, 4'h1, 4'h1, 4'h0, rx_en, tx_en, uart_en};
        strb = 4'b1111;
    endfunction
    
    function void setup_status_read();
        trans_type = READ;
        addr = ADDR_STATUS_REG;
        strb = 4'b0000;
    endfunction
    
    function void setup_tx_data_write(bit [DATA_WIDTH-1:0] tx_data);
        trans_type = WRITE;
        addr = ADDR_TX_DATA_REG;
        data = tx_data;
        strb = 4'b1111;
    endfunction
    
    function void setup_rx_data_read();
        trans_type = READ;
        addr = ADDR_RX_DATA_REG;
        strb = 4'b0000;
    endfunction

endclass

`endif // AXI4_LITE_TRANSACTION_SV
