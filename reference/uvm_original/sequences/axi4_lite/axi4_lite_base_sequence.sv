// AXI4-Lite UVM Base Sequence
// Target Board: Zybo Z7-20
// Date: July 26, 2025
// Description: Base sequence for AXI4-Lite transactions

`ifndef AXI4_LITE_BASE_SEQUENCE_SV
`define AXI4_LITE_BASE_SEQUENCE_SV

class axi4_lite_base_sequence extends uvm_sequence #(axi4_lite_transaction);
    
    // UVM registration
    `uvm_object_utils(axi4_lite_base_sequence)
    
    // Constructor
    function new(string name = "axi4_lite_base_sequence");
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
    
    // Utility task for single register write
    virtual task write_register(bit [31:0] addr, bit [31:0] data, bit [3:0] strb = 4'b1111);
        axi4_lite_transaction tr;
        
        tr = axi4_lite_transaction::type_id::create("write_tr");
        
        if (!tr.randomize() with {
            trans_type == axi4_lite_transaction::WRITE;
            addr == local::addr;
            data == local::data;
            strb == local::strb;
        }) begin
            `uvm_error("SEQ", "Failed to randomize write transaction")
        end
        
        start_item(tr);
        finish_item(tr);
        
        `uvm_info("AXI4_SEQ", $sformatf("Write: addr=0x%08h, data=0x%08h, strb=%b", 
                 addr, data, strb), UVM_MEDIUM)
    endtask
    
    // Utility task for single register read
    virtual task read_register(bit [31:0] addr, output bit [31:0] rdata, output bit [1:0] resp);
        axi4_lite_transaction tr;
        
        tr = axi4_lite_transaction::type_id::create("read_tr");
        
        if (!tr.randomize() with {
            trans_type == axi4_lite_transaction::READ;
            addr == local::addr;
        }) begin
            `uvm_error("SEQ", "Failed to randomize read transaction")
        end
        
        start_item(tr);
        finish_item(tr);
        
        rdata = tr.rdata;
        resp = tr.resp;
        
        `uvm_info("AXI4_SEQ", $sformatf("Read: addr=0x%08h, rdata=0x%08h, resp=%b", 
                 addr, rdata, resp), UVM_MEDIUM)
    endtask
    
    // Utility task for read-modify-write
    virtual task read_modify_write(bit [31:0] addr, bit [31:0] mask, bit [31:0] new_data);
        bit [31:0] current_data, modified_data;
        bit [1:0] resp;
        
        // Read current value
        read_register(addr, current_data, resp);
        
        if (resp != AXI_RESP_OKAY) begin
            `uvm_error("SEQ", $sformatf("Read failed for RMW at addr=0x%08h", addr))
            return;
        end
        
        // Modify data
        modified_data = (current_data & ~mask) | (new_data & mask);
        
        // Write back
        write_register(addr, modified_data);
        
        `uvm_info("AXI4_SEQ", $sformatf("RMW: addr=0x%08h, old=0x%08h, new=0x%08h", 
                 addr, current_data, modified_data), UVM_MEDIUM)
    endtask

endclass

`endif // AXI4_LITE_BASE_SEQUENCE_SV
