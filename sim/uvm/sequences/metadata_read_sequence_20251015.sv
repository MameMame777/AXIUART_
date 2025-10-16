`timescale 1ns / 1ps

// Read-focused sequence to exercise metadata queue handling for read transactions
class metadata_read_sequence_20251015 extends uvm_sequence #(uart_frame_transaction);
    
    `uvm_object_utils(metadata_read_sequence_20251015)
    
    function new(string name = "metadata_read_sequence_20251015");
        super.new(name);
    endfunction

    virtual task body();
        drive_single_read("PRIMARY_REG", 32'h0000_1000);
        drive_single_read("STATUS_REG", 32'h0000_1004);
        drive_single_read("FIFO_STATUS", 32'h0000_1008);
        `uvm_info("READ_SEQ_2025", "Read-focused metadata sequence completed", UVM_LOW)
    endtask

    virtual task drive_single_read(string tag, logic [31:0] addr);
        uart_frame_transaction req;

        `uvm_info("READ_SEQ_2025", $sformatf("Starting %s read transaction", tag), UVM_MEDIUM)

        `uvm_create(req)

        req.is_write       = 1'b0;
        req.auto_increment = 1'b0;
        req.size           = 2'b10;      // 32-bit read
        req.length         = 4'h0;       // Single beat
        req.expect_error   = 1'b0;
        req.addr           = addr;
        req.data           = new[0];

        req.build_cmd();
        req.calculate_crc();

        `uvm_send(req)

        `uvm_info("READ_SEQ_2025",
                  $sformatf("Completed %s read: CMD=0x%02X ADDR=0x%08X",
                            tag, req.cmd, req.addr),
                  UVM_MEDIUM)
    endtask

endclass
