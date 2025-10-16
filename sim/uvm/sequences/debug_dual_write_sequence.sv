`timescale 1ns / 1ps

// Dual write debug sequence to exercise scoreboard metadata queue
class simple_dual_write_sequence_20251015 extends uvm_sequence #(uart_frame_transaction);
    
    `uvm_object_utils(simple_dual_write_sequence_20251015)
    
    function new(string name = "simple_dual_write_sequence_20251015");
        super.new(name);
    endfunction

    virtual task body();
        drive_single_write("FIRST", 32'h0000_1000, 8'h42);
        drive_single_write("SECOND", 32'h0000_1004, 8'h24);
        `uvm_info("DUAL_WRITE_SEQ_2025", "Dual write sequence completed", UVM_MEDIUM)
    endtask

    virtual task drive_single_write(string tag, logic [31:0] addr, logic [7:0] data_byte);
        uart_frame_transaction req;

        `uvm_info("DUAL_WRITE_SEQ_2025", $sformatf("Starting %s write transaction", tag), UVM_MEDIUM)

        `uvm_create(req)

        req.is_write       = 1'b1;
        req.auto_increment = 1'b0;
        req.size           = 2'b00;      // 8-bit access
        req.length         = 4'h0;       // length=0 encodes one beat
        req.expect_error   = 1'b0;
        req.addr           = addr;

        req.data = new[1];
        req.data[0] = data_byte;

        req.build_cmd();
        req.calculate_crc();

        `uvm_send(req)

        `uvm_info("DUAL_WRITE_SEQ_2025",
                  $sformatf("Sent %s write: CMD=0x%02X ADDR=0x%08X DATA=0x%02X",
                            tag, req.cmd, req.addr, req.data[0]),
                  UVM_MEDIUM)
    endtask

endclass
