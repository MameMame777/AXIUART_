`timescale 1ns / 1ps

// Simple Read-only debug sequence to exercise scoreboard metadata handling
class simple_debug_read_sequence_20251015 extends uvm_sequence #(uart_frame_transaction);

    `uvm_object_utils(simple_debug_read_sequence_20251015)

    function new(string name = "simple_debug_read_sequence_20251015");
        super.new(name);
    endfunction

    virtual task body();
        uart_frame_transaction req;

        `uvm_info("DEBUG_READ_SEQ_2025", "Starting SINGLE read transaction debug", UVM_MEDIUM)

        `uvm_create(req)

        req.is_write       = 1'b0;
        req.auto_increment = 1'b0;
        req.size           = 2'b10;   // 32-bit access to observe full AXI read path
        req.length         = 4'h0;    // length=0 encodes one beat
        req.expect_error   = 1'b0;
        req.addr           = 32'h0000_1000;
        req.data           = new[0];  // No payload for read command

        req.build_cmd();
        req.calculate_crc();

        `uvm_send(req)

        `uvm_info("DEBUG_READ_SEQ_2025",
                  $sformatf("Requested read: CMD=0x%02X ADDR=0x%08X",
                            req.cmd, req.addr),
                  UVM_MEDIUM)

        if (!req.response_received) begin
            `uvm_warning("DEBUG_READ_SEQ_2025", "Read response not yet marked as received")
        end else begin
            `uvm_info("DEBUG_READ_SEQ_2025",
                $sformatf("Read response: STATUS=0x%02X DATA_BYTES=%0d",
                          req.response_status, req.response_data.size()),
                UVM_MEDIUM)
        end

        `uvm_info("DEBUG_READ_SEQ_2025", "SINGLE read sequence completed", UVM_MEDIUM)
    endtask

endclass
