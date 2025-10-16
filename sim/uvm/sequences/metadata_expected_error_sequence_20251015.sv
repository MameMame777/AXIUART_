`timescale 1ns / 1ps

// Expected-error sequence to validate metadata handling for error scenarios
class metadata_expected_error_sequence_20251015 extends uvm_sequence #(uart_frame_transaction);
    
    `uvm_object_utils(metadata_expected_error_sequence_20251015)
    
    function new(string name = "metadata_expected_error_sequence_20251015");
        super.new(name);
    endfunction

    virtual task body();
    send_metadata_request("RESERVED_READ_LOW", 1'b0, 32'h0000_0FF0, 8'h00);
    // Use an address outside the implemented register window to guarantee AXI SLVERR
    send_metadata_request("OUT_OF_RANGE_WRITE", 1'b1, 32'h0000_1800, 8'hA5);
        send_metadata_request("MISALIGNED_WRITE", 1'b1, 32'h0000_1001, 8'h5A);
        `uvm_info("ERROR_SEQ_2025", "Expected-error metadata sequence completed", UVM_LOW)
    endtask

    virtual task send_metadata_request(string tag, bit is_write, logic [31:0] addr, logic [7:0] data_byte);
        uart_frame_transaction req;

        `uvm_info("ERROR_SEQ_2025", $sformatf("Starting %s %s transaction", tag, is_write ? "write" : "read"), UVM_MEDIUM)

        `uvm_create(req)

        req.is_write       = is_write;
        req.auto_increment = 1'b0;
        req.size           = is_write ? 2'b00 : 2'b10; // Byte writes, 32-bit reads
        req.length         = 4'h0;                     // Single beat
        req.expect_error   = 1'b1;
        req.addr           = addr;
        req.error_inject   = 1'b0;
        req.force_crc_error = 1'b0;
        req.force_timeout  = 1'b0;

        if (is_write) begin
            req.data = new[1];
            req.data[0] = data_byte;
        end else begin
            req.data = new[0];
        end

        req.build_cmd();
        req.calculate_crc();

        `uvm_send(req)

        `uvm_info("ERROR_SEQ_2025",
                  $sformatf("Completed %s %s: CMD=0x%02X ADDR=0x%08X EXPECT_ERROR=1",
                            tag, is_write ? "write" : "read", req.cmd, req.addr),
                  UVM_MEDIUM)
    endtask

endclass
