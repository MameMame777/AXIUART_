`timescale 1ns / 1ps

import uvm_pkg::*;
`include "uvm_macros.svh"
import uart_axi4_test_pkg::*;

// Sequence that performs multi-register, multi-pattern 32-bit write/read validation via the UART bridge
class test_reg_rw_sequence extends uvm_sequence #(uart_frame_transaction);

    `uvm_object_utils(test_reg_rw_sequence)

    localparam int unsigned NUM_REGISTERS = 2;
    localparam int unsigned NUM_PATTERNS  = 3;

    // Absolute addresses for REG_TEST_0 through REG_TEST_7 within the AXI register block
    localparam bit [31:0] REG_TEST_ADDRS   [NUM_REGISTERS] = '{
        32'h0000_1020, // REG_TEST_0
        32'h0000_1024  // REG_TEST_1
    };

    localparam string    REG_LABELS       [NUM_REGISTERS] = '{
        "REG_TEST_0",
        "REG_TEST_1"
    };

    // Stress patterns chosen by user for comprehensive RW coverage (replicated to 32 bits)
    localparam bit [31:0] PATTERN_VALUES  [NUM_PATTERNS]  = '{
        32'h5555_5555,
        32'hAAAA_AAAA,
        32'hFFFF_FFFF
    };

    localparam string    PATTERN_LABELS   [NUM_PATTERNS]  = '{
        "0x5555_5555",
        "0xAAAA_AAAA",
        "0xFFFF_FFFF"
    };

    function new(string name = "test_reg_rw_sequence");
        super.new(name);
    endfunction

    virtual task body();
        foreach (REG_TEST_ADDRS[reg_index]) begin
            foreach (PATTERN_VALUES[pattern_index]) begin
                perform_register_pattern_check(
                    REG_TEST_ADDRS[reg_index],
                    PATTERN_VALUES[pattern_index],
                    REG_LABELS[reg_index],
                    PATTERN_LABELS[pattern_index]
                );
            end
        end

        `uvm_info("TEST_REG_RW",
            "Completed REG_TEST_0-REG_TEST_7 read/write coverage for all requested patterns",
            UVM_LOW)
    endtask

    protected task perform_register_pattern_check(bit [31:0] address,
                                                  bit [31:0] pattern,
                                                  string reg_label,
                                                  string pattern_label);
        uart_frame_transaction write_req;
        uart_frame_transaction read_req;
        bit [31:0] observed_value;

        write_req = uart_frame_transaction::type_id::create(
            $sformatf("%s_write_%s", reg_label, pattern_label));
        if (write_req == null) begin
            `uvm_fatal("TEST_REG_SEQ", "Failed to allocate write transaction")
        end

        start_item(write_req);
        configure_write_request(write_req, address, pattern);
        finish_item(write_req);

        if (!write_req.response_received || write_req.response_status != STATUS_OK) begin
            `uvm_fatal("TEST_REG_WRITE",
                $sformatf("%s write response invalid for pattern %s: received=%0b status=0x%02X",
                    reg_label, pattern_label, write_req.response_received, write_req.response_status))
        end

        read_req = uart_frame_transaction::type_id::create(
            $sformatf("%s_read_%s", reg_label, pattern_label));
        if (read_req == null) begin
            `uvm_fatal("TEST_REG_SEQ", "Failed to allocate read transaction")
        end

        start_item(read_req);
        configure_read_request(read_req, address);
        finish_item(read_req);

        if (!read_req.response_received || read_req.response_status != STATUS_OK) begin
            `uvm_fatal("TEST_REG_READ",
                $sformatf("%s read response invalid for pattern %s: received=%0b status=0x%02X",
                    reg_label, pattern_label, read_req.response_received, read_req.response_status))
        end

        if (read_req.response_data.size() != 4) begin
            `uvm_fatal("TEST_REG_READ",
                $sformatf("%s expected 4 data bytes, observed %0d", reg_label, read_req.response_data.size()))
        end

        observed_value = assemble_32bit(read_req.response_data);
        if (observed_value !== pattern) begin
            `uvm_fatal("TEST_REG_MISMATCH",
                $sformatf("%s readback mismatch for pattern %s: expected=0x%08X observed=0x%08X",
                    reg_label, pattern_label, pattern, observed_value))
        end

        `uvm_info("TEST_REG_RW",
            $sformatf("%s verified with pattern %s", reg_label, pattern_label),
            UVM_MEDIUM)
    endtask

    protected task configure_write_request(ref uart_frame_transaction tr,
                                           bit [31:0] address,
                                           bit [31:0] pattern);
        tr.is_write       = 1'b1;
        tr.auto_increment = 1'b0;
        tr.size           = 2'b10; // 32-bit access
        tr.length         = 4'h0;  // single beat
        tr.expect_error   = 1'b0;
        tr.addr           = address;
        tr.data           = new[4];
        for (int i = 0; i < 4; i++) begin
            tr.data[i] = pattern[8*i +: 8];
        end
        tr.build_cmd();
        tr.calculate_crc();
    endtask

    protected task configure_read_request(ref uart_frame_transaction tr,
                                          bit [31:0] address);
        tr.is_write       = 1'b0;
        tr.auto_increment = 1'b0;
        tr.size           = 2'b10;
        tr.length         = 4'h0;
        tr.expect_error   = 1'b0;
        tr.addr           = address;
        tr.data           = new[0];
        tr.build_cmd();
        tr.calculate_crc();
    endtask

    protected function bit [31:0] assemble_32bit(const ref logic [7:0] bytes[]);
        bit [31:0] value;
        value = '0;
        for (int i = 0; i < bytes.size(); i++) begin
            value[8*i +: 8] = bytes[i];
        end
        return value;
    endfunction

endclass
