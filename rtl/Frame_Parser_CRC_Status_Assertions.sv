`timescale 1ns / 1ps

//==============================================================================
// Frame_Parser_CRC_Status_Assertions.sv
// Dedicated CRC status monitoring assertions for Frame_Parser
//
// Motivation:
//   During CRC mismatch scenarios we must guarantee that the DUT surfaces
//   STATUS_CRC_ERR promptly and never asserts frame_valid spuriously.
//   This module augments the existing Frame_Parser_Assertions without
//   modifying the DUT.
//==============================================================================

module Frame_Parser_CRC_Status_Assertions (
    input  logic        clk,
    input  logic        rst,
    input  logic [3:0]  state,
    input  logic        frame_valid,
    input  logic        frame_consumed,
    input  logic [7:0]  received_crc,
    input  logic [7:0]  expected_crc,
    input  logic [7:0]  error_status_reg
);

    // Local copies of protocol constants (must match Frame_Parser.sv)
    localparam [3:0] VALIDATE       = 4'h8;
    localparam [3:0] ERROR          = 4'h9;
    localparam [7:0] STATUS_OK      = 8'h00;
    localparam [7:0] STATUS_CRC_ERR = 8'h01;

    // CRC mismatch must push STATUS_CRC_ERR within two cycles.
    property crc_mismatch_sets_status_err;
        @(posedge clk) disable iff (rst)
        (state == VALIDATE && (received_crc != expected_crc))
        |-> ##[0:2] (error_status_reg == STATUS_CRC_ERR);
    endproperty
    assert_crc_mismatch_sets_status_err: assert property (crc_mismatch_sets_status_err)
        else $fatal("ASSERTION_FAIL: STATUS_CRC_ERR not asserted promptly after CRC mismatch at %t", $time);

    // Once a CRC mismatch is detected, frame_valid must remain low until the frame is consumed or the FSM leaves VALIDATE.
    property crc_mismatch_blocks_frame_valid;
        @(posedge clk) disable iff (rst)
        (state == VALIDATE && (received_crc != expected_crc))
        |-> (!frame_valid) until_with (frame_consumed || (state != VALIDATE));
    endproperty
    assert_crc_mismatch_blocks_frame_valid: assert property (crc_mismatch_blocks_frame_valid)
        else $fatal("ASSERTION_FAIL: frame_valid asserted while CRC mismatch pending at %t", $time);

    // Guard against STATUS_OK reappearing while the mismatch condition persists.
    property crc_mismatch_does_not_return_ok;
        @(posedge clk) disable iff (rst)
        (state == VALIDATE && (received_crc != expected_crc))
        |-> (error_status_reg != STATUS_OK) until_with (frame_consumed || (state == ERROR));
    endproperty
    assert_crc_mismatch_does_not_return_ok: assert property (crc_mismatch_does_not_return_ok)
        else $fatal("ASSERTION_FAIL: STATUS_OK observed while CRC mismatch unhandled at %t", $time);

endmodule