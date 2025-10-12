`timescale 1ns / 1ps

// Emergency Frame_Parser Diagnostics - Monitors frame_valid_hold and state
module emergency_frame_parser_diagnostics (
    input logic clk,
    input logic rst,
    input logic frame_valid_hold,
    input logic [3:0] state
);
    // frame_valid_hold must only be asserted in VALIDATE state
    property frame_valid_only_in_validate;
        @(posedge clk) disable iff (rst)
        frame_valid_hold |-> (state == 4'd5);
    endproperty
    assert_frame_valid_state: assert property (frame_valid_only_in_validate)
    else $error("[FP_DIAG] frame_valid_hold asserted outside VALIDATE state! state=%0d, time=%0t", state, $time);

    // frame_valid_hold must be deasserted in IDLE state
    property frame_valid_deasserted_in_idle;
        @(posedge clk) disable iff (rst)
        (state == 4'd0) |-> !frame_valid_hold;
    endproperty
    assert_frame_valid_idle: assert property (frame_valid_deasserted_in_idle)
    else $error("[FP_DIAG] frame_valid_hold asserted in IDLE state! time=%0t", $time);
endmodule
