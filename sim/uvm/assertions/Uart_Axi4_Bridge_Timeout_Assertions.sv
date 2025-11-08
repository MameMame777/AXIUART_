`timescale 1ns / 1ps

module Uart_Axi4_Bridge_Timeout_Assertions #(
    parameter int unsigned FRAME_RESPONSE_TIMEOUT_CYCLES   = 1_250_000,
    parameter int unsigned AXI_TRANSACTION_TIMEOUT_CYCLES  = 2_500_000,
    parameter int unsigned BRIDGE_STALL_TIMEOUT_CYCLES     = 6_250_000
)(
    input  logic       clk,
    input  logic       rst,
    input  logic       parser_frame_valid,
    input  logic       parser_frame_error,
    input  logic       parser_frame_consumed,
    input  logic       bridge_busy,
    input  logic [2:0] main_state,
    input  logic       axi_start_transaction,
    input  logic       axi_transaction_done,
    input  logic       builder_response_complete,
    input  logic [7:0] bridge_error_code
);

    localparam int unsigned FRAME_RESPONSE_LIMIT  = FRAME_RESPONSE_TIMEOUT_CYCLES;
    localparam int unsigned AXI_TRANSACTION_LIMIT = AXI_TRANSACTION_TIMEOUT_CYCLES;
    localparam int unsigned STALL_LIMIT           = BRIDGE_STALL_TIMEOUT_CYCLES;

    initial begin
        if (FRAME_RESPONSE_LIMIT == 0) begin
            $fatal(1, "FRAME_RESPONSE_TIMEOUT_CYCLES must be non-zero");
        end
        if (AXI_TRANSACTION_LIMIT == 0) begin
            $fatal(1, "AXI_TRANSACTION_TIMEOUT_CYCLES must be non-zero");
        end
        if (STALL_LIMIT == 0) begin
            $fatal(1, "BRIDGE_STALL_TIMEOUT_CYCLES must be non-zero");
        end
    end

    function automatic string main_state_name(logic [2:0] state_value);
        case (state_value)
            3'd0: return "MAIN_IDLE";
            3'd1: return "MAIN_AXI_TRANSACTION";
            3'd2: return "MAIN_BUILD_RESPONSE";
            3'd3: return "MAIN_WAIT_RESPONSE";
            3'd4: return "MAIN_DISABLED_RESPONSE";
            default: return "UNKNOWN";
        endcase
    endfunction

    task automatic report_timeout(string tag);
        $display("[%s] Bridge timeout at %0t ns :: state=%s busy=%0b parser_valid=%0b parser_error=%0b consumed=%0b error=0x%02h",
                 tag,
                 $time,
                 main_state_name(main_state),
                 bridge_busy,
                 parser_frame_valid,
                 parser_frame_error,
                 parser_frame_consumed,
                 bridge_error_code);
    endtask

    property frame_response_completes;
        @(posedge clk) disable iff (rst)
        $rose(parser_frame_valid && !parser_frame_error)
            |-> ##[1:FRAME_RESPONSE_LIMIT] (parser_frame_consumed || parser_frame_error);
    endproperty

    assert property (frame_response_completes)
    else begin
        report_timeout("FRAME_RESPONSE_TIMEOUT");
        $fatal(1, "Bridge failed to consume frame within %0d cycles", FRAME_RESPONSE_LIMIT);
    end

    property axi_transaction_finishes;
        @(posedge clk) disable iff (rst)
        $rose(axi_start_transaction)
            |-> ##[1:AXI_TRANSACTION_LIMIT] axi_transaction_done;
    endproperty

    assert property (axi_transaction_finishes)
    else begin
        report_timeout("AXI_TRANSACTION_TIMEOUT");
        $fatal(1, "AXI transaction stuck for %0d cycles", AXI_TRANSACTION_LIMIT);
    end

    localparam int unsigned STALL_COUNTER_WIDTH = (STALL_LIMIT > 1) ? $clog2(STALL_LIMIT) + 1 : 1;

    logic [STALL_COUNTER_WIDTH-1:0] stall_counter;
    logic [2:0]                      last_main_state;

    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            stall_counter   <= '0;
            last_main_state <= main_state;
        end else begin
            last_main_state <= main_state;
            if (!bridge_busy) begin
                stall_counter <= '0;
            end else begin
                if (main_state != last_main_state || axi_transaction_done || builder_response_complete || parser_frame_consumed || parser_frame_error) begin
                    stall_counter <= '0;
                end else if (stall_counter >= STALL_LIMIT - 1) begin
                    report_timeout("BRIDGE_STALL_TIMEOUT");
                    $fatal(1, "Bridge busy without progress for %0d cycles", STALL_LIMIT);
                end else begin
                    stall_counter <= stall_counter + 1'b1;
                end
            end
        end
    end

endmodule