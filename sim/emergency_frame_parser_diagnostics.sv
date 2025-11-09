`timescale 1ns / 1ps

// Emergency diagnostics for Frame_Parser state machine
// Provides focused assertions and monitors used during simulation-only debug.
module emergency_frame_parser_diagnostics #(
    parameter int MAX_VALIDATE_STRETCH = 512,
    parameter int MAX_STATE_STABLE_CYCLES = 4096
)(
    input  logic        clk,
    input  logic        rst,
    input  logic        frame_valid_hold,
    input  logic [3:0]  state
);

    typedef enum logic [3:0] {
        IDLE        = 4'h0,
        CMD         = 4'h1,
        ADDR_BYTE0  = 4'h2,
        ADDR_BYTE1  = 4'h3,
        ADDR_BYTE2  = 4'h4,
        ADDR_BYTE3  = 4'h5,
        DATA_RX     = 4'h6,
        CRC_RX      = 4'h7,
        VALIDATE    = 4'h8,
        ERROR_STATE = 4'h9
    } parser_state_t;

    parser_state_t state_q;
    int            validate_hold_cycles;
    int            state_stable_cycles;

    // Ensure frame_valid_hold does not persist indefinitely once VALIDATE completes.
    property frame_valid_releases;
        @(posedge clk) disable iff (rst)
        frame_valid_hold |-> ##[1:MAX_VALIDATE_STRETCH] !frame_valid_hold;
    endproperty
    assert property (frame_valid_releases)
        else $error("[EMERGENCY_FP] frame_valid_hold stuck high beyond %0d cycles (time=%0t)", MAX_VALIDATE_STRETCH, $time);

    // Detect state machine lock-up away from IDLE. Guard on the live state so that
    // long idle stretches (expected while TX drains) do not trigger false positives.
    property state_eventually_advances;
        @(posedge clk) disable iff (rst)
    (state != IDLE) |-> ##[1:MAX_STATE_STABLE_CYCLES] (!$stable(state));
    endproperty
    assert property (state_eventually_advances)
        else $error("[EMERGENCY_FP] parser state %0d held for >%0d cycles (time=%0t)", state, MAX_STATE_STABLE_CYCLES, $time);

    // Coverage on healthy VALIDATE to IDLE progression.
    cover property (@(posedge clk) disable iff (rst)
        (state_q == VALIDATE && frame_valid_hold) ##1 (state == CMD || state == IDLE));

    always_ff @(posedge clk) begin
        if (rst) begin
            state_q               <= IDLE;
            validate_hold_cycles  <= 0;
            state_stable_cycles   <= 0;
        end else begin
            if (state == state_q) begin
                if (state_stable_cycles < MAX_STATE_STABLE_CYCLES) begin
                    state_stable_cycles <= state_stable_cycles + 1;
                end
            end else begin
                state_stable_cycles <= 0;
            end

            if (frame_valid_hold && state == VALIDATE) begin
                if (validate_hold_cycles < MAX_VALIDATE_STRETCH) begin
                    validate_hold_cycles <= validate_hold_cycles + 1;
                end
            end else begin
                validate_hold_cycles <= 0;
            end

            if (validate_hold_cycles == MAX_VALIDATE_STRETCH) begin
                $warning("[EMERGENCY_FP] VALIDATE hold exceeded %0d cycles (time=%0t)", MAX_VALIDATE_STRETCH, $time);
            end

            state_q <= parser_state_t'(state);
        end
    end

endmodule
