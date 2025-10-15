`timescale 1ns / 1ps

// Bridge status interface aligned with RTL implementation for monitoring
interface bridge_status_if (
    input logic clk,
    input logic rst_n
);

    // Frame parser state monitoring
    logic frame_parser_state_changed;
    logic [7:0] current_frame_parser_state;

    // FIFO status monitoring (64-deep FIFOs require 7-bit counters)
    logic fifo_status_changed;
    logic [6:0] rx_fifo_count;
    logic [6:0] rx_fifo_depth;
    logic [6:0] tx_fifo_count;
    logic [6:0] tx_fifo_depth;

    // Bridge status and error reporting
    logic [7:0] bridge_state;
    logic [31:0] error_status;
    // Helper method to decode the frame parser state into a readable string
    function string get_frame_parser_state_name();
        case (current_frame_parser_state)
            8'h00: return "IDLE";
            8'h01: return "WAIT_START";
            8'h02: return "RECV_COMMAND";
            8'h03: return "RECV_ADDRESS";
            8'h04: return "RECV_LENGTH";
            8'h05: return "RECV_DATA";
            8'h06: return "RECV_CRC";
            8'h07: return "VALIDATE";
            8'h08: return "EXECUTE";
            8'h09: return "SEND_RESPONSE";
            8'h0A: return "ERROR";
            default: return "UNKNOWN";
        endcase
    endfunction

    // Default values to avoid X-propagation in simulation
    initial begin
        frame_parser_state_changed = 1'b0;
        current_frame_parser_state = 8'h00;
        fifo_status_changed = 1'b0;
        rx_fifo_count = 7'h00;
        rx_fifo_depth = 7'h40;
        tx_fifo_count = 7'h00;
        tx_fifo_depth = 7'h40;
        bridge_state = 8'h00;
        error_status = 32'h0;
    end

    // Monitor modport used by UVM components
    modport monitor (
        input clk,
        input rst_n,
        input frame_parser_state_changed,
        input current_frame_parser_state,
        input fifo_status_changed,
        input rx_fifo_count,
        input rx_fifo_depth,
        input tx_fifo_count,
        input tx_fifo_depth,
        input bridge_state,
        input error_status,
        import get_frame_parser_state_name
    );

    // DUT modport for RTL connectivity
    modport dut (
        input clk,
        input rst_n,
        output frame_parser_state_changed,
        output current_frame_parser_state,
        output fifo_status_changed,
        output rx_fifo_count,
        output rx_fifo_depth,
        output tx_fifo_count,
        output tx_fifo_depth,
        output bridge_state,
        output error_status
    );

endinterface
