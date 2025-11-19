`timescale 1ns / 1ps

//==============================================================================
// Frame_Parser_Assertions.sv
// SystemVerilog Assertion Module for Frame Parser
// 
// Description:
//   This module contains SystemVerilog assertions for Frame_Parser.sv
//   Connected via bind statement for clean separation of RTL and verification
//   
// Key Features:
//   - Real-time protocol violation detection
//   - CRC validation integrity verification  
//   - Frame state machine correctness
//   - Timeout detection and handling
//   - Immediate $fatal on critical violations
//
// Usage:
//   bind Frame_Parser Frame_Parser_Assertions FP_assertions_inst (.*);
//==============================================================================

module Frame_Parser_Assertions (
    input logic clk,
    input logic rst,
    
    // State machine monitoring
    input logic [3:0] state,
    input logic [3:0] state_next,
    
    // FIFO interface monitoring
    input logic [7:0] rx_fifo_data,
    input logic rx_fifo_empty,
    input logic rx_fifo_rd_en,
    
    // Frame validation monitoring  
    input logic frame_valid,
    input logic frame_consumed,
    input logic frame_error,
    
    // CRC monitoring (critical)
    input logic [7:0] received_crc,
    input logic [7:0] expected_crc,
    
    // Error status monitoring
    input logic [7:0] error_status_reg,
    
    // Timeout monitoring
    input logic timeout_occurred,
    
    // Command processing monitoring
    input logic [7:0] cmd_reg,
    input logic cmd_valid,
    
    // Debug signals for enhanced monitoring
    input logic [31:0] addr_reg,
    input logic [6:0] data_byte_count,
    input logic [6:0] expected_data_bytes
);

    // State definitions (must match Frame_Parser.sv)
    localparam [3:0] IDLE       = 4'h0;
    localparam [3:0] CMD        = 4'h1;
    localparam [3:0] ADDR_BYTE0 = 4'h2;
    localparam [3:0] ADDR_BYTE1 = 4'h3;
    localparam [3:0] ADDR_BYTE2 = 4'h4;
    localparam [3:0] ADDR_BYTE3 = 4'h5;
    localparam [3:0] DATA_RX    = 4'h6;
    localparam [3:0] CRC_RX     = 4'h7;
    localparam [3:0] VALIDATE   = 4'h8;
    localparam [3:0] ERROR      = 4'h9;
    
    // Protocol constants (must match Frame_Parser.sv)
    localparam [7:0] SOF_HOST_TO_DEVICE = 8'hA5;
    localparam [7:0] STATUS_OK          = 8'h00;
    localparam [7:0] STATUS_CRC_ERR     = 8'h01;
    localparam [7:0] STATUS_CMD_INV     = 8'h02;
    localparam [7:0] STATUS_ADDR_ALIGN  = 8'h03;
    localparam [7:0] STATUS_TIMEOUT     = 8'h04;
    localparam [7:0] STATUS_LEN_RANGE   = 8'h07;
    // Allow ample cycles between sequential state transitions to account for
    // high-speed UART byte arrival latency (currently ~160 clk cycles per byte at 125 MHz).
    localparam int STATE_ADVANCE_MAX_CYCLES = 16384;

    //==========================================================================
    // CRITICAL PROTOCOL ASSERTIONS
    //==========================================================================

    // A1: SOF Detection Reliability - SOF must trigger state transition
    property sof_detection_reliability;
        @(posedge clk) disable iff (rst)
        (state == IDLE && !rx_fifo_empty && rx_fifo_data == SOF_HOST_TO_DEVICE && rx_fifo_rd_en)
        |=> (state == CMD);
    endproperty
    assert_sof_detection: assert property (sof_detection_reliability)
        else $fatal("ASSERTION_FAIL: SOF detection failed - Critical protocol violation at %t", $time);

    // A2: CRC Validation Integrity (MOST CRITICAL)
    // Allow the status register one to two cycles to settle after the comparison window
    property crc_match_status_ok;
        @(posedge clk) disable iff (rst)
        (state == VALIDATE && (received_crc == expected_crc)) |-> ##[0:2]
        (error_status_reg == STATUS_OK);
    endproperty
    assert_crc_match_status: assert property (crc_match_status_ok)
        else $fatal("ASSERTION_FAIL: CRC validation integrity violation (match) - expected STATUS_OK, received=0x%02X, expected=0x%02X, status=0x%02X at %t",
                    received_crc, expected_crc, error_status_reg, $time);

    property crc_mismatch_status_err;
        @(posedge clk) disable iff (rst)
        (state == VALIDATE && (received_crc != expected_crc)) |-> ##[0:2]
        (error_status_reg == STATUS_CRC_ERR);
    endproperty
    assert_crc_mismatch_status: assert property (crc_mismatch_status_err)
        else $fatal("ASSERTION_FAIL: CRC validation integrity violation (mismatch) - expected STATUS_CRC_ERR, received=0x%02X, expected=0x%02X, status=0x%02X at %t",
                    received_crc, expected_crc, error_status_reg, $time);

    // A3: Frame Valid Generation Correctness - CRITICAL FIX for frame_consumed handling
    // RESET command (0xFF) exclusion: RESET is a control command, not a data frame
    property frame_valid_generation_correctness;
        @(posedge clk) disable iff (rst)
        (state == VALIDATE && error_status_reg == STATUS_OK && (received_crc == expected_crc) && !frame_consumed && cmd_reg != 8'hFF)
        |=> frame_valid;
    endproperty
    assert_frame_valid: assert property (frame_valid_generation_correctness)
        else $fatal("ASSERTION_FAIL: frame_valid generation failed - Critical system failure at %t", $time);
    // A4: Frame Valid Persistence Guarantee
    property frame_valid_persistence_guarantee;
        @(posedge clk) disable iff (rst)
        (frame_valid && !frame_consumed) |=> frame_valid;
    endproperty
    assert_frame_persistence: assert property (frame_valid_persistence_guarantee)
        else $fatal("ASSERTION_FAIL: frame_valid persistence violation - Data loss risk at %t", $time);

    // A5: State Machine Sequential Integrity
    property state_machine_sequential_integrity;
        @(posedge clk) disable iff (rst)
        (state == IDLE && rx_fifo_rd_en && !rx_fifo_empty && rx_fifo_data == SOF_HOST_TO_DEVICE) |=>
            (state == CMD) ##[1:STATE_ADVANCE_MAX_CYCLES]
            (state == ADDR_BYTE0 || state == ERROR) ##[1:STATE_ADVANCE_MAX_CYCLES]
            (state == ADDR_BYTE1 || state == ERROR) ##[1:STATE_ADVANCE_MAX_CYCLES]
            (state == ADDR_BYTE2 || state == ERROR) ##[1:STATE_ADVANCE_MAX_CYCLES]
            (state == ADDR_BYTE3 || state == ERROR);
    endproperty
    assert_state_sequence: assert property (state_machine_sequential_integrity)
        else $fatal("ASSERTION_FAIL: State machine sequence violation at %t", $time);

    // A6: Timeout Handling Correctness
    property timeout_handling_correctness;
        @(posedge clk) disable iff (rst)
        (timeout_occurred && (state != IDLE) && (state != ERROR)) |=> 
        (state == ERROR || error_status_reg == STATUS_TIMEOUT);
    endproperty
    assert_timeout_handling: assert property (timeout_handling_correctness)
        else $fatal("ASSERTION_FAIL: Timeout handling violation at %t", $time);

    // A7: Frame Error Detection Accuracy
    property frame_error_detection_accuracy;
        @(posedge clk) disable iff (rst)
        (state == VALIDATE) |->
        ((error_status_reg != STATUS_OK) <-> frame_error);
    endproperty
    assert_frame_error: assert property (frame_error_detection_accuracy)
        else $fatal("ASSERTION_FAIL: Frame error detection mismatch at %t", $time);

    //==========================================================================
    // ENHANCED MONITORING ASSERTIONS
    //==========================================================================

    // A8: Data Byte Count Integrity
    property data_byte_count_integrity;
        @(posedge clk) disable iff (rst)
        (state == DATA_RX && !rx_fifo_empty && rx_fifo_rd_en) |=> 
        (data_byte_count <= expected_data_bytes);
    endproperty
    assert_data_count: assert property (data_byte_count_integrity)
        else $fatal("ASSERTION_FAIL: Data byte count overflow at %t", $time);

    // A9: Command Validity Check
    property command_validity_check;
        @(posedge clk) disable iff (rst)
        (state == CMD && !rx_fifo_empty && rx_fifo_rd_en) |=> 
        ##1 (cmd_valid || (error_status_reg == STATUS_CMD_INV) || (error_status_reg == STATUS_LEN_RANGE));
    endproperty
    assert_cmd_validity: assert property (command_validity_check)
        else $fatal("ASSERTION_FAIL: Command validity check failed at %t", $time);

    // A10: FIFO Read Enable Safety
    property fifo_read_safety;
        @(posedge clk) disable iff (rst)
        rx_fifo_rd_en |-> !rx_fifo_empty;
    endproperty
    assert_fifo_safety: assert property (fifo_read_safety)
        else $fatal("ASSERTION_FAIL: FIFO read from empty FIFO attempted at %t", $time);

    //==========================================================================
    // EVENT-DRIVEN MINIMAL LOGGING
    //==========================================================================

    // Minimal success event logging (only critical events)
    always @(posedge clk) begin
        if (!rst) begin
            // SOF Detection Success
            if (state == IDLE && !rx_fifo_empty && rx_fifo_data == SOF_HOST_TO_DEVICE && rx_fifo_rd_en) begin
                $info("[FRAME_PARSER] SOF DETECTED at %t", $time);
            end
            
            // CRC Validation Results
            if (state == VALIDATE) begin
                if (error_status_reg == STATUS_OK) begin
                    $info("[FRAME_PARSER] FRAME VALID: CRC=0x%02X at %t", received_crc, $time);
                end else if (error_status_reg == STATUS_CRC_ERR) begin
                    $warning("[FRAME_PARSER] CRC MISMATCH: received=0x%02X, expected=0x%02X at %t", 
                             received_crc, expected_crc, $time);
                end else begin
                    $warning("[FRAME_PARSER] FRAME INVALID: status=0x%02X at %t", error_status_reg, $time);
                end
            end
            
            // Timeout Events
            if (timeout_occurred && state != IDLE) begin
                $warning("[FRAME_PARSER] TIMEOUT in state %0d at %t", state, $time);
            end
            
            // Frame Consumption
            if (frame_consumed && frame_valid) begin
                $info("[FRAME_PARSER] FRAME CONSUMED at %t", $time);
            end
        end
    end

    //==========================================================================
    // COVERAGE MONITORS
    //==========================================================================

    // State coverage
    cover property (@(posedge clk) disable iff (rst) state == IDLE);
    cover property (@(posedge clk) disable iff (rst) state == CMD);
    cover property (@(posedge clk) disable iff (rst) state == VALIDATE);
    cover property (@(posedge clk) disable iff (rst) state == ERROR);
    
    // Error status coverage
    cover property (@(posedge clk) disable iff (rst) error_status_reg == STATUS_OK);
    cover property (@(posedge clk) disable iff (rst) error_status_reg == STATUS_CRC_ERR);
    cover property (@(posedge clk) disable iff (rst) error_status_reg == STATUS_TIMEOUT);
    cover property (@(posedge clk) disable iff (rst) error_status_reg == STATUS_CMD_INV);

endmodule