`timescale 1ns / 1ps

//==============================================================================
// Frame_Parser_Assertions_Bind.sv
// Bind Statement File for Frame Parser Assertions
//
// Description:
//   This file contains the bind statement to connect Frame_Parser_Assertions
//   to Frame_Parser module instances. This provides clean separation between
//   RTL code and verification code.
//
// Usage:
//   Include this file in compilation after both Frame_Parser.sv and 
//   Frame_Parser_Assertions.sv are compiled.
//==============================================================================

// Bind the assertion module to all instances of Frame_Parser
bind Frame_Parser Frame_Parser_Assertions FP_assertions_inst (
    .clk(clk),
    .rst(rst),
    
    // State machine monitoring
    .state(state),
    .state_next(state_next),
    
    // FIFO interface monitoring
    .rx_fifo_data(rx_fifo_data),
    .rx_fifo_empty(rx_fifo_empty),
    .rx_fifo_rd_en(rx_fifo_rd_en),
    
    // Frame validation monitoring
    .frame_valid(frame_valid),
    .frame_consumed(frame_consumed),
    .frame_error(frame_error),
    
    // CRC monitoring (critical)
    .received_crc(received_crc),
    .expected_crc(expected_crc),
    
    // Error status monitoring
    .error_status_reg(error_status_reg),
    
    // Timeout monitoring
    .timeout_occurred(timeout_occurred),
    
    // Command processing monitoring
    .cmd_reg(cmd_reg),
    .cmd_valid(cmd_valid),
    
    // Debug signals for enhanced monitoring
    .addr_reg(addr_reg),
    .data_byte_count(data_byte_count),
    .expected_data_bytes(expected_data_bytes)
);