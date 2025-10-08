`timescale 1ns / 1ps

// Frame Parser Module for UART-AXI4 Bridge
// Implements state machine from Section 6.6 of protocol specification
//
// Debug instrumentation added 2025-10-05 per fpga_debug_work_plan.md  
// Phase 1&2 signals: debug_rx_sof_raw, debug_rx_sof_proc, debug_crc_match,
//                    debug_status_gen, debug_error_cause
module Frame_Parser #(
    parameter int CLK_FREQ_HZ = 125_000_000,   // System clock frequency (125MHz)
    parameter int BAUD_RATE = 115200,
    parameter int TIMEOUT_BYTE_TIMES = 10     // Timeout after 10 byte times of idle
)(
    input  logic        clk,
    input  logic        rst,
    
    // FIFO interface (from UART RX)
    input  logic [7:0]  rx_fifo_data,
    input  logic        rx_fifo_empty,
    output logic        rx_fifo_rd_en,
    
    // Parsed frame output
    output logic [7:0]  cmd,
    output logic [31:0] addr,
    output logic [7:0]  data_out [0:63],    // Max 16 x 32-bit = 64 bytes
    output logic [5:0]  data_count,         // Number of valid data bytes
    output logic        frame_valid,        // Frame is valid and ready
    output logic [7:0]  error_status,       // Error status code
    output logic        frame_error,        // Frame has error
    
    // Control
    input  logic        frame_consumed,     // Frame has been processed
    output logic        parser_busy,        // Parser is active
    // Debug signals for HW analysis
    output logic [7:0] debug_cmd_in,
    output logic [7:0] debug_cmd_decoded,
    output logic [7:0] debug_status_out,
    output logic [7:0] debug_crc_in,
    output logic [7:0] debug_crc_calc,
    output logic       debug_crc_error,
    output logic [3:0] debug_state,
    output logic [7:0] debug_error_cause
);

    // Protocol constants
    localparam [7:0] SOF_HOST_TO_DEVICE = 8'hA5;
    
    // Status codes from Section 3
    localparam [7:0] STATUS_OK        = 8'h00;
    localparam [7:0] STATUS_CRC_ERR   = 8'h01;
    localparam [7:0] STATUS_CMD_INV   = 8'h02;
    localparam [7:0] STATUS_ADDR_ALIGN = 8'h03;
    localparam [7:0] STATUS_TIMEOUT   = 8'h04;
    localparam [7:0] STATUS_LEN_RANGE = 8'h07;
    
    // Debug signals for FPGA debugging - Phase 1 & 2 (ref: fpga_debug_work_plan.md)
    logic [7:0] debug_rx_sof_raw;     // Received SOF before correction
    logic [7:0] debug_rx_sof_proc;    // SOF after processing (should be 0x5A)
    logic       debug_crc_match;      // CRC validation result
    logic [7:0] debug_status_gen;     // STATUS generation trace
    logic [7:0] debug_error_cause_internal;    // Error source classification
    
    // Error cause encoding: 0x0=No error, 0x1=CRC mismatch, 0x2=AXI timeout, 0x3=Unsupported command
    
    // Timeout calculation
    localparam int BYTE_TIME_CLOCKS = CLK_FREQ_HZ / (BAUD_RATE / 10); // 10 bits per byte
    localparam int TIMEOUT_CLOCKS = BYTE_TIME_CLOCKS * TIMEOUT_BYTE_TIMES;
    localparam int TIMEOUT_WIDTH = $clog2(TIMEOUT_CLOCKS + 1);
    
    // State machine
    typedef enum logic [3:0] {
        IDLE,
        CMD,
        ADDR_BYTE0,
        ADDR_BYTE1,
        ADDR_BYTE2,
        ADDR_BYTE3,
        DATA_RX,
        CRC_RX,
        VALIDATE,
        ERROR
    } parser_state_t;
    
    parser_state_t state, state_next;
    
    // Internal registers
    logic [7:0]  cmd_reg;
    logic [7:0]  current_cmd;     // Current command being processed
    logic [31:0] addr_reg;
    logic [7:0]  data_reg [0:63];
    logic [5:0]  data_byte_count;
    logic [7:0]  expected_crc;
    logic [7:0]  received_crc;
    logic [7:0]  error_status_reg;
    
    // Timeout counter
    logic [TIMEOUT_WIDTH-1:0] timeout_counter;
    logic timeout_occurred;
    logic timeout_monitor_active;
    
    // CRC calculator instance
    logic crc_enable;
    logic crc_reset;
    logic [7:0] crc_data_in;
    logic [7:0] crc_out;
    
    Crc8_Calculator crc_calc (
        .clk(clk),
        .rst(rst),
        .crc_enable(crc_enable),
        .data_in(crc_data_in),
        .crc_reset(crc_reset),
        .crc_out(crc_out),
        .crc_final(expected_crc)
    );
    
    // Command field parsing
    logic rw_bit;
    logic inc_bit;
    logic [1:0] size_field;
    logic [3:0] len_field;
    logic [5:0] expected_data_bytes;  // Now a register (updated in sequential logic)
    
    // Debug signals for hardware analysis - CMD parsing
    logic [7:0] debug_rx_cmd_raw;
    logic [7:0] debug_rx_cmd_parsed;
    logic       debug_rx_rw_bit;
    logic       debug_rx_inc_bit;
    logic [1:0] debug_rx_size_field;
    logic [3:0] debug_rx_len_field;
    logic [5:0] debug_rx_expected_bytes;
    
    always_comb begin
        rw_bit = current_cmd[7];
        inc_bit = current_cmd[6];
        size_field = current_cmd[5:4];
        len_field = current_cmd[3:0];
        
        // Debug signal assignments
        debug_rx_cmd_raw = rx_fifo_data;
        debug_rx_cmd_parsed = current_cmd;
        debug_rx_rw_bit = rw_bit;
        debug_rx_inc_bit = inc_bit;
        debug_rx_size_field = size_field;
        debug_rx_len_field = len_field;
        debug_rx_expected_bytes = expected_data_bytes;
    end
    
    // Command validation
    logic cmd_valid;
    always_comb begin
        cmd_valid = 1'b1;
        
        // Check for reserved size field
        if (current_cmd[5:4] == 2'b11) begin
            cmd_valid = 1'b0;
        end
        
        // Check LEN range (should be 1-16, encoded as 0-15)
        if (current_cmd[3:0] > 15) begin  // This is impossible with 4 bits, but for clarity
            cmd_valid = 1'b0;
        end
    end
    
    // Timeout management
    always_comb begin
        unique case (state)
            CMD,
            ADDR_BYTE0,
            ADDR_BYTE1,
            ADDR_BYTE2,
            ADDR_BYTE3,
            DATA_RX,
            CRC_RX: timeout_monitor_active = 1'b1;
            default: timeout_monitor_active = 1'b0;
        endcase
    end

    always_ff @(posedge clk) begin
        if (rst || !timeout_monitor_active) begin
            timeout_counter <= '0;
            timeout_occurred <= 1'b0;
        end else begin
            if (!rx_fifo_empty) begin
                timeout_counter <= '0;
                timeout_occurred <= 1'b0;
            end else if (timeout_counter >= TIMEOUT_CLOCKS) begin
                timeout_occurred <= 1'b1;
            end else begin
                timeout_counter <= timeout_counter + 1;
            end
        end
    end
    
    // State machine (sequential part)
    always_ff @(posedge clk) begin
        if (rst) begin
            state <= IDLE;
            cmd_reg <= '0;
            current_cmd <= '0;  // Initialize current_cmd to prevent X-state
            addr_reg <= '0;
            data_byte_count <= '0;
            received_crc <= '0;
            error_status_reg <= STATUS_OK;
            expected_data_bytes <= '0;  // Initialize expected_data_bytes to prevent X-state
            // Initialize data array to prevent X-state propagation
            for (int i = 0; i < 64; i++) begin
                data_reg[i] <= '0;
            end
        end else begin
            state <= state_next;
            
            if (rx_fifo_rd_en && !rx_fifo_empty) begin
                case (state)
                    CMD: begin
                        cmd_reg <= rx_fifo_data;
                        current_cmd <= rx_fifo_data;  // Capture immediately for later use
                        // expected_data_bytes calculation is handled separately above
                    end
                    ADDR_BYTE0: begin
                        addr_reg[7:0] <= rx_fifo_data;
                    end
                    ADDR_BYTE1: begin
                        addr_reg[15:8] <= rx_fifo_data;
                    end
                    ADDR_BYTE2: begin
                        addr_reg[23:16] <= rx_fifo_data;
                    end
                    ADDR_BYTE3: begin
                        addr_reg[31:24] <= rx_fifo_data;
                    end
                    DATA_RX: begin
                        data_reg[data_byte_count] <= rx_fifo_data;
                        data_byte_count <= data_byte_count + 1;
                    end
                    CRC_RX: begin
                        received_crc <= rx_fifo_data;
                    end
                endcase
            end
            
            // Reset data byte count at start of new frame
            if (state == IDLE) begin
                data_byte_count <= '0;
                error_status_reg <= STATUS_OK;
                current_cmd <= '0;
                expected_data_bytes <= '0;  // Reset expected data bytes
            end
            
            // Handle expected_data_bytes calculation separately to prevent X-state contamination
            if (state == CMD && rx_fifo_rd_en && !rx_fifo_empty) begin
                // Calculate expected data bytes based on command fields
                if (rx_fifo_data[7] == 1'b1) begin  // READ command (RW bit = 1)
                    expected_data_bytes <= 6'd0;  // No data bytes for read commands
                    `ifdef ENABLE_DEBUG
                        $display("DEBUG: Frame_Parser CMD expected_data_bytes=0 (READ) cmd=0x%02X at time %0t", rx_fifo_data, $time);
                    `endif
                end else begin  // WRITE command (RW bit = 0)
                    case (rx_fifo_data[5:4])  // SIZE field
                        2'b00: expected_data_bytes <= (rx_fifo_data[3:0] + 1) * 1;  // BYTE (8-bit)
                        2'b01: expected_data_bytes <= (rx_fifo_data[3:0] + 1) * 2;  // HALF (16-bit)
                        2'b10: expected_data_bytes <= (rx_fifo_data[3:0] + 1) * 4;  // WORD (32-bit)
                        2'b11: expected_data_bytes <= 6'd0;                         // Invalid size
                    endcase
                    `ifdef ENABLE_DEBUG
                        $display("DEBUG: Frame_Parser CMD expected_data_bytes=%d (write) cmd=0x%02X size=0b%02b len=%d at time %0t", 
                                 (rx_fifo_data[5:4] == 2'b00) ? (rx_fifo_data[3:0] + 1) * 1 :
                                 (rx_fifo_data[5:4] == 2'b01) ? (rx_fifo_data[3:0] + 1) * 2 :
                                 (rx_fifo_data[5:4] == 2'b10) ? (rx_fifo_data[3:0] + 1) * 4 : 0,
                                 rx_fifo_data, rx_fifo_data[5:4], rx_fifo_data[3:0], $time);
                    `endif
                end
            end
            
            // Set error status in validation state
            if (state == VALIDATE) begin
                if (!cmd_valid) begin
                    error_status_reg <= (size_field == 2'b11) ? STATUS_CMD_INV : STATUS_LEN_RANGE;
                    // Debug error cause: 0x3 = Unsupported command
                    debug_error_cause_internal <= 8'h03;
                end else if (received_crc != expected_crc) begin
                    error_status_reg <= STATUS_CRC_ERR;
                    // Debug error cause: 0x1 = CRC mismatch
                    debug_error_cause_internal <= 8'h01;
                    `ifdef ENABLE_DEBUG
                        $display("DEBUG: Frame_Parser CRC mismatch recv=0x%02X exp=0x%02X at time %0t", received_crc, expected_crc, $time);
                        $display("DEBUG: Frame_Parser CRC context cmd=0x%02X addr=0x%08X data_bytes=%0d expected_bytes=%0d", current_cmd, addr_reg, data_byte_count, expected_data_bytes);
                        for (int dbg_i = 0; dbg_i < data_byte_count; dbg_i++) begin
                            if (dbg_i < 8) begin
                                $display("DEBUG: Frame_Parser data[%0d]=0x%02X", dbg_i, data_reg[dbg_i]);
                            end else begin
                                if (dbg_i == 8) begin
                                    $display("DEBUG: Frame_Parser ... remaining %0d byte(s) omitted", data_byte_count - 8);
                                end
                                break;
                            end
                        end
                    `endif
                end else begin
                    error_status_reg <= STATUS_OK;
                    // Debug error cause: 0x0 = No error
                    debug_error_cause_internal <= 8'h00;
                end
            end
            
            // Handle timeout
            if (timeout_occurred && (state != IDLE) && (state != ERROR)) begin
                error_status_reg <= STATUS_TIMEOUT;
                // Debug error cause: 0x2 = AXI timeout
                debug_error_cause_internal <= 8'h02;
            end
            
            // Clear frame_consumed acknowledgment
            if (frame_consumed) begin
                // Frame has been processed, ready for next frame
            end
        end
    end
    
    // State machine (combinational part)
    always_comb begin
        state_next = state;
        rx_fifo_rd_en = 1'b0;
        crc_enable = 1'b0;
        crc_reset = 1'b0;
        crc_data_in = rx_fifo_data;
        
        // Default debug signal assignments to prevent latches
        debug_rx_sof_raw = 8'h00;
        debug_rx_sof_proc = 8'h00;
        debug_crc_match = 1'b0;
        debug_status_gen = error_status_reg;  // Always show current status
        
        case (state)
            IDLE: begin
                if (!rx_fifo_empty && (rx_fifo_data == SOF_HOST_TO_DEVICE)) begin
                    // Debug signal assignments - Phase 2
                    debug_rx_sof_raw = rx_fifo_data;
                    debug_rx_sof_proc = SOF_HOST_TO_DEVICE;  // Expected processed value
                    
                    rx_fifo_rd_en = 1'b1;
                    crc_reset = 1'b1;  // Reset CRC when SOF is detected (fix timing)
                    state_next = CMD;
                    `ifdef ENABLE_DEBUG
                        $display("DEBUG: Frame_Parser SOF detected = 0x%02X at time %0t", rx_fifo_data, $time);
                    `endif
                end else if (!rx_fifo_empty) begin
                    // Debug signal assignments for invalid SOF
                    debug_rx_sof_raw = rx_fifo_data;
                    debug_rx_sof_proc = 8'h00;  // Mark as invalid
                    
                    rx_fifo_rd_en = 1'b1;  // Discard invalid SOF
                    `ifdef ENABLE_DEBUG
                        $display("DEBUG: Frame_Parser invalid SOF discarded = 0x%02X at time %0t", rx_fifo_data, $time);
                    `endif
                end
            end
            
            CMD: begin
                if (!rx_fifo_empty) begin
                    rx_fifo_rd_en = 1'b1;
                    crc_enable = 1'b1;
                    state_next = ADDR_BYTE0;
                end else if (timeout_occurred) begin
                    state_next = ERROR;
                end
            end
            
            ADDR_BYTE0: begin
                if (!rx_fifo_empty) begin
                    rx_fifo_rd_en = 1'b1;
                    crc_enable = 1'b1;
                    state_next = ADDR_BYTE1;
                end else if (timeout_occurred) begin
                    state_next = ERROR;
                end
            end
            
            ADDR_BYTE1: begin
                if (!rx_fifo_empty) begin
                    rx_fifo_rd_en = 1'b1;
                    crc_enable = 1'b1;
                    state_next = ADDR_BYTE2;
                end else if (timeout_occurred) begin
                    state_next = ERROR;
                end
            end
            
            ADDR_BYTE2: begin
                if (!rx_fifo_empty) begin
                    rx_fifo_rd_en = 1'b1;
                    crc_enable = 1'b1;
                    state_next = ADDR_BYTE3;
                end else if (timeout_occurred) begin
                    state_next = ERROR;
                end
            end
            
            ADDR_BYTE3: begin
                if (!rx_fifo_empty) begin
                    rx_fifo_rd_en = 1'b1;
                    crc_enable = 1'b1;
                    // Proper state transition based on command type and expected data bytes
                    if (expected_data_bytes == 0) begin
                        state_next = CRC_RX;  // No data bytes, go directly to CRC
                        `ifdef ENABLE_DEBUG
                            $display("DEBUG: Frame_Parser ADDR_BYTE3->CRC_RX (no data bytes) at time %0t", $time);
                        `endif
                    end else begin
                        state_next = DATA_RX;  // Has data bytes, go to DATA_RX
                        `ifdef ENABLE_DEBUG
                            $display("DEBUG: Frame_Parser ADDR_BYTE3->DATA_RX (expected_bytes=%d) at time %0t", expected_data_bytes, $time);
                        `endif
                    end
                end else if (timeout_occurred) begin
                    state_next = ERROR;
                end
            end
            
            DATA_RX: begin
                if (!rx_fifo_empty) begin
                    rx_fifo_rd_en = 1'b1;
                    crc_enable = 1'b1;
                    // Safer comparison: check if we've received all expected data bytes
                    if (data_byte_count + 1 >= expected_data_bytes) begin
                        state_next = CRC_RX;
                        `ifdef ENABLE_DEBUG
                            $display("DEBUG: Frame_Parser DATA_RX->CRC_RX (count=%d, expected=%d) at time %0t", 
                                     data_byte_count + 1, expected_data_bytes, $time);
                        `endif
                    end else begin
                        `ifdef ENABLE_DEBUG
                            $display("DEBUG: Frame_Parser DATA_RX continuing (count=%d, expected=%d) at time %0t", 
                                     data_byte_count + 1, expected_data_bytes, $time);
                        `endif
                    end
                end else if (timeout_occurred) begin
                    state_next = ERROR;
                end
            end
            
            CRC_RX: begin
                if (!rx_fifo_empty) begin
                    rx_fifo_rd_en = 1'b1;
                    state_next = VALIDATE;
                end else if (timeout_occurred) begin
                    state_next = ERROR;
                end
            end
            
            VALIDATE: begin
                // Debug signal assignments - Phase 2
                debug_crc_match = (received_crc == expected_crc);
                debug_status_gen = error_status_reg;
                
                if (frame_consumed) begin
                    state_next = IDLE;
                    `ifdef ENABLE_DEBUG
                        $display("DEBUG: Frame_Parser frame consumed, returning to IDLE at time %0t", $time);
                    `endif
                end else begin
                    state_next = VALIDATE;  // Stay in VALIDATE until frame is consumed
                    `ifdef ENABLE_DEBUG
                        if (error_status_reg == STATUS_OK) begin
                            $display("DEBUG: Frame_Parser VALID frame ready (waiting for consumption) at time %0t", $time);
                        end else begin
                            $display("DEBUG: Frame_Parser INVALID frame (status=0x%02X) waiting for consumption at time %0t", 
                                     error_status_reg, $time);
                        end
                    `endif
                end
            end
            
            ERROR: begin
                if (frame_consumed) begin
                    state_next = IDLE;
                end else begin
                    state_next = ERROR;  // Stay in ERROR until frame is consumed
                end
            end
        endcase
    end
    
    // Output assignments
    assign cmd = cmd_reg;
    assign addr = addr_reg;
    assign data_count = data_byte_count;
    assign frame_valid = (state == VALIDATE) && (error_status_reg == STATUS_OK);
    assign error_status = error_status_reg;
    assign frame_error = (state == VALIDATE) && (error_status_reg != STATUS_OK) || 
                        (state == ERROR) || timeout_occurred;
    assign parser_busy = (state != IDLE);
    
    // Debug signal assignments for hardware analysis
    assign debug_cmd_in = rx_fifo_data;
    assign debug_cmd_decoded = cmd_reg;
    assign debug_status_out = error_status_reg;
    assign debug_crc_in = received_crc;
    assign debug_crc_calc = expected_crc;
    assign debug_crc_error = (received_crc != expected_crc);
    assign debug_crc_received = received_crc;
    assign debug_crc_expected = expected_crc;
    assign debug_error_status = error_status_reg;
    assign debug_state = state;
    assign debug_parser_state = state;
    assign debug_error_cause = debug_error_cause_internal;
    assign debug_frame_valid_flag = frame_valid;
    
    // Copy data array to output
    always_comb begin
        for (int i = 0; i < 64; i++) begin
            data_out[i] = data_reg[i];
        end
    end

endmodule