`timescale 1ns / 1ps

// Frame Builder module for UART-AXI4 Bridge
// Constructs response frames per protocol specification
module Frame_Builder (
    input  logic        clk,
    input  logic        rst,
    
    // Frame construction inputs
    input  logic [7:0]  status_code,        // Response status code
    input  logic [7:0]  cmd_echo,           // Echo of original command
    input  logic [31:0] addr_echo,          // Echo of address (for read responses)
    input  logic [7:0]  response_data [0:63], // Response data (for read responses)
    input  logic [5:0]  response_data_count,   // Number of response data bytes
    input  logic        build_response,     // Start building response
    input  logic        is_read_response,   // True for read response, false for write
    
    // FIFO interface (to UART TX)
    output logic [7:0]  tx_fifo_data,
    output logic        tx_fifo_wr_en,
    input  logic        tx_fifo_full,
    
    // Status
    output logic        builder_busy,
    output logic        response_complete
);

    // Protocol constants
    localparam [7:0] SOF_DEVICE_TO_HOST = 8'h5A;
    localparam [7:0] STATUS_OK = 8'h00;
    
    // State machine
    typedef enum logic [3:0] {
        IDLE,
        SOF,
        STATUS,
        CMD,
        ADDR_BYTE0,
        ADDR_BYTE1,
        ADDR_BYTE2,
        ADDR_BYTE3,
        DATA,
        CRC,
        DONE,
        INTER_FRAME_GAP
    } builder_state_t;
    
    builder_state_t state, state_next;
    
    // Internal registers
    logic [7:0]  status_reg;
    logic [7:0]  cmd_reg;
    logic [31:0] addr_reg;
    logic [7:0]  data_reg [0:63];
    logic [5:0]  data_count_reg;
    logic [5:0]  data_index;
    logic        is_read_reg;
    
    // Edge detection for build_response
    logic        build_response_prev;
    logic        build_response_edge;
    
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
        .crc_final()  // Not used here, use crc_out
    );
    
    // Edge detection assignment
    assign build_response_edge = build_response && !build_response_prev;
    
    // State machine (sequential part)
    always_ff @(posedge clk) begin
        if (rst) begin
            state <= IDLE;
            status_reg <= '0;
            cmd_reg <= '0;
            addr_reg <= '0;
            data_count_reg <= '0;
            data_index <= '0;
            is_read_reg <= 1'b0;
            build_response_prev <= 1'b0;
            // Initialize data array to prevent X-state propagation
            for (int i = 0; i < 64; i++) begin
                data_reg[i] <= '0;
            end
        end else begin
            state <= state_next;
            build_response_prev <= build_response;
            
            // Load inputs when build_response rising edge detected (single clock edge trigger)
            if (build_response_edge && (state == IDLE)) begin
                status_reg <= status_code;
                cmd_reg <= cmd_echo;
                addr_reg <= addr_echo;
                data_count_reg <= response_data_count;
                data_index <= '0;
                is_read_reg <= is_read_response;
                
                // Copy response data
                for (int i = 0; i < 64; i++) begin
                    data_reg[i] <= response_data[i];
                end
            end
            
            // Increment data index when writing data bytes successfully
            if ((state == DATA) && tx_fifo_wr_en && !tx_fifo_full) begin
                data_index <= data_index + 1;
            end
            
            // Reset data_index when starting new frame
            if (build_response_edge) begin
                data_index <= '0;
            end
        end
    end
    
    // State machine (combinational part)
    always_comb begin
        state_next = state;
        tx_fifo_data = '0;
        tx_fifo_wr_en = 1'b0;
        crc_enable = 1'b0;
        crc_reset = 1'b0;
        crc_data_in = '0;
        
        `ifdef ENABLE_DEBUG
            if (build_response_edge) begin
                $display("DEBUG: Frame_Builder triggered - cmd_echo=0x%02X, status_code=0x%02X at time %0t", 
                         cmd_echo, status_code, $time);
            end
        `endif
        crc_data_in = '0;
        
        case (state)
            IDLE: begin
                crc_reset = 1'b1;  // Reset CRC for new frame
                if (build_response_edge) begin
                    state_next = SOF;
                end
            end
            
            SOF: begin
                if (!tx_fifo_full) begin
                    tx_fifo_data = SOF_DEVICE_TO_HOST;
                    tx_fifo_wr_en = 1'b1;
                    `ifdef ENABLE_DEBUG
                        $display("DEBUG: Frame_Builder sending SOF = 0x%02X at time %0t", SOF_DEVICE_TO_HOST, $time);
                    `endif
                    state_next = STATUS;
                end
            end
            
            STATUS: begin
                if (!tx_fifo_full) begin
                    tx_fifo_data = status_reg;
                    tx_fifo_wr_en = 1'b1;
                    crc_enable = 1'b1;
                    crc_data_in = status_reg;
                    `ifdef ENABLE_DEBUG
                        $display("DEBUG: Frame_Builder sending STATUS = 0x%02X at time %0t", status_reg, $time);
                    `endif
                    state_next = CMD;
                end
            end
            
            CMD: begin
                if (!tx_fifo_full) begin
                    tx_fifo_data = cmd_reg;
                    tx_fifo_wr_en = 1'b1;
                    crc_enable = 1'b1;
                    crc_data_in = cmd_reg;
                    
                    // Decide next state based on response type and status
                    // Write response (MSB=0): SOF + STATUS + CMD + CRC (4 bytes total)
                    // Read response (MSB=1): SOF + STATUS + CMD + ADDR + DATA + CRC (7+ bytes total)
                    
                    // Force Write responses to be exactly 4 bytes by checking MSB=0
                    if (cmd_reg[7] == 1'b0) begin  // Write command (MSB=0)
                        // Write response: go directly to CRC after CMD
                        state_next = CRC;
                    end else if ((status_reg == STATUS_OK) && cmd_reg[7]) begin  // Read command (MSB=1) 
                        // Successful read response includes address and data
                        state_next = ADDR_BYTE0;
                    end else begin
                        // Error response - go directly to CRC
                        state_next = CRC;
                    end
                end
            end
            
            ADDR_BYTE0: begin
                if (!tx_fifo_full) begin
                    tx_fifo_data = addr_reg[7:0];
                    tx_fifo_wr_en = 1'b1;
                    crc_enable = 1'b1;
                    crc_data_in = addr_reg[7:0];
                    state_next = ADDR_BYTE1;
                end
            end
            
            ADDR_BYTE1: begin
                if (!tx_fifo_full) begin
                    tx_fifo_data = addr_reg[15:8];
                    tx_fifo_wr_en = 1'b1;
                    crc_enable = 1'b1;
                    crc_data_in = addr_reg[15:8];
                    state_next = ADDR_BYTE2;
                end
            end
            
            ADDR_BYTE2: begin
                if (!tx_fifo_full) begin
                    tx_fifo_data = addr_reg[23:16];
                    tx_fifo_wr_en = 1'b1;
                    crc_enable = 1'b1;
                    crc_data_in = addr_reg[23:16];
                    state_next = ADDR_BYTE3;
                end
            end
            
            ADDR_BYTE3: begin
                if (!tx_fifo_full) begin
                    tx_fifo_data = addr_reg[31:24];
                    tx_fifo_wr_en = 1'b1;
                    crc_enable = 1'b1;
                    crc_data_in = addr_reg[31:24];
                    
                    if (data_count_reg > 0) begin
                        state_next = DATA;
                    end else begin
                        state_next = CRC;
                    end
                end
            end
            
            DATA: begin
                if (!tx_fifo_full && (data_index < data_count_reg)) begin
                    tx_fifo_data = data_reg[data_index];
                    tx_fifo_wr_en = 1'b1;
                    crc_enable = 1'b1;
                    crc_data_in = data_reg[data_index];
                    
                    // Check if this will be the last data byte after incrementing
                    if ((data_index + 1) == data_count_reg) begin
                        state_next = CRC;
                    end
                    // else stay in DATA state for next byte
                end
            end
            
            CRC: begin
                if (!tx_fifo_full) begin
                    tx_fifo_data = crc_out;
                    tx_fifo_wr_en = 1'b1;
                    state_next = DONE;
                end
            end
            
            DONE: begin
                state_next = INTER_FRAME_GAP;
            end
            
            INTER_FRAME_GAP: begin
                // Wait one cycle for proper frame separation
                state_next = IDLE;
            end
        endcase
    end
    
    // Output assignments
    assign builder_busy = (state != IDLE);
    assign response_complete = (state == DONE) && (state_next == INTER_FRAME_GAP);

    // Assertions for verification
    `ifdef ENABLE_FRAME_BUILDER_ASSERTIONS
        // Should not start building when already busy
        assert_no_build_when_busy: assert property (
            @(posedge clk) disable iff (rst)
            builder_busy |-> !build_response
        ) else $warning("Frame_Builder: build_response asserted while busy");

        // response_complete should be a single-cycle pulse
        assert_response_complete_pulse: assert property (
            @(posedge clk) disable iff (rst)
            response_complete |=> !response_complete
        ) else $error("Frame_Builder: response_complete should be a single-cycle pulse");

        // Should not write to FIFO when full
        assert_no_write_when_full: assert property (
            @(posedge clk) disable iff (rst)
            tx_fifo_full |-> !tx_fifo_wr_en
        ) else $error("Frame_Builder: Writing to FIFO when full");
    `endif

endmodule