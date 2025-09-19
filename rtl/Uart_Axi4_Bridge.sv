`timescale 1ns / 1ps

// Top-level UART-AXI4-Lite Bridge Module
// Implements complete protocol per AXIUART_/docs/uart_axi4_protocol.md
module Uart_Axi4_Bridge #(
    parameter int CLK_FREQ_HZ = 50_000_000,     // System clock frequency
    parameter int BAUD_RATE = 115200,           // UART baud rate
    parameter int AXI_TIMEOUT = 1000,           // AXI timeout in clock cycles
    parameter int UART_OVERSAMPLE = 16,         // UART oversampling factor
    parameter int RX_FIFO_DEPTH = 64,           // RX FIFO depth
    parameter int TX_FIFO_DEPTH = 64,           // TX FIFO depth
    parameter int MAX_LEN = 16                  // Maximum LEN field value
)(
    // Clock and reset
    input  logic        clk,
    input  logic        rst,
    
    // UART interface
    input  logic        uart_rx,
    output logic        uart_tx,
    
    // AXI4-Lite master interface
    axi4_lite_if.master axi,
    
    // Status monitoring outputs
    output logic        bridge_busy,            // Bridge is actively processing
    output logic [7:0]  bridge_error_code,     // Current error code
    output logic [15:0] tx_transaction_count,  // TX transaction counter
    output logic [15:0] rx_transaction_count,  // RX transaction counter
    output logic [7:0]  fifo_status_flags,     // FIFO status flags
    
    // Statistics reset input
    input  logic        reset_statistics       // Pulse to reset counters
);

    // FIFO width calculation (7 bits for 64-deep FIFO)
    localparam int RX_FIFO_WIDTH = $clog2(RX_FIFO_DEPTH) + 1;
    localparam int TX_FIFO_WIDTH = $clog2(TX_FIFO_DEPTH) + 1;
    
    // UART RX signals
    logic [7:0] rx_data;
    logic rx_valid;
    logic rx_error;
    logic rx_busy;
    
    // UART TX signals
    logic [7:0] tx_data;
    logic tx_start;
    logic tx_busy;
    logic tx_done;
    
    // RX FIFO signals
    logic [7:0] rx_fifo_data;
    logic rx_fifo_wr_en;
    logic rx_fifo_full;
    logic rx_fifo_empty;
    logic rx_fifo_rd_en;
    logic [7:0] rx_fifo_rd_data;
    logic [RX_FIFO_WIDTH-1:0] rx_fifo_count;
    
    // TX FIFO signals
    logic [7:0] tx_fifo_data;
    logic tx_fifo_wr_en;
    logic tx_fifo_full;
    logic tx_fifo_empty;
    logic tx_fifo_rd_en;
    logic [7:0] tx_fifo_rd_data;
    logic [TX_FIFO_WIDTH-1:0] tx_fifo_count;
    
    // Frame parser signals
    logic [7:0] parser_cmd;
    logic [31:0] parser_addr;
    logic [7:0] parser_data_out [0:63];
    logic [5:0] parser_data_count;
    logic parser_frame_valid;
    logic [7:0] parser_error_status;
    logic parser_frame_error;
    logic parser_frame_consumed;
    logic parser_busy;
    
    // AXI master signals
    logic [7:0] axi_write_data [0:63];
    logic axi_start_transaction;
    logic axi_transaction_done;
    logic [7:0] axi_status;
    logic [7:0] axi_read_data [0:63];
    logic [5:0] axi_read_data_count;
    
    // Frame builder signals
    logic [7:0] builder_status_code;
    logic [7:0] builder_cmd_echo;
    logic [31:0] builder_addr_echo;
    logic [7:0] builder_response_data [0:63];
    logic [5:0] builder_response_data_count;
    logic builder_build_response;
    logic builder_is_read_response;
    logic builder_busy;
    logic builder_response_complete;
    
    // Main control state machine
    typedef enum logic [2:0] {
        MAIN_IDLE,
        MAIN_AXI_TRANSACTION,
        MAIN_BUILD_RESPONSE,
        MAIN_WAIT_RESPONSE
    } main_state_t;
    
    main_state_t main_state, main_state_next;
    
    // UART RX instance
    Uart_Rx #(
        .CLK_FREQ_HZ(CLK_FREQ_HZ),
        .BAUD_RATE(BAUD_RATE),
        .OVERSAMPLE(UART_OVERSAMPLE)
    ) uart_rx_inst (
        .clk(clk),
        .rst(rst),
        .uart_rx(uart_rx),
        .rx_data(rx_data),
        .rx_valid(rx_valid),
        .rx_error(rx_error),
        .rx_busy(rx_busy)
    );
    
    // UART TX instance
    Uart_Tx #(
        .CLK_FREQ_HZ(CLK_FREQ_HZ),
        .BAUD_RATE(BAUD_RATE)
    ) uart_tx_inst (
        .clk(clk),
        .rst(rst),
        .tx_data(tx_data),
        .tx_start(tx_start),
        .uart_tx(uart_tx),
        .tx_busy(tx_busy),
        .tx_done(tx_done)
    );
    
    // RX FIFO instance
    fifo_sync #(
        .DATA_WIDTH(8),
        .FIFO_DEPTH(RX_FIFO_DEPTH)
    ) rx_fifo (
        .clk(clk),
        .rst(rst),
        .wr_en(rx_fifo_wr_en),
        .wr_data(rx_data),
        .full(rx_fifo_full),
        .almost_full(),
        .rd_en(rx_fifo_rd_en),
        .rd_data(rx_fifo_rd_data),
        .empty(rx_fifo_empty),
        .almost_empty(),
        .count(rx_fifo_count)
    );
    
    // TX FIFO instance
    fifo_sync #(
        .DATA_WIDTH(8),
        .FIFO_DEPTH(TX_FIFO_DEPTH)
    ) tx_fifo (
        .clk(clk),
        .rst(rst),
        .wr_en(tx_fifo_wr_en),
        .wr_data(tx_fifo_data),
        .full(tx_fifo_full),
        .almost_full(),
        .rd_en(tx_fifo_rd_en),
        .rd_data(tx_fifo_rd_data),
        .empty(tx_fifo_empty),
        .almost_empty(),
        .count(tx_fifo_count)
    );
    
    // Frame parser instance
    Frame_Parser #(
        .CLK_FREQ_HZ(CLK_FREQ_HZ),
        .BAUD_RATE(BAUD_RATE),
        .TIMEOUT_BYTE_TIMES(10)
    ) frame_parser (
        .clk(clk),
        .rst(rst),
        .rx_fifo_data(rx_fifo_rd_data),
        .rx_fifo_empty(rx_fifo_empty),
        .rx_fifo_rd_en(rx_fifo_rd_en),
        .cmd(parser_cmd),
        .addr(parser_addr),
        .data_out(parser_data_out),
        .data_count(parser_data_count),
        .frame_valid(parser_frame_valid),
        .error_status(parser_error_status),
        .frame_error(parser_frame_error),
        .frame_consumed(parser_frame_consumed),
        .parser_busy(parser_busy)
    );
    
    // AXI4-Lite master instance
    Axi4_Lite_Master #(
        .AXI_TIMEOUT(AXI_TIMEOUT),
        .EARLY_BUSY_THRESHOLD(100)
    ) axi_master (
        .clk(clk),
        .rst(rst),
        .cmd(parser_cmd),
        .addr(parser_addr),
        .write_data(axi_write_data),
        .start_transaction(axi_start_transaction),
        .transaction_done(axi_transaction_done),
        .axi_status(axi_status),
        .read_data(axi_read_data),
        .read_data_count(axi_read_data_count),
        .axi(axi)
    );
    
    // Frame builder instance
    Frame_Builder frame_builder (
        .clk(clk),
        .rst(rst),
        .status_code(builder_status_code),
        .cmd_echo(builder_cmd_echo),
        .addr_echo(builder_addr_echo),
        .response_data(builder_response_data),
        .response_data_count(builder_response_data_count),
        .build_response(builder_build_response),
        .is_read_response(builder_is_read_response),
        .tx_fifo_data(tx_fifo_data),
        .tx_fifo_wr_en(tx_fifo_wr_en),
        .tx_fifo_full(tx_fifo_full),
        .builder_busy(builder_busy),
        .response_complete(builder_response_complete)
    );
    
    // RX FIFO write control
    assign rx_fifo_wr_en = rx_valid && !rx_error && !rx_fifo_full;
    
    // TX FIFO read control and UART TX feeding
    assign tx_fifo_rd_en = !tx_fifo_empty && !tx_busy;
    assign tx_data = tx_fifo_rd_data;
    assign tx_start = tx_fifo_rd_en;  // Start transmission when reading from FIFO
    
    // Copy parser data to AXI write data
    always_comb begin
        for (int i = 0; i < 64; i++) begin
            axi_write_data[i] = parser_data_out[i];
        end
    end
    
    // Main control state machine (sequential part)
    always_ff @(posedge clk) begin
        if (rst) begin
            main_state <= MAIN_IDLE;
        end else begin
            main_state <= main_state_next;
        end
    end
    
    // Main control state machine (combinational part)
    always_comb begin
        main_state_next = main_state;
        axi_start_transaction = 1'b0;
        parser_frame_consumed = 1'b0;
        builder_build_response = 1'b0;
        builder_is_read_response = 1'b0;
        builder_status_code = 8'h00;
        builder_cmd_echo = 8'h00;
        builder_addr_echo = 32'h00000000;
        builder_response_data_count = 6'h00;
        
        // Copy AXI read data to builder response data
        for (int i = 0; i < 64; i++) begin
            builder_response_data[i] = axi_read_data[i];
        end
        
        case (main_state)
            MAIN_IDLE: begin
                if (parser_frame_valid) begin
                    main_state_next = MAIN_AXI_TRANSACTION;
                end else if (parser_frame_error) begin
                    main_state_next = MAIN_BUILD_RESPONSE;
                end
            end
            
            MAIN_AXI_TRANSACTION: begin
                axi_start_transaction = 1'b1;
                if (axi_transaction_done) begin
                    main_state_next = MAIN_BUILD_RESPONSE;
                end
            end
            
            MAIN_BUILD_RESPONSE: begin
                builder_build_response = 1'b1;
                builder_cmd_echo = parser_cmd;
                builder_addr_echo = parser_addr;
                
                if (parser_frame_error) begin
                    // Error response
                    builder_status_code = parser_error_status;
                    builder_is_read_response = 1'b0;
                    builder_response_data_count = 6'h00;
                end else begin
                    // Normal response
                    builder_status_code = axi_status;
                    builder_is_read_response = parser_cmd[7];  // RW bit
                    
                    if (parser_cmd[7]) begin  // Read response
                        if (axi_status == 8'h00) begin  // Success
                            builder_response_data_count = axi_read_data_count;
                        end else begin  // Error
                            builder_response_data_count = 6'h00;
                        end
                    end else begin  // Write response
                        builder_response_data_count = 6'h00;
                    end
                end
                
                main_state_next = MAIN_WAIT_RESPONSE;
            end
            
            MAIN_WAIT_RESPONSE: begin
                if (builder_response_complete) begin
                    parser_frame_consumed = 1'b1;
                    main_state_next = MAIN_IDLE;
                end
            end
        endcase
    end

    // Assertions for verification
    `ifdef ENABLE_BRIDGE_ASSERTIONS
        // UART RX data should not be lost due to FIFO overflow
        assert_no_rx_data_loss: assert property (
            @(posedge clk) disable iff (rst)
            rx_valid && !rx_error |-> !rx_fifo_full
        ) else $warning("UART_Bridge: RX data lost due to FIFO overflow");

        // Frame parser should eventually become non-busy
        assert_parser_eventually_idle: assert property (
            @(posedge clk) disable iff (rst)
            parser_busy |-> ##[1:10000] !parser_busy
        ) else $error("UART_Bridge: Parser stuck in busy state");

        // AXI transaction should eventually complete
        assert_axi_eventually_done: assert property (
            @(posedge clk) disable iff (rst)
            axi_start_transaction |-> ##[1:5000] axi_transaction_done
        ) else $error("UART_Bridge: AXI transaction never completes");
    `endif

    // Statistics counters
    logic [15:0] tx_count_reg;
    logic [15:0] rx_count_reg;
    
    // Transaction completion detection
    logic tx_transaction_complete;
    logic rx_transaction_complete;
    
    assign tx_transaction_complete = builder_response_complete && !parser_cmd[7]; // Write transaction
    assign rx_transaction_complete = builder_response_complete && parser_cmd[7];  // Read transaction
    
    // Statistics counter logic
    always_ff @(posedge clk) begin
        if (rst || reset_statistics) begin
            tx_count_reg <= 16'h0000;
            rx_count_reg <= 16'h0000;
        end else begin
            if (tx_transaction_complete) begin
                tx_count_reg <= tx_count_reg + 1'b1;
            end
            if (rx_transaction_complete) begin
                rx_count_reg <= rx_count_reg + 1'b1;
            end
        end
    end
    
    // Status monitoring logic
    always_comb begin
        // Bridge busy status - active when processing any transaction
        bridge_busy = parser_busy || (main_state != MAIN_IDLE) || tx_busy || rx_busy;
        
        // Error code reporting - prioritized error status
        if (parser_frame_error) begin
            bridge_error_code = parser_error_status;
        end else if (axi_status != 8'h00) begin
            bridge_error_code = axi_status;
        end else if (rx_error) begin
            bridge_error_code = 8'h01; // UART RX error
        end else begin
            bridge_error_code = 8'h00; // No error
        end
        
        // FIFO status flags
        fifo_status_flags[0] = rx_fifo_full;
        fifo_status_flags[1] = rx_fifo_empty;
        fifo_status_flags[2] = tx_fifo_full;
        fifo_status_flags[3] = tx_fifo_empty;
        fifo_status_flags[7:4] = rx_fifo_count[3:0]; // RX FIFO level (lower 4 bits)
    end
    
    // Output assignments
    assign tx_transaction_count = tx_count_reg;
    assign rx_transaction_count = rx_count_reg;

endmodule