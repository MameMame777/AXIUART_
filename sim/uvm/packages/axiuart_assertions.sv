`timescale 1ns / 1ps

// Comprehensive SystemVerilog Assertions for AXIUART protocol compliance
// Implements 8 critical assertion categories for coverage improvement

module axiuart_assertions (
    input logic clk,
    input logic reset,
    
    // AXI4-Lite interface signals
    input logic        axi_awvalid,
    input logic        axi_awready,
    input logic [31:0] axi_awaddr,
    input logic [2:0]  axi_awprot,
    
    input logic        axi_wvalid,
    input logic        axi_wready,
    input logic [31:0] axi_wdata,
    input logic [3:0]  axi_wstrb,
    
    input logic        axi_bvalid,
    input logic        axi_bready,
    input logic [1:0]  axi_bresp,
    
    input logic        axi_arvalid,
    input logic        axi_arready,
    input logic [31:0] axi_araddr,
    input logic [2:0]  axi_arprot,
    
    input logic        axi_rvalid,
    input logic        axi_rready,
    input logic [31:0] axi_rdata,
    input logic [1:0]  axi_rresp,
    
    // UART interface signals
    input logic uart_rx,
    input logic uart_tx,
    input logic uart_tx_busy,
    input logic uart_rx_valid,
    input logic uart_parity_error,
    input logic uart_frame_error,
    
    // CRC calculation signals
    input logic crc_enable,
    input logic crc_calc_valid,
    input logic crc_calc_start,
    input logic crc_match,
    input logic [7:0] crc_result,
    
    // FIFO status signals
    input logic rx_fifo_full,
    input logic rx_fifo_empty,
    input logic rx_fifo_wr_en,
    input logic rx_fifo_rd_en,
    input logic [6:0] rx_fifo_count,
    
    input logic tx_fifo_full,
    input logic tx_fifo_empty,
    input logic tx_fifo_wr_en,
    input logic tx_fifo_rd_en,
    input logic [6:0] tx_fifo_count,
    
    // State machine signals
    input logic [2:0] frame_parser_state,
    input logic [2:0] axi_master_state,
    
    // Address alignment signals
    input logic addr_alignment_active,
    input logic [31:0] aligned_addr,
    input logic alignment_correction
);

    // Local parameters for states and constants
    localparam [2:0] PARSER_IDLE    = 3'b000,
                     PARSER_HEADER  = 3'b001,
                     PARSER_LENGTH  = 3'b010,
                     PARSER_PAYLOAD = 3'b011,
                     PARSER_CRC     = 3'b100,
                     PARSER_ERROR   = 3'b101;
                     
    localparam [2:0] AXI_IDLE      = 3'b000,
                     AXI_ADDR      = 3'b001,
                     AXI_DATA      = 3'b010,
                     AXI_RESP      = 3'b011,
                     AXI_ERROR     = 3'b100;

    //==========================================================================
    // SVA-1: AXI4-Lite Protocol Compliance Assertions
    //==========================================================================
    
    // Write address handshake timing
    property p_axi_aw_handshake;
        @(posedge clk) disable iff (reset)
        axi_awvalid && !axi_awready |-> ##[1:16] axi_awready;
    endproperty
    
    assert_axi_aw_handshake: assert property (p_axi_aw_handshake)
    else `uvm_error("AXIUART_ASSERT", "AXI WRITE ADDRESS HANDSHAKE VIOLATION - AWREADY not asserted within 16 cycles")
    
    cover_axi_aw_handshake: cover property (p_axi_aw_handshake);
    
    // Write data handshake must complete before response
    property p_axi_w_before_b;
        @(posedge clk) disable iff (reset)
        axi_wvalid && axi_wready |-> ##[0:$] (axi_bvalid && axi_bready);
    endproperty
    
    assert_axi_w_before_b: assert property (p_axi_w_before_b)
    else `uvm_error("AXIUART_ASSERT", "AXI WRITE DATA/RESPONSE SEQUENCING VIOLATION")
    
    // Read address handshake timing
    property p_axi_ar_handshake;
        @(posedge clk) disable iff (reset)
        axi_arvalid && !axi_arready |-> ##[1:16] axi_arready;
    endproperty
    
    assert_axi_ar_handshake: assert property (p_axi_ar_handshake)
    else `uvm_error("AXIUART_ASSERT", "AXI READ ADDRESS HANDSHAKE VIOLATION - ARREADY not asserted within 16 cycles")
    
    // AXI address alignment check
    property p_axi_addr_aligned;
        @(posedge clk) disable iff (reset)
        (axi_awvalid |-> (axi_awaddr[1:0] == 2'b00)) and
        (axi_arvalid |-> (axi_araddr[1:0] == 2'b00));
    endproperty
    
    assert_axi_addr_aligned: assert property (p_axi_addr_aligned)
    else `uvm_error("AXIUART_ASSERT", "AXI ADDRESS ALIGNMENT VIOLATION - Address must be 32-bit aligned")
    
    //==========================================================================
    // SVA-2: UART Timing Constraints
    //==========================================================================
    
    // UART start bit stability (assuming 8 clock cycles per bit minimum)
    sequence s_uart_start_bit;
        @(posedge clk) $fell(uart_rx) ##0 (!uart_rx)[*8];
    endsequence
    
    property p_uart_start_bit_stable;
        @(posedge clk) disable iff (reset)
        $fell(uart_rx) |-> s_uart_start_bit;
    endproperty
    
    assert_uart_start_bit: assert property (p_uart_start_bit_stable)
    else `uvm_error("AXIUART_ASSERT", "UART START BIT TIMING VIOLATION - Start bit not stable for minimum duration")
    
    cover_uart_start_bit: cover property (p_uart_start_bit_stable);
    
    // UART transmission busy consistency
    property p_uart_tx_busy_consistent;
        @(posedge clk) disable iff (reset)
        uart_tx_busy |-> ##[1:$] !uart_tx_busy;
    endproperty
    
    assert_uart_tx_busy: assert property (p_uart_tx_busy_consistent)
    else `uvm_error("AXIUART_ASSERT", "UART TX BUSY SIGNAL STUCK - Transmission never completes")
    
    // Parity error should not persist
    property p_parity_error_transient;
        @(posedge clk) disable iff (reset)
        uart_parity_error |-> ##[1:5] !uart_parity_error;
    endproperty
    
    assert_parity_error_transient: assert property (p_parity_error_transient)
    else `uvm_error("AXIUART_ASSERT", "UART PARITY ERROR PERSISTENT - Error flag should be transient")
    
    //==========================================================================
    // SVA-3: CRC Calculation Boundary Assertions
    //==========================================================================
    
    // CRC enable should not change during active calculation
    property p_crc_enable_stable;
        @(posedge clk) disable iff (reset)
        crc_calc_start && crc_enable |-> (crc_enable throughout (crc_calc_start ##[1:$] crc_calc_valid));
    endproperty
    
    assert_crc_enable_stable: assert property (p_crc_enable_stable)
    else `uvm_error("AXIUART_ASSERT", "CRC ENABLE CHANGE DURING CALCULATION - Enable signal changed mid-calculation")
    
    cover_crc_enable_stable: cover property (p_crc_enable_stable);
    
    // CRC calculation latency bound (4 cycles maximum)
    property p_crc_calc_latency;
        @(posedge clk) disable iff (reset)
        crc_calc_start && crc_enable |-> ##[1:4] crc_calc_valid;
    endproperty
    
    assert_crc_calc_latency: assert property (p_crc_calc_latency)
    else `uvm_error("AXIUART_ASSERT", "CRC CALCULATION LATENCY VIOLATION - Calculation exceeds 4 cycles")
    
    // CRC result stability
    property p_crc_result_stable;
        @(posedge clk) disable iff (reset)
        crc_calc_valid |-> (crc_result == $past(crc_result)) throughout (crc_calc_valid ##1 !crc_calc_valid);
    endproperty
    
    assert_crc_result_stable: assert property (p_crc_result_stable)
    else `uvm_error("AXIUART_ASSERT", "CRC RESULT INSTABILITY - CRC result changed while valid")
    
    //==========================================================================
    // SVA-4: FIFO Overflow/Underflow Protection
    //==========================================================================
    
    // RX FIFO write protection when full
    property p_rx_fifo_overflow_protection;
        @(posedge clk) disable iff (reset)
        rx_fifo_full |-> !rx_fifo_wr_en;
    endproperty
    
    assert_rx_fifo_no_overflow: assert property (p_rx_fifo_overflow_protection)
    else `uvm_error("AXIUART_ASSERT", "RX FIFO OVERFLOW - Write attempted when FIFO full")
    
    cover_rx_fifo_full_condition: cover property (@(posedge clk) disable iff (reset) rx_fifo_full);
    
    // TX FIFO read protection when empty
    property p_tx_fifo_underflow_protection;
        @(posedge clk) disable iff (reset)
        tx_fifo_empty |-> !tx_fifo_rd_en;
    endproperty
    
    assert_tx_fifo_no_underflow: assert property (p_tx_fifo_underflow_protection)
    else `uvm_error("AXIUART_ASSERT", "TX FIFO UNDERFLOW - Read attempted when FIFO empty")
    
    // FIFO count integrity (never exceeds maximum depth)
    property p_fifo_count_bounds;
        @(posedge clk) disable iff (reset)
        (rx_fifo_count <= 7'd63) && (tx_fifo_count <= 7'd63);
    endproperty
    
    assert_fifo_count_bounds: assert property (p_fifo_count_bounds)
    else `uvm_error("AXIUART_ASSERT", "FIFO COUNT OVERFLOW - Count exceeds maximum depth (63)")
    
    // FIFO count consistency with flags
    property p_fifo_flags_consistent;
        @(posedge clk) disable iff (reset)
        (rx_fifo_empty <-> (rx_fifo_count == 7'd0)) &&
        (rx_fifo_full <-> (rx_fifo_count == 7'd63)) &&
        (tx_fifo_empty <-> (tx_fifo_count == 7'd0)) &&
        (tx_fifo_full <-> (tx_fifo_count == 7'd63));
    endproperty
    
    assert_fifo_flags_consistent: assert property (p_fifo_flags_consistent)
    else `uvm_error("AXIUART_ASSERT", "FIFO FLAG INCONSISTENCY - Flags do not match count values")
    
    //==========================================================================
    // SVA-5: Reset During Transfer Protection
    //==========================================================================
    
    // Reset should clear AXI transaction state
    property p_reset_clears_axi_state;
        @(posedge clk)
        reset |=> (axi_master_state == AXI_IDLE);
    endproperty
    
    assert_reset_axi_state: assert property (p_reset_clears_axi_state)
    else `uvm_error("AXIUART_ASSERT", "RESET STATE VIOLATION - AXI state not cleared on reset")
    
    // Reset should clear frame parser state
    property p_reset_clears_parser_state;
        @(posedge clk)
        reset |=> (frame_parser_state == PARSER_IDLE);
    endproperty
    
    assert_reset_parser_state: assert property (p_reset_clears_parser_state)
    else `uvm_error("AXIUART_ASSERT", "RESET STATE VIOLATION - Parser state not cleared on reset")
    
    // Reset recovery timing (8 cycles maximum)
    property p_reset_recovery_timing;
        @(posedge clk)
        $fell(reset) |-> ##[1:8] (frame_parser_state == PARSER_IDLE) && (axi_master_state == AXI_IDLE);
    endproperty
    
    assert_reset_recovery: assert property (p_reset_recovery_timing)
    else `uvm_error("AXIUART_ASSERT", "RESET RECOVERY VIOLATION - System not ready within 8 cycles")
    
    //==========================================================================
    // SVA-6: Address Alignment Correction
    //==========================================================================
    
    // Misaligned address should trigger correction
    property p_misalignment_triggers_correction;
        @(posedge clk) disable iff (reset)
        (axi_awvalid && (axi_awaddr[1:0] != 2'b00)) || (axi_arvalid && (axi_araddr[1:0] != 2'b00))
        |-> addr_alignment_active;
    endproperty
    
    assert_alignment_correction_trigger: assert property (p_misalignment_triggers_correction)
    else `uvm_error("AXIUART_ASSERT", "ADDRESS ALIGNMENT CORRECTION NOT TRIGGERED")
    
    cover_alignment_correction: cover property (p_misalignment_triggers_correction);
    
    // Address alignment preserves upper bits
    property p_alignment_preserves_upper_bits;
        @(posedge clk) disable iff (reset)
        alignment_correction |-> (aligned_addr[31:2] == $past(axi_awvalid ? axi_awaddr[31:2] : axi_araddr[31:2]));
    endproperty
    
    assert_alignment_preserves_bits: assert property (p_alignment_preserves_upper_bits)
    else `uvm_error("AXIUART_ASSERT", "ADDRESS ALIGNMENT CORRUPTION - Upper address bits changed")
    
    // Aligned output should be word-boundary aligned
    property p_aligned_output_word_boundary;
        @(posedge clk) disable iff (reset)
        alignment_correction |-> (aligned_addr[1:0] == 2'b00);
    endproperty
    
    assert_word_boundary_alignment: assert property (p_aligned_output_word_boundary)
    else `uvm_error("AXIUART_ASSERT", "ADDRESS ALIGNMENT FAILURE - Output not word-aligned")
    
    //==========================================================================
    // SVA-7: Frame Parser State Integrity
    //==========================================================================
    
    // Valid state transitions only
    property p_parser_valid_transitions;
        @(posedge clk) disable iff (reset)
        (frame_parser_state == PARSER_IDLE) |-> ##1 (frame_parser_state inside {PARSER_IDLE, PARSER_HEADER, PARSER_ERROR}) ||
        (frame_parser_state == PARSER_HEADER) |-> ##1 (frame_parser_state inside {PARSER_LENGTH, PARSER_ERROR}) ||
        (frame_parser_state == PARSER_LENGTH) |-> ##1 (frame_parser_state inside {PARSER_PAYLOAD, PARSER_ERROR}) ||
        (frame_parser_state == PARSER_PAYLOAD) |-> ##1 (frame_parser_state inside {PARSER_CRC, PARSER_IDLE, PARSER_ERROR}) ||
        (frame_parser_state == PARSER_CRC) |-> ##1 (frame_parser_state inside {PARSER_IDLE, PARSER_ERROR}) ||
        (frame_parser_state == PARSER_ERROR) |-> ##1 (frame_parser_state inside {PARSER_IDLE, PARSER_ERROR});
    endproperty
    
    assert_parser_valid_transitions: assert property (p_parser_valid_transitions)
    else `uvm_error("AXIUART_ASSERT", "FRAME PARSER INVALID STATE TRANSITION")
    
    // Error state entry clears processing
    property p_error_state_clears_processing;
        @(posedge clk) disable iff (reset)
        (frame_parser_state != PARSER_ERROR) ##1 (frame_parser_state == PARSER_ERROR)
        |-> ##[1:10] (frame_parser_state == PARSER_IDLE);
    endproperty
    
    assert_error_recovery: assert property (p_error_state_clears_processing)
    else `uvm_error("AXIUART_ASSERT", "FRAME PARSER ERROR RECOVERY FAILURE")
    
    // Timeout recovery
    property p_parser_timeout_recovery;
        @(posedge clk) disable iff (reset)
        (frame_parser_state != PARSER_IDLE) |-> ##[1:1000] (frame_parser_state == PARSER_IDLE);
    endproperty
    
    assert_parser_timeout: assert property (p_parser_timeout_recovery)
    else `uvm_error("AXIUART_ASSERT", "FRAME PARSER TIMEOUT - State machine stuck")
    
    //==========================================================================
    // SVA-8: Cross-Clock Domain Safety (if applicable)
    //==========================================================================
    
    // Stable control signals (no glitches on critical paths)
    property p_control_signal_stability;
        @(posedge clk) disable iff (reset)
        $stable(crc_enable) && $stable(uart_tx_busy);
    endproperty
    
    assert_control_stability: assert property (p_control_signal_stability)
    else `uvm_error("AXIUART_ASSERT", "CONTROL SIGNAL INSTABILITY - Critical signals are glitching")
    
    //==========================================================================
    // Coverage Properties for Functional Coverage Integration  
    //==========================================================================
    
    // Cover important scenarios for functional coverage
    cover_axi_write_sequence: cover property (
        @(posedge clk) disable iff (reset)
        axi_awvalid ##1 axi_awready ##[0:2] axi_wvalid ##1 axi_wready ##[1:5] axi_bvalid ##1 axi_bready
    );
    
    cover_axi_read_sequence: cover property (
        @(posedge clk) disable iff (reset)
        axi_arvalid ##1 axi_arready ##[1:10] axi_rvalid ##1 axi_rready
    );
    
    cover_uart_error_conditions: cover property (
        @(posedge clk) disable iff (reset)
        uart_parity_error || uart_frame_error
    );
    
    cover_crc_mismatch: cover property (
        @(posedge clk) disable iff (reset)
        crc_calc_valid && !crc_match
    );
    
    cover_fifo_boundary_conditions: cover property (
        @(posedge clk) disable iff (reset)
        rx_fifo_full || tx_fifo_full || rx_fifo_empty || tx_fifo_empty
    );
    
    cover_state_machine_transitions: cover property (
        @(posedge clk) disable iff (reset)
        $changed(frame_parser_state) || $changed(axi_master_state)
    );
    
    cover_alignment_scenarios: cover property (
        @(posedge clk) disable iff (reset)
        addr_alignment_active && alignment_correction
    );

endmodule

// Bind statement to connect assertions to DUT
bind AXIUART_Top axiuart_assertions axiuart_assert_inst (
    .clk                    (clk),
    .reset                  (reset),
    
    // AXI4-Lite connections
    .axi_awvalid           (axi_internal.awvalid),
    .axi_awready           (axi_internal.awready),
    .axi_awaddr            (axi_internal.awaddr),
    .axi_awprot            (axi_internal.awprot),
    
    .axi_wvalid            (axi_internal.wvalid),
    .axi_wready            (axi_internal.wready),
    .axi_wdata             (axi_internal.wdata),
    .axi_wstrb             (axi_internal.wstrb),
    
    .axi_bvalid            (axi_internal.bvalid),
    .axi_bready            (axi_internal.bready),
    .axi_bresp             (axi_internal.bresp),
    
    .axi_arvalid           (axi_internal.arvalid),
    .axi_arready           (axi_internal.arready),
    .axi_araddr            (axi_internal.araddr),
    .axi_arprot            (axi_internal.arprot),
    
    .axi_rvalid            (axi_internal.rvalid),
    .axi_rready            (axi_internal.rready),
    .axi_rdata             (axi_internal.rdata),
    .axi_rresp             (axi_internal.rresp),
    
    // UART connections
    .uart_rx               (uart_rx),
    .uart_tx               (uart_tx),
    .uart_tx_busy          (uart_bridge_inst.uart_tx_inst.tx_busy),
    .uart_rx_valid         (uart_bridge_inst.uart_rx_inst.rx_valid),
    .uart_parity_error     (uart_bridge_inst.uart_rx_inst.parity_error),
    .uart_frame_error      (uart_bridge_inst.uart_rx_inst.frame_error),
    
    // CRC connections
    .crc_enable            (uart_bridge_inst.frame_parser.crc_enable),
    .crc_calc_valid        (uart_bridge_inst.frame_parser.crc_calc.valid),
    .crc_calc_start        (uart_bridge_inst.frame_parser.crc_calc.start),
    .crc_match             (uart_bridge_inst.frame_parser.crc_match),
    .crc_result            (uart_bridge_inst.frame_parser.crc_calc.result),
    
    // FIFO connections
    .rx_fifo_full          (uart_bridge_inst.rx_fifo.full),
    .rx_fifo_empty         (uart_bridge_inst.rx_fifo.empty),
    .rx_fifo_wr_en         (uart_bridge_inst.rx_fifo.wr_en),
    .rx_fifo_rd_en         (uart_bridge_inst.rx_fifo.rd_en),
    .rx_fifo_count         (uart_bridge_inst.rx_fifo.count),
    
    .tx_fifo_full          (uart_bridge_inst.tx_fifo.full),
    .tx_fifo_empty         (uart_bridge_inst.tx_fifo.empty),
    .tx_fifo_wr_en         (uart_bridge_inst.tx_fifo.wr_en),
    .tx_fifo_rd_en         (uart_bridge_inst.tx_fifo.rd_en),
    .tx_fifo_count         (uart_bridge_inst.tx_fifo.count),
    
    // State machine connections
    .frame_parser_state    (uart_bridge_inst.frame_parser.current_state),
    .axi_master_state      (uart_bridge_inst.axi_master.current_state),
    
    // Address alignment connections (if present)
    .addr_alignment_active (1'b0), // Connect to actual signal if available
    .aligned_addr          (32'h0), // Connect to actual signal if available
    .alignment_correction  (1'b0)   // Connect to actual signal if available
);