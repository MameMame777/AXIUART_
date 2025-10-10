`timescale 1ns / 1ps

// FIXED AXI4-Lite Register Block for AXIUART System
// Corrected ready signal logic to avoid circular dependencies
module Register_Block #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter int BASE_ADDR = 32'h0000_1000
)(
    input  logic clk,
    input  logic rst,
    
    // AXI4-Lite slave interface
    axi4_lite_if.slave axi,
    
    // Register interface to UART bridge
    output logic        bridge_reset_stats,    // Pulse to reset statistics counters
    output logic [7:0]  baud_div_config,       // UART baud rate divider configuration
    output logic [7:0]  timeout_config,        // AXI timeout configuration
    output logic [3:0]  debug_mode,            // Debug mode selection
    
    // Status inputs from UART bridge
    input  logic        bridge_busy,           // Bridge is processing transaction
    input  logic [7:0]  error_code,            // Current error code
    input  logic [15:0] tx_count,              // TX transaction counter
    input  logic [15:0] rx_count,              // RX transaction counter
    input  logic [7:0]  fifo_status            // FIFO status flags
);

    // Register address map (byte addresses)
    localparam bit [11:0] REG_CONTROL    = 12'h000;  // 0x000: Control register
    localparam bit [11:0] REG_STATUS     = 12'h004;  // 0x004: Status register
    localparam bit [11:0] REG_CONFIG     = 12'h008;  // 0x008: Configuration register
    localparam bit [11:0] REG_DEBUG      = 12'h00C;  // 0x00C: Debug control
    localparam bit [11:0] REG_TX_COUNT   = 12'h010;  // 0x010: TX counter (RO)
    localparam bit [11:0] REG_RX_COUNT   = 12'h014;  // 0x014: RX counter (RO)
    localparam bit [11:0] REG_FIFO_STAT  = 12'h018;  // 0x018: FIFO status (RO)
    localparam bit [11:0] REG_VERSION    = 12'h01C;  // 0x01C: Version register (RO)
    
    // Test registers for protocol debugging (added 2025-10-05)
    // Extended test set for pattern analysis (2025-10-09)
    localparam bit [11:0] REG_TEST_0     = 12'h020;  // 0x020: Test register 0 (RW)
    localparam bit [11:0] REG_TEST_1     = 12'h024;  // 0x024: Test register 1 (RW)
    localparam bit [11:0] REG_TEST_2     = 12'h028;  // 0x028: Test register 2 (RW)
    localparam bit [11:0] REG_TEST_3     = 12'h02C;  // 0x02C: Test register 3 (RW)
    localparam bit [11:0] REG_TEST_4     = 12'h040;  // 0x040: Test register 4 (RW) - gap test
    localparam bit [11:0] REG_TEST_5     = 12'h050;  // 0x050: Test register 5 (RW) - larger gap
    localparam bit [11:0] REG_TEST_6     = 12'h080;  // 0x080: Test register 6 (RW) - even larger gap
    localparam bit [11:0] REG_TEST_7     = 12'h100;  // 0x100: Test register 7 (RW) - different range

    // Register storage
    logic [31:0] control_reg;      // RW - Control register
    logic [31:0] config_reg;       // RW - Configuration register  
    logic [31:0] debug_reg;        // RW - Debug register
    
    // Test registers for protocol debugging (added 2025-10-05)
    // Extended test set for pattern analysis (2025-10-09)
    logic [31:0] test_reg_0;       // RW - Test register 0 (pure read/write test)
    logic [31:0] test_reg_1;       // RW - Test register 1 (pattern test)
    logic [31:0] test_reg_2;       // RW - Test register 2 (increment test)
    logic [31:0] test_reg_3;       // RW - Test register 3 (mirror test)
    logic [31:0] test_reg_4;       // RW - Test register 4 (gap test)
    logic [31:0] test_reg_5;       // RW - Test register 5 (larger gap)
    logic [31:0] test_reg_6;       // RW - Test register 6 (even larger gap)
    logic [31:0] test_reg_7;       // RW - Test register 7 (different range)
    
    // AXI4-Lite response codes
    localparam bit [1:0] RESP_OKAY   = 2'b00;
    localparam bit [1:0] RESP_SLVERR = 2'b10;
    
    // Internal signals
    logic [11:0] addr_offset;
    logic [31:0] read_data;
    logic [1:0]  read_resp;
    logic [1:0]  write_resp;
    logic [31:0] write_addr_reg;   // CRITICAL: Write address tracking
    logic [31:0] read_addr_reg;
    logic [31:0] active_addr;
    
    // AXI4-Lite control signals - defined before state machine
    wire aw_handshake = axi.awvalid && axi.awready;
    wire w_handshake = axi.wvalid && axi.wready;
    wire ar_handshake = axi.arvalid && axi.arready;
    
    // Address decoding logic added after state machine declaration
    
    // AXI4-Lite state machine - CORRECTED
    typedef enum logic [2:0] {
        IDLE,
        WRITE_ADDR,
        WRITE_DATA, 
        WRITE_RESP,
        READ_DATA
    } axi_state_t;
    
    axi_state_t axi_state, axi_next_state;
    
    // State machine sequential logic
    always_ff @(posedge clk) begin
        if (rst) begin
            axi_state <= IDLE;
        end else begin
            axi_state <= axi_next_state;
        end
    end
    
    // State machine combinational logic - CORRECTED
    always_comb begin
        axi_next_state = axi_state;
        
        case (axi_state)
            IDLE: begin
                if (axi.awvalid) begin
                    if (aw_handshake) begin
                        axi_next_state = WRITE_DATA;
                    end else begin
                        axi_next_state = WRITE_ADDR;
                    end
                end else if (axi.arvalid) begin
                    axi_next_state = READ_DATA;
                end
            end
            
            WRITE_ADDR: begin
                if (aw_handshake) begin
                    axi_next_state = WRITE_DATA;
                end
            end
            
            WRITE_DATA: begin
                if (w_handshake) begin
                    axi_next_state = WRITE_RESP;
                end
            end
            
            WRITE_RESP: begin
                if (axi.bready) begin
                    axi_next_state = IDLE;
                end
            end
            
            READ_DATA: begin
                if (axi.rready) begin
                    axi_next_state = IDLE;
                end
            end
            
            default: axi_next_state = IDLE;
        endcase
    end
    
    // Address decoding based on current transaction
    always_comb begin
        case (axi_state)
            READ_DATA: active_addr = read_addr_reg;
            default:   active_addr = write_addr_reg;
        endcase
    end

    assign addr_offset = active_addr[11:0];

    // Helper function to validate supported WSTRB patterns and alignment
    function automatic bit is_wstrb_supported(logic [1:0] addr_lsb, logic [3:0] wstrb);
        case (wstrb)
            4'b0001: return (addr_lsb == 2'b00);            // Byte lane 0 only
            4'b0011: return (addr_lsb == 2'b00);            // Lower halfword
            4'b1100: return (addr_lsb == 2'b10);            // Upper halfword
            4'b1111: return (addr_lsb == 2'b00);            // Full word
            default: return 1'b0;                           // Unsupported pattern
        endcase
    endfunction

    function automatic logic [31:0] apply_wstrb_mask(logic [31:0] current,
                                                     logic [31:0] wdata,
                                                     logic [3:0] wstrb);
        logic [31:0] mask;
        mask = '0;
        for (int i = 0; i < 4; i++) begin
            if (wstrb[i]) begin
                mask[8*i +: 8] = 8'hFF;
            end
        end
        return (current & ~mask) | (wdata & mask);
    endfunction

    function automatic bit is_write_access_valid(logic [11:0] offset,
                                                 logic [3:0] wstrb);
        logic [11:0] aligned_offset;
        bit within_register_range;
        aligned_offset = {offset[11:2], 2'b00};
        
        // Check if aligned offset matches any valid register
        case (aligned_offset)
            REG_CONTROL, REG_STATUS, REG_CONFIG, REG_DEBUG,
            REG_TX_COUNT, REG_RX_COUNT, REG_FIFO_STAT, REG_VERSION,
            REG_TEST_0, REG_TEST_1, REG_TEST_2, REG_TEST_3,
            REG_TEST_4, REG_TEST_5, REG_TEST_6, REG_TEST_7: begin
                within_register_range = 1'b1;
            end
            default: begin
                within_register_range = 1'b0;
            end
        endcase
        
        if (!within_register_range) begin
            return 1'b0;
        end
        
        // Ensure access doesn't exceed the 4-byte register boundary
        if (offset > (aligned_offset + 12'd3)) begin
            return 1'b0;
        end
        
        return is_wstrb_supported(offset[1:0], wstrb);
    endfunction

    function automatic bit is_read_access_valid(logic [11:0] offset);
        logic [11:0] aligned_offset;
        aligned_offset = {offset[11:2], 2'b00};
        
        // Check if aligned offset matches any valid register
        case (aligned_offset)
            REG_CONTROL, REG_STATUS, REG_CONFIG, REG_DEBUG,
            REG_TX_COUNT, REG_RX_COUNT, REG_FIFO_STAT, REG_VERSION,
            REG_TEST_0, REG_TEST_1, REG_TEST_2, REG_TEST_3,
            REG_TEST_4, REG_TEST_5, REG_TEST_6, REG_TEST_7: begin
                // Valid register found
            end
            default: begin
                return 1'b0;  // Invalid register address
            end
        endcase
        
        // Ensure access doesn't exceed the 4-byte register boundary
        if (offset > (aligned_offset + 12'd3)) begin
            return 1'b0;
        end
        
        // AXI4-Lite requires word-aligned reads for simplicity
        return (offset[1:0] == 2'b00);
    endfunction

    // Control signals derived from handshake
    wire write_enable = (axi_state == WRITE_DATA) && w_handshake;
    wire read_enable = (axi_state == READ_DATA);
    
    // Core AXI debug signals 
    wire axi_awvalid_debug = axi.awvalid;               // CRITICAL: Master awvalid reaches slave
    wire axi_wvalid_debug = axi.wvalid;                 // CRITICAL: Master wvalid reaches slave
    
    // AXI4-Lite data and address debug
    wire [31:0] axi_awaddr_debug = axi.awaddr;          // CRITICAL: Write address
    wire [31:0] axi_wdata_debug = axi.wdata;            // CRITICAL: Write data
    wire [3:0] axi_wstrb_debug = axi.wstrb;
    
    // Special trigger signals for ILA
    wire reg_test_write_trigger = write_enable && 
                               ((write_addr_reg[11:0] >= 12'h020) && (write_addr_reg[11:0] <= 12'h02C));  // CRITICAL: REG_TEST write trigger
    
    // AXI4-Lite ready signals - FIXED: No circular dependencies
    assign axi.awready = (axi_state == IDLE) || (axi_state == WRITE_ADDR);
    assign axi.wready = (axi_state == WRITE_DATA);
    assign axi.arready = (axi_state == IDLE);
    
    // Write response channel
    wire axi_bvalid_debug = axi.bvalid;
    wire axi_bready_debug = axi.bready;
    wire [1:0] axi_bresp_debug = axi.bresp;
    assign axi.bvalid = (axi_state == WRITE_RESP);
    assign axi.bresp = write_resp;
    
    // Read response channel
    assign axi.rvalid = (axi_state == READ_DATA);
    assign axi.rdata = read_data;
    assign axi.rresp = read_resp;
    
    // Register write logic
    logic reset_stats_pulse;
    
    // Test register write detection signals - Extended (2025-10-09)
    logic test_reg_0_write_detect;
    logic test_reg_1_write_detect;
    logic test_reg_2_write_detect;
    logic test_reg_3_write_detect;
    logic test_reg_4_write_detect;
    logic test_reg_5_write_detect;
    logic test_reg_6_write_detect;
    logic test_reg_7_write_detect;

    always_ff @(posedge clk) begin
        if (rst) begin
            control_reg <= 32'h0000_0000;  // Default control register value
            config_reg <= 32'h0000_0000;
            debug_reg <= 32'h0000_0000;
            
            // Test register initialization - SAFE INITIAL VALUES (not test patterns)
            test_reg_0 <= 32'h00000000;    // Zero initial value
            test_reg_1 <= 32'h00000000;    // Zero initial value  
            test_reg_2 <= 32'h00000000;    // Zero initial value
            test_reg_3 <= 32'h00000000;    // Zero initial value
            test_reg_4 <= 32'h00000000;    // Zero initial value
            test_reg_5 <= 32'h00000000;    // Zero initial value
            test_reg_6 <= 32'h00000000;    // Zero initial value
            test_reg_7 <= 32'h00000000;    // Zero initial value
            
            // Test register write detection initialization - Extended
            test_reg_0_write_detect <= 1'b0;
            test_reg_1_write_detect <= 1'b0;
            test_reg_2_write_detect <= 1'b0;
            test_reg_3_write_detect <= 1'b0;
            test_reg_4_write_detect <= 1'b0;
            test_reg_5_write_detect <= 1'b0;
            test_reg_6_write_detect <= 1'b0;
            test_reg_7_write_detect <= 1'b0;
            
            write_resp <= RESP_OKAY;
            write_addr_reg <= BASE_ADDR;
            read_addr_reg <= BASE_ADDR;
            reset_stats_pulse <= 1'b0;
        end else begin
            reset_stats_pulse <= 1'b0;
            
            // Clear test register write detection flags
            test_reg_0_write_detect <= 1'b0;
            test_reg_1_write_detect <= 1'b0;
            test_reg_2_write_detect <= 1'b0;
            test_reg_3_write_detect <= 1'b0;
            test_reg_4_write_detect <= 1'b0;
            test_reg_5_write_detect <= 1'b0;
            test_reg_6_write_detect <= 1'b0;
            test_reg_7_write_detect <= 1'b0;

            if (aw_handshake) begin
                write_addr_reg <= axi.awaddr;
                write_resp <= RESP_OKAY;
            end

            if (ar_handshake) begin
                read_addr_reg <= axi.araddr;
            end

            if (write_enable) begin
                logic [11:0] write_offset;
                logic [11:0] aligned_offset;
                bit write_ok;
                logic [31:0] masked_value;

                write_offset = write_addr_reg[11:0];
                aligned_offset = {write_offset[11:2], 2'b00};
                write_ok = is_write_access_valid(write_offset, axi.wstrb);

                if (write_ok) begin
                    case (aligned_offset)
                        REG_CONTROL: begin
                            masked_value = apply_wstrb_mask(control_reg, axi.wdata, axi.wstrb);
                            control_reg[0] <= masked_value[0];
                            control_reg[1] <= 1'b0; // Reserved bit forced low
                            control_reg[31:2] <= '0;
                            if (axi.wstrb[0] && axi.wdata[1]) begin
                                reset_stats_pulse <= 1'b1;
                            end
                        end

                        REG_CONFIG: begin
                            masked_value = apply_wstrb_mask(config_reg, axi.wdata, axi.wstrb);
                            config_reg[7:0] <= masked_value[7:0];
                            config_reg[15:8] <= masked_value[15:8];
                            config_reg[31:16] <= 16'b0;
                        end

                        REG_DEBUG: begin
                            masked_value = apply_wstrb_mask(debug_reg, axi.wdata, axi.wstrb);
                            debug_reg[3:0] <= masked_value[3:0];
                            debug_reg[31:4] <= 28'b0;
                        end

                        // Test registers - full 32-bit read/write (added 2025-10-05)
                        REG_TEST_0: begin
                            masked_value = apply_wstrb_mask(test_reg_0, axi.wdata, axi.wstrb);
                            test_reg_0 <= masked_value;
                            test_reg_0_write_detect <= 1'b1;
                        end

                        REG_TEST_1: begin
                            masked_value = apply_wstrb_mask(test_reg_1, axi.wdata, axi.wstrb);
                            test_reg_1 <= masked_value;
                            test_reg_1_write_detect <= 1'b1;
                        end

                        REG_TEST_2: begin
                            masked_value = apply_wstrb_mask(test_reg_2, axi.wdata, axi.wstrb);
                            test_reg_2 <= masked_value;
                            test_reg_2_write_detect <= 1'b1;
                        end

                        REG_TEST_3: begin
                            masked_value = apply_wstrb_mask(test_reg_3, axi.wdata, axi.wstrb);
                            test_reg_3 <= masked_value;
                            test_reg_3_write_detect <= 1'b1;
                        end

                        // Extended test registers (added 2025-10-09)
                        REG_TEST_4: begin
                            masked_value = apply_wstrb_mask(test_reg_4, axi.wdata, axi.wstrb);
                            test_reg_4 <= masked_value;
                            test_reg_4_write_detect <= 1'b1;
                        end

                        REG_TEST_5: begin
                            masked_value = apply_wstrb_mask(test_reg_5, axi.wdata, axi.wstrb);
                            test_reg_5 <= masked_value;
                            test_reg_5_write_detect <= 1'b1;
                        end

                        REG_TEST_6: begin
                            masked_value = apply_wstrb_mask(test_reg_6, axi.wdata, axi.wstrb);
                            test_reg_6 <= masked_value;
                            test_reg_6_write_detect <= 1'b1;
                        end

                        REG_TEST_7: begin
                            masked_value = apply_wstrb_mask(test_reg_7, axi.wdata, axi.wstrb);
                            test_reg_7 <= masked_value;
                            test_reg_7_write_detect <= 1'b1;
                        end

                        default: begin
                            // Writes to RO registers succeed but have no effect
                        end
                    endcase
                    write_resp <= RESP_OKAY;
                end else begin
                    write_resp <= RESP_SLVERR;
                end
            end
        end
    end
    
    assign bridge_reset_stats = reset_stats_pulse;

    // Register read logic
    always_comb begin
        logic [11:0] read_offset;
        logic [11:0] aligned_offset;
        bit read_ok;

        read_offset = read_addr_reg[11:0];
        aligned_offset = {read_offset[11:2], 2'b00};
        read_ok = is_read_access_valid(read_offset);

        read_resp = RESP_OKAY;
        read_data = '0;

        if (read_ok) begin
            case (aligned_offset)
                REG_CONTROL: begin
                    read_data = control_reg;
                end

                REG_STATUS: begin
                    read_data[0] = bridge_busy;
                    read_data[8:1] = error_code;
                    read_data[31:9] = '0;
                end

                REG_CONFIG: begin
                    read_data = config_reg;
                end

                REG_DEBUG: begin
                    read_data = debug_reg;
                end

                REG_TX_COUNT: begin
                    read_data[15:0] = tx_count;
                    read_data[31:16] = '0;
                end

                REG_RX_COUNT: begin
                    read_data[15:0] = rx_count;
                    read_data[31:16] = '0;
                end

                REG_FIFO_STAT: begin
                    read_data[7:0] = fifo_status;
                    read_data[31:8] = '0;
                end

                REG_VERSION: begin
                    read_data = 32'h0001_0000;  // Version 1.0.0
                end

                // Test registers - return stored values (added 2025-10-05, extended 2025-10-09)
                REG_TEST_0: begin
                    read_data = test_reg_0;
                end

                REG_TEST_1: begin
                    read_data = test_reg_1;
                end

                REG_TEST_2: begin
                    read_data = test_reg_2;
                end

                REG_TEST_3: begin
                    read_data = test_reg_3;
                end

                REG_TEST_4: begin
                    read_data = test_reg_4;
                end

                REG_TEST_5: begin
                    read_data = test_reg_5;
                end

                REG_TEST_6: begin
                    read_data = test_reg_6;
                end

                REG_TEST_7: begin
                    read_data = test_reg_7;
                end

                default: begin
                    read_data = '0;
                end
            endcase
        end else begin
            read_resp = RESP_SLVERR;
        end
    end
    
    // Output register mappings
    assign baud_div_config = config_reg[7:0];
    assign timeout_config = config_reg[15:8];
    assign debug_mode = debug_reg[3:0];

    `ifdef ENABLE_DEBUG
    // Critical debugging only - AXI handshakes and state transitions
    always_ff @(posedge clk) begin
        if (!rst && aw_handshake) begin
            $display("DEBUG: AW handshake addr=0x%08X at time %0t", axi.awaddr, $time);
        end
        if (!rst && ar_handshake) begin
            $display("DEBUG: AR handshake addr=0x%08X at time %0t", axi.araddr, $time);
        end
        // Only show critical register writes (control/status registers)
        if (!rst && write_enable && is_write_access_valid(write_addr_reg[11:0], axi.wstrb)) begin
            case ({write_addr_reg[11:2], 2'b00})
                REG_CONTROL: $display("DEBUG: CONTROL write=0x%08X", axi.wdata);
                REG_CONFIG: $display("DEBUG: CONFIG write=0x%08X", axi.wdata);
                default: begin end // Suppress test register spam
            endcase
        end
    end
    `endif

    // Debug output
    initial begin
        $display("REGISTER_BLOCK: FIXED version instantiated with BASE_ADDR=0x%08X", BASE_ADDR);
    end

endmodule