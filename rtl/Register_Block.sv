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
    output logic        bridge_enable,         // Enable UART bridge operation
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

    // Register storage
    logic [31:0] control_reg;      // RW - Control register
    logic [31:0] config_reg;       // RW - Configuration register  
    logic [31:0] debug_reg;        // RW - Debug register
    
    // AXI4-Lite response codes
    localparam bit [1:0] RESP_OKAY   = 2'b00;
    localparam bit [1:0] RESP_SLVERR = 2'b10;
    
    // Internal signals
    logic [11:0] addr_offset;
    logic        write_enable;
    logic        read_enable;
    logic [31:0] read_data;
    logic [1:0]  read_resp;
    logic [1:0]  write_resp;
    logic [31:0] write_addr_reg;
    logic [31:0] read_addr_reg;
    logic [31:0] active_addr;
    logic        aw_handshake;
    logic        w_handshake;
    logic        ar_handshake;
    
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
        within_register_range = (aligned_offset >= REG_CONTROL) && (aligned_offset <= REG_VERSION);
        if (!within_register_range) begin
            return 1'b0;
        end
        if (offset > (REG_VERSION + 12'd3)) begin
            return 1'b0;
        end
        return is_wstrb_supported(offset[1:0], wstrb);
    endfunction

    function automatic bit is_read_access_valid(logic [11:0] offset);
        logic [11:0] aligned_offset;
        aligned_offset = {offset[11:2], 2'b00};
        if ((aligned_offset < REG_CONTROL) || (aligned_offset > REG_VERSION)) begin
            return 1'b0;
        end
        if (offset > (REG_VERSION + 12'd3)) begin
            return 1'b0;
        end
        return (offset[1:0] == 2'b00);
    endfunction

    // AXI4-Lite control signals
    assign aw_handshake = axi.awvalid && axi.awready;
    assign w_handshake = axi.wvalid && axi.wready;
    assign ar_handshake = axi.arvalid && axi.arready;

    assign write_enable = (axi_state == WRITE_DATA) && w_handshake;
    assign read_enable = (axi_state == READ_DATA);
    
    // AXI4-Lite ready signals - FIXED: No circular dependencies
    assign axi.awready = (axi_state == IDLE) || (axi_state == WRITE_ADDR);
    assign axi.wready = (axi_state == WRITE_DATA);
    assign axi.arready = (axi_state == IDLE);
    
    // Write response channel
    assign axi.bvalid = (axi_state == WRITE_RESP);
    assign axi.bresp = write_resp;
    
    // Read response channel
    assign axi.rvalid = (axi_state == READ_DATA);
    assign axi.rdata = read_data;
    assign axi.rresp = read_resp;
    
    // Register write logic
    logic reset_stats_pulse;

    always_ff @(posedge clk) begin
        if (rst) begin
            control_reg <= 32'h0000_0001;  // bridge_enable = 1 (enabled by default)
            config_reg <= 32'h0000_0000;
            debug_reg <= 32'h0000_0000;
            write_resp <= RESP_OKAY;
            write_addr_reg <= BASE_ADDR;
            read_addr_reg <= BASE_ADDR;
            reset_stats_pulse <= 1'b0;
        end else begin
            reset_stats_pulse <= 1'b0;

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

                default: begin
                    read_data = '0;
                end
            endcase
        end else begin
            read_resp = RESP_SLVERR;
        end
    end
    
    // Output register mappings
    assign bridge_enable = control_reg[0];
    assign baud_div_config = config_reg[7:0];
    assign timeout_config = config_reg[15:8];
    assign debug_mode = debug_reg[3:0];

    `ifdef ENABLE_DEBUG
    always_ff @(posedge clk) begin
        if (!rst && write_enable &&
            is_write_access_valid(write_addr_reg[11:0], axi.wstrb) &&
            ({write_addr_reg[11:2], 2'b00} == REG_CONTROL)) begin
            $display("DEBUG: Register_Block CONTROL write data=0x%08X -> bridge_enable=%0b at time %0t", axi.wdata, axi.wdata[0], $time);
        end
    end
    `endif

    `ifdef ENABLE_DEBUG
    always_ff @(posedge clk) begin
        if (!rst && aw_handshake) begin
            $display("DEBUG: Register_Block AW handshake addr=0x%08X at time %0t", axi.awaddr, $time);
        end
        if (!rst && w_handshake) begin
            $display("DEBUG: Register_Block W handshake data=0x%08X wstrb=0x%X at time %0t", axi.wdata, axi.wstrb, $time);
        end
        if (!rst && ar_handshake) begin
            $display("DEBUG: Register_Block AR handshake addr=0x%08X at time %0t", axi.araddr, $time);
        end
    end
    `endif

    // Debug output
    initial begin
        $display("REGISTER_BLOCK: FIXED version instantiated with BASE_ADDR=0x%08X", BASE_ADDR);
    end

endmodule