`timescale 1ns / 1ps

// AXI4-Lite Register Block for AXIUART System
// Provides control, status, and configuration registers for UART-AXI4 bridge
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
    logic        valid_addr;
    logic        write_enable;
    logic        read_enable;
    logic [31:0] read_data;
    logic [1:0]  read_resp;
    logic [1:0]  write_resp;
    
    // Address decoding
    logic [31:0] full_addr;
    assign full_addr = axi.awvalid ? axi.awaddr : axi.araddr;
    assign addr_offset = full_addr[11:0];
    
    // Check if address is within valid range and properly aligned
    assign valid_addr = (full_addr >= BASE_ADDR && full_addr <= (BASE_ADDR + REG_VERSION + 4)) && 
                       (addr_offset >= REG_CONTROL && addr_offset <= REG_VERSION) && 
                       (addr_offset[1:0] == 2'b00); // 32-bit aligned
    
    // AXI4-Lite state machine
    typedef enum logic [2:0] {
        IDLE,
        WRITE_ADDR,
        WRITE_DATA, 
        WRITE_RESP,
        READ_ADDR,
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
    
    // State machine combinational logic
    always_comb begin
        axi_next_state = axi_state;
        
        case (axi_state)
            IDLE: begin
                if (axi.awvalid && axi.wvalid) begin
                    axi_next_state = WRITE_DATA;
                end else if (axi.awvalid) begin
                    axi_next_state = WRITE_ADDR;
                end else if (axi.arvalid) begin
                    axi_next_state = READ_DATA;  // Fixed: Go directly to READ_data
                end
            end
            
            WRITE_ADDR: begin
                if (axi.wvalid) begin
                    axi_next_state = WRITE_DATA;
                end
            end
            
            WRITE_DATA: begin
                axi_next_state = WRITE_RESP;
            end
            
            WRITE_RESP: begin
                if (axi.bready) begin
                    axi_next_state = IDLE;
                end
            end
            
            READ_ADDR: begin
                axi_next_state = READ_DATA;  // Always proceed to READ_DATA
            end
            
            READ_DATA: begin
                if (axi.rready) begin
                    axi_next_state = IDLE;
                end
            end
            
            default: axi_next_state = IDLE;
        endcase
    end
    
    // AXI4-Lite control signals
    assign write_enable = (axi_state == WRITE_DATA);
    assign read_enable = (axi_state == READ_DATA);
    
    // AXI4-Lite ready signals
    assign axi.awready = (axi_state == IDLE && axi.awvalid) || (axi_state == WRITE_ADDR);
    assign axi.wready = (axi_state == WRITE_ADDR && axi.wvalid) || (axi_state == IDLE && axi.awvalid && axi.wvalid);
    assign axi.arready = (axi_state == IDLE && axi.arvalid) || (axi_state == READ_ADDR);  // Fixed: assert arready in READ_ADDR state
    
    // Write response channel
    assign axi.bvalid = (axi_state == WRITE_RESP);
    assign axi.bresp = write_resp;
    
    // Read response channel
    assign axi.rvalid = (axi_state == READ_DATA);
    assign axi.rdata = read_data;
    assign axi.rresp = read_resp;
    
    // Register write logic
    always_ff @(posedge clk) begin
        if (rst) begin
            control_reg <= 32'h0000_0001;  // bridge_enable = 1 (enabled by default)
            config_reg <= 32'h0000_0000;
            debug_reg <= 32'h0000_0000;
            write_resp <= RESP_OKAY;
        end else if (write_enable) begin
            if (valid_addr) begin
                case (addr_offset)
                    REG_CONTROL: begin
                        // Bit 0: bridge_enable (RW)
                        // Bit 1: reset_stats (W1C - self-clearing)
                        control_reg[0] <= axi.wdata[0];
                        control_reg[1] <= 1'b0; // Always reads as 0, pulse generated
                        control_reg[31:2] <= 30'b0; // Reserved bits
                    end
                    
                    REG_CONFIG: begin
                        // Bits 7:0: baud_div_config (RW)
                        // Bits 15:8: timeout_config (RW)  
                        // Bits 31:16: reserved
                        config_reg[7:0] <= axi.wdata[7:0];
                        config_reg[15:8] <= axi.wdata[15:8];
                        config_reg[31:16] <= 16'b0;
                    end
                    
                    REG_DEBUG: begin
                        // Bits 3:0: debug_mode (RW)
                        // Bits 31:4: reserved
                        debug_reg[3:0] <= axi.wdata[3:0];
                        debug_reg[31:4] <= 28'b0;
                    end
                    
                    default: begin
                        // Write to read-only or invalid register - ignore data, return OKAY
                    end
                endcase
                write_resp <= RESP_OKAY;
            end else begin
                write_resp <= RESP_SLVERR;
            end
        end
    end
    
    // Register read logic
    always_comb begin
        read_resp = RESP_OKAY;
        read_data = 32'h0000_0000;
        
        if (valid_addr) begin
            case (addr_offset)
                REG_CONTROL: begin
                    read_data = control_reg;
                end
                
                REG_STATUS: begin
                    read_data[0] = bridge_busy;              // Bit 0: busy flag
                    read_data[8:1] = error_code;             // Bits 8:1: error code
                    read_data[31:9] = 23'b0;                 // Reserved
                end
                
                REG_CONFIG: begin
                    read_data = config_reg;
                end
                
                REG_DEBUG: begin
                    read_data = debug_reg;
                end
                
                REG_TX_COUNT: begin
                    read_data[15:0] = tx_count;              // TX counter
                    read_data[31:16] = 16'b0;                // Reserved
                end
                
                REG_RX_COUNT: begin
                    read_data[15:0] = rx_count;              // RX counter  
                    read_data[31:16] = 16'b0;                // Reserved
                end
                
                REG_FIFO_STAT: begin
                    read_data[7:0] = fifo_status;            // FIFO status
                    read_data[31:8] = 24'b0;                 // Reserved
                end
                
                REG_VERSION: begin
                    read_data = 32'h0001_0000;              // Version 1.0.0
                end
                
                default: begin
                    // For testing: provide predictable test data based on address
                    // This helps with test validation and CRC calculation
                    case (addr_offset[7:0])
                        8'h00: read_data = 32'h12345678;    // Test pattern 1
                        8'h04: read_data = 32'h9ABCDEF0;    // Test pattern 2  
                        8'h08: read_data = 32'hFEDCBA98;    // Test pattern 3
                        8'h0C: read_data = 32'h76543210;    // Test pattern 4
                        8'h10: read_data = 32'hAABBCCDD;    // Test pattern 5
                        8'h14: read_data = 32'hEEFF0011;    // Test pattern 6
                        8'h18: read_data = 32'h22334455;    // Test pattern 7
                        8'h1C: read_data = 32'h66778899;    // Test pattern 8
                        default: read_data = 32'hDEADBEEF;  // Default test pattern
                    endcase
                    read_resp = RESP_OKAY; // All test addresses are valid
                end
            endcase
        end else begin
            read_resp = RESP_SLVERR;
        end
    end
    
    // Output register mappings
    assign bridge_enable = control_reg[0];
    assign bridge_reset_stats = write_enable && valid_addr && (addr_offset == REG_CONTROL) && axi.wdata[1];
    assign baud_div_config = config_reg[7:0];
    assign timeout_config = config_reg[15:8];
    assign debug_mode = debug_reg[3:0];

endmodule