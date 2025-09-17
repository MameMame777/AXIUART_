`timescale 1ns / 1ps

// AXI4-Lite Master Module for UART-AXI4 Bridge
// Performs AXI4-Lite transactions based on parsed UART commands
module Axi4_Lite_Master #(
    parameter int AXI_TIMEOUT = 1000,      // Timeout in clock cycles
    parameter int EARLY_BUSY_THRESHOLD = 100  // Early BUSY threshold
)(
    input  logic        clk,
    input  logic        rst,
    
    // Command interface
    input  logic [7:0]  cmd,               // Command byte from parser
    input  logic [31:0] addr,              // Address from parser
    input  logic [7:0]  write_data [0:63], // Write data from parser
    input  logic        start_transaction, // Start AXI transaction
    output logic        transaction_done,  // Transaction complete
    output logic [7:0]  axi_status,        // Transaction status
    
    // Read data output
    output logic [7:0]  read_data [0:63],  // Read data for frame builder
    output logic [5:0]  read_data_count,   // Number of read data bytes
    
    // AXI4-Lite Master Interface
    axi4_lite_if.master axi
);

    // Status codes from protocol specification
    localparam [7:0] STATUS_OK        = 8'h00;
    localparam [7:0] STATUS_ADDR_ALIGN = 8'h03;
    localparam [7:0] STATUS_TIMEOUT   = 8'h04;
    localparam [7:0] STATUS_AXI_SLVERR = 8'h05;
    localparam [7:0] STATUS_BUSY      = 8'h06;
    
    // Command field parsing
    logic rw_bit;
    logic inc_bit;
    logic [1:0] size_field;
    logic [3:0] len_field;
    
    always_comb begin
        rw_bit = cmd[7];
        inc_bit = cmd[6];
        size_field = cmd[5:4];
        len_field = cmd[3:0];
    end
    
    // Address alignment checker
    logic addr_ok;
    logic [3:0] wstrb;
    logic [2:0] align_status;
    
    Address_Aligner addr_aligner (
        .addr(addr),
        .size(size_field),
        .addr_ok(addr_ok),
        .wstrb(wstrb),
        .status_code(align_status)
    );
    
    // Beat size calculation
    logic [2:0] beat_size;
    always_comb begin
        case (size_field)
            2'b00: beat_size = 1;  // 8-bit
            2'b01: beat_size = 2;  // 16-bit
            2'b10: beat_size = 4;  // 32-bit
            default: beat_size = 0; // Invalid
        endcase
    end
    
    // State machine
    typedef enum logic [3:0] {
        IDLE,
        CHECK_ALIGNMENT,
        WRITE_ADDR,
        WRITE_DATA,
        WRITE_RESP,
        READ_ADDR,
        READ_DATA,
        NEXT_BEAT,
        DONE,
        ERROR
    } axi_state_t;
    
    axi_state_t state, state_next;
    
    // Internal registers
    logic [3:0] beat_counter;
    logic [31:0] current_addr;
    logic [5:0] data_byte_index;
    logic [7:0] status_reg;
    logic [15:0] timeout_counter;
    logic early_busy_sent;
    
    // Timeout and busy logic
    logic timeout_occurred;
    logic early_busy_threshold_reached;
    
    always_comb begin
        timeout_occurred = (timeout_counter >= AXI_TIMEOUT);
        early_busy_threshold_reached = (timeout_counter >= EARLY_BUSY_THRESHOLD);
    end
    
    // State machine (sequential part)
    always_ff @(posedge clk) begin
        if (rst) begin
            state <= IDLE;
            beat_counter <= '0;
            current_addr <= '0;
            data_byte_index <= '0;
            status_reg <= STATUS_OK;
            timeout_counter <= '0;
            early_busy_sent <= 1'b0;
        end else begin
            state <= state_next;
            
            // Initialize on transaction start
            if (start_transaction && (state == IDLE)) begin
                beat_counter <= '0;
                current_addr <= addr;
                data_byte_index <= '0;
                status_reg <= STATUS_OK;
                timeout_counter <= '0;
                early_busy_sent <= 1'b0;
            end
            
            // Update beat counter and address for next beat
            if (state == NEXT_BEAT) begin
                beat_counter <= beat_counter + 1;
                if (inc_bit) begin
                    current_addr <= current_addr + beat_size;
                end
                data_byte_index <= data_byte_index + beat_size;
            end
            
            // Timeout counter management
            if ((state == WRITE_ADDR) || (state == WRITE_DATA) || (state == WRITE_RESP) ||
                (state == READ_ADDR) || (state == READ_DATA)) begin
                if (!timeout_occurred) begin
                    timeout_counter <= timeout_counter + 1;
                end
            end else begin
                timeout_counter <= '0;
            end
            
            // Early BUSY status tracking
            if ((state == READ_DATA) && early_busy_threshold_reached && !early_busy_sent) begin
                early_busy_sent <= 1'b1;
                // Note: In real implementation, this would trigger BUSY response
                // For now, we continue waiting until full timeout
            end
            
            // Status updates
            if (state == CHECK_ALIGNMENT) begin
                if (!addr_ok) begin
                    status_reg <= STATUS_ADDR_ALIGN;
                end
            end
            
            if (timeout_occurred && ((state == WRITE_ADDR) || (state == WRITE_DATA) || 
                                   (state == WRITE_RESP) || (state == READ_ADDR) || (state == READ_DATA))) begin
                status_reg <= early_busy_sent ? STATUS_BUSY : STATUS_TIMEOUT;
            end
            
            if ((state == WRITE_RESP) && axi.bvalid && axi.bready) begin
                if (axi.bresp != 2'b00) begin  // OKAY = 2'b00
                    status_reg <= STATUS_AXI_SLVERR;
                end
            end
            
            if ((state == READ_DATA) && axi.rvalid && axi.rready) begin
                if (axi.rresp != 2'b00) begin  // OKAY = 2'b00
                    status_reg <= STATUS_AXI_SLVERR;
                end
            end
        end
    end
    
    // State machine (combinational part)
    always_comb begin
        state_next = state;
        
        case (state)
            IDLE: begin
                if (start_transaction) begin
                    state_next = CHECK_ALIGNMENT;
                end
            end
            
            CHECK_ALIGNMENT: begin
                if (!addr_ok) begin
                    state_next = ERROR;
                end else if (rw_bit) begin  // Read
                    state_next = READ_ADDR;
                end else begin  // Write
                    state_next = WRITE_ADDR;
                end
            end
            
            WRITE_ADDR: begin
                if (axi.awready && axi.awvalid) begin
                    state_next = WRITE_DATA;
                end else if (timeout_occurred) begin
                    state_next = ERROR;
                end
            end
            
            WRITE_DATA: begin
                if (axi.wready && axi.wvalid) begin
                    state_next = WRITE_RESP;
                end else if (timeout_occurred) begin
                    state_next = ERROR;
                end
            end
            
            WRITE_RESP: begin
                if (axi.bvalid && axi.bready) begin
                    if (beat_counter >= len_field) begin
                        state_next = DONE;
                    end else begin
                        state_next = NEXT_BEAT;
                    end
                end else if (timeout_occurred) begin
                    state_next = ERROR;
                end
            end
            
            READ_ADDR: begin
                if (axi.arready && axi.arvalid) begin
                    state_next = READ_DATA;
                end else if (timeout_occurred) begin
                    state_next = ERROR;
                end
            end
            
            READ_DATA: begin
                if (axi.rvalid && axi.rready) begin
                    if (beat_counter >= len_field) begin
                        state_next = DONE;
                    end else begin
                        state_next = NEXT_BEAT;
                    end
                end else if (timeout_occurred) begin
                    state_next = ERROR;
                end
            end
            
            NEXT_BEAT: begin
                if (rw_bit) begin  // Read
                    state_next = READ_ADDR;
                end else begin  // Write
                    state_next = WRITE_ADDR;
                end
            end
            
            DONE: begin
                state_next = IDLE;
            end
            
            ERROR: begin
                state_next = IDLE;
            end
        endcase
    end
    
    // AXI4-Lite signal assignments
    always_comb begin
        // Default values
        axi.awaddr = current_addr;
        axi.awprot = 3'b000;  // Non-secure, unprivileged, data access
        axi.awvalid = 1'b0;
        
        axi.wdata = '0;
        axi.wstrb = wstrb;
        axi.wvalid = 1'b0;
        
        axi.bready = 1'b0;
        
        axi.araddr = current_addr;
        axi.arprot = 3'b000;  // Non-secure, unprivileged, data access
        axi.arvalid = 1'b0;
        
        axi.rready = 1'b0;
        
        // State-specific assignments
        case (state)
            WRITE_ADDR: begin
                axi.awvalid = 1'b1;
            end
            
            WRITE_DATA: begin
                axi.wvalid = 1'b1;
                // Pack write data based on size and byte index
                case (size_field)
                    2'b00: begin  // 8-bit
                        axi.wdata[7:0] = write_data[data_byte_index];
                    end
                    2'b01: begin  // 16-bit
                        axi.wdata[7:0] = write_data[data_byte_index];
                        axi.wdata[15:8] = write_data[data_byte_index + 1];
                    end
                    2'b10: begin  // 32-bit
                        axi.wdata[7:0] = write_data[data_byte_index];
                        axi.wdata[15:8] = write_data[data_byte_index + 1];
                        axi.wdata[23:16] = write_data[data_byte_index + 2];
                        axi.wdata[31:24] = write_data[data_byte_index + 3];
                    end
                endcase
            end
            
            WRITE_RESP: begin
                axi.bready = 1'b1;
            end
            
            READ_ADDR: begin
                axi.arvalid = 1'b1;
            end
            
            READ_DATA: begin
                axi.rready = 1'b1;
            end
        endcase
    end
    
    // Read data capture
    always_ff @(posedge clk) begin
        if (rst) begin
            read_data_count <= '0;
        end else if ((state == READ_DATA) && axi.rvalid && axi.rready) begin
            // Unpack read data based on size
            case (size_field)
                2'b00: begin  // 8-bit
                    read_data[data_byte_index] <= axi.rdata[7:0];
                end
                2'b01: begin  // 16-bit
                    read_data[data_byte_index] <= axi.rdata[7:0];
                    read_data[data_byte_index + 1] <= axi.rdata[15:8];
                end
                2'b10: begin  // 32-bit
                    read_data[data_byte_index] <= axi.rdata[7:0];
                    read_data[data_byte_index + 1] <= axi.rdata[15:8];
                    read_data[data_byte_index + 2] <= axi.rdata[23:16];
                    read_data[data_byte_index + 3] <= axi.rdata[31:24];
                end
            endcase
            
            // Update read data count
            if (beat_counter >= len_field) begin
                read_data_count <= data_byte_index + beat_size;
            end
        end else if (state == IDLE) begin
            read_data_count <= '0;
        end
    end
    
    // Output assignments
    assign transaction_done = (state == DONE) || (state == ERROR);
    assign axi_status = status_reg;

endmodule