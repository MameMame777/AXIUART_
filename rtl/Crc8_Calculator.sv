`timescale 1ns / 1ps

// CRC8 Calculator Module for UART-AXI4 Bridge
// Polynomial: 0x07 (x^8 + x^2 + x^1 + 1)
// Initial value: 0x00, no reflection, no XOR output
// Matches test vectors in Section 10.2 of protocol specification
module Crc8_Calculator (
    input  logic        clk,
    input  logic        rst,
    input  logic        crc_enable,    // Enable CRC calculation for this byte
    input  logic [7:0]  data_in,       // Input data byte
    input  logic        crc_reset,     // Reset CRC to initial value
    output logic [7:0]  crc_out,       // Current CRC value
    output logic [7:0]  crc_final      // Final CRC value (same as crc_out)
);

    // CRC8 register
    logic [7:0] crc_reg;
    logic [7:0] crc_next;

    // CRC calculation logic (combinational)
    always_comb begin
        crc_next = crc_reg;
        if (crc_enable) begin
            logic [7:0] crc_temp;
            crc_temp = crc_reg ^ data_in;
            
            // Process each bit
            for (int i = 0; i < 8; i++) begin
                if (crc_temp[7]) begin
                    crc_temp = (crc_temp << 1) ^ 8'h07;
                end else begin
                    crc_temp = crc_temp << 1;
                end
            end
            crc_next = crc_temp;
        end
    end

    // CRC register update (sequential)
    always_ff @(posedge clk) begin
        if (rst || crc_reset) begin
            crc_reg <= 8'h00;  // Initial value per specification
        end else begin
            crc_reg <= crc_next;
        end
    end

    // Output assignments
    assign crc_out = crc_reg;
    assign crc_final = crc_reg;

    // Assertions for verification
    `ifdef ENABLE_CRC8_ASSERTIONS
        // Verify reset behavior
        assert_reset_behavior: assert property (
            @(posedge clk) (rst || crc_reset) |=> (crc_out == 8'h00)
        ) else $error("CRC8: Reset behavior violation");

        // Verify stability when not enabled
        assert_stability_when_disabled: assert property (
            @(posedge clk) disable iff (rst || crc_reset)
            !crc_enable |=> $stable(crc_out)
        ) else $error("CRC8: Stability violation when disabled");
    `endif

endmodule