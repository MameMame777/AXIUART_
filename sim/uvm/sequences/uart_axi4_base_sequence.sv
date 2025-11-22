`timescale 1ns / 1ps

// Base Sequence Class for UART-AXI4 Error Injection Tests
class uart_axi4_base_sequence extends uvm_sequence #(uart_frame_transaction);
    
    `uvm_object_utils(uart_axi4_base_sequence)
    
    // Configuration
    uart_axi4_env_config cfg;
    
    function new(string name = "uart_axi4_base_sequence");
        super.new(name);
    endfunction
    
    virtual task pre_body();
        // Get configuration if available
        if (!uvm_config_db#(uart_axi4_env_config)::get(null, get_full_name(), "cfg", cfg)) begin
            `uvm_warning(get_type_name(), "Configuration not found, using defaults")
        end
    endtask
    
    // CRC8 calculation function matching RTL polynomial 0x07
    virtual function bit [7:0] calculate_crc8(bit [7:0] data_bytes[], int byte_count = -1);
        bit [7:0] crc = 8'h00;
        int actual_count;
        
        // DSIM fix: avoid signed/unsigned comparison with .size()
        if (byte_count < 0) actual_count = data_bytes.size();
        else actual_count = byte_count;
        
        // CRC8 calculation with polynomial 0x07 (matching Frame_Parser.sv)
        for (int i = 0; i < actual_count; i++) begin
            crc = crc ^ data_bytes[i];
            for (int j = 0; j < 8; j++) begin
                if (crc & 8'h80) begin
                    crc = (crc << 1) ^ 8'h07;
                end else begin
                    crc = crc << 1;
                end
            end
        end
        
        return crc;
    endfunction
    
    // Helper function to build frame bytes for CRC calculation
    virtual function bit [7:0][] build_frame_bytes(uart_frame_transaction trans);
        bit [7:0] frame_bytes[];
        int byte_count;
        
        // Calculate frame size: SOF + CMD + ADDR(4) + DATA + (no CRC for calculation)
        byte_count = 1 + 1 + 4 + trans.data.size();
        frame_bytes = new[byte_count];
        
        // Serialize frame data
        frame_bytes[0] = trans.sof;
        frame_bytes[1] = trans.cmd;
        frame_bytes[2] = trans.addr[31:24];
        frame_bytes[3] = trans.addr[23:16];
        frame_bytes[4] = trans.addr[15:8];
        frame_bytes[5] = trans.addr[7:0];
        
        for (int i = 0; i < trans.data.size(); i++) begin
            frame_bytes[6 + i] = trans.data[i];
        end
        
        return frame_bytes;
    endfunction
    
    // Validate expected data bytes based on command
    virtual function int calculate_expected_bytes(bit [7:0] cmd);
        bit [1:0] size_field = cmd[5:4];
        bit [3:0] len_field = cmd[3:0];
        int bytes_per_transfer;
        int expected_bytes;
        
        // Decode size field (matching Frame_Parser.sv logic)
        case (size_field)
            2'b00: bytes_per_transfer = 1;  // 8-bit
            2'b01: bytes_per_transfer = 2;  // 16-bit 
            2'b10: bytes_per_transfer = 4;  // 32-bit
            2'b11: return -1;               // Invalid (STATUS_CMD_INV)
        endcase
        
        expected_bytes = bytes_per_transfer * (len_field + 1);
        
        // Check maximum constraints (from RTL analysis)
        if (expected_bytes > 64) return -1;  // STATUS_LEN_RANGE
        
        return expected_bytes;
    endfunction
    
    // Check address alignment based on command size field
    virtual function bit check_address_alignment(logic [31:0] addr, bit [7:0] cmd);
        bit [1:0] size_field = cmd[5:4];
        
        case (size_field)
            2'b00: return 1'b1;                    // 8-bit: always aligned
            2'b01: return (addr[0] == 1'b0);       // 16-bit: 2-byte aligned
            2'b10: return (addr[1:0] == 2'b00);    // 32-bit: 4-byte aligned
            2'b11: return 1'b0;                    // Invalid size
        endcase
    endfunction
    
endclass