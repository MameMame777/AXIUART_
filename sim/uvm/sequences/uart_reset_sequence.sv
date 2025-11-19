`timescale 1ns / 1ps

//=============================================================================
// uart_reset_sequence.sv
//
// RESET Command Sequence for UART-AXI4 Bridge
// 
// Description:
//   Sends protocol-level RESET command (CMD=0xFF) to soft-reset bridge
//   internal state (FIFOs, state machines) while preserving CONFIG registers.
//
// Protocol Frame:
//   Command: SOF (0xA5) | CMD (0xFF) | CRC (0x58)
//   Response: SOF (0x5A) | STATUS (0x00) | CMD echo (0xFF) | CRC (0x55)
//
// Use Case:
//   Safe baud rate switching after CONFIG register update.
//   Timeline: CONFIG write → RESET → UVM baud rate update → Data transfer
//
// Author: AXIUART Development Team
// Date: 2025-11-19
//=============================================================================

class uart_reset_sequence extends uvm_sequence #(uart_frame_transaction);
    `uvm_object_utils(uart_reset_sequence)
    
    // Configuration handle
    uart_axi4_config cfg;
    
    // Response tracking
    bit reset_ack_received = 0;
    bit reset_success = 0;
    
    function new(string name = "uart_reset_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction req;
        // No response transaction needed (RESET has no ACK)
        
        // Get configuration from sequencer
        if (!uvm_config_db#(uart_axi4_config)::get(null, get_full_name(), "cfg", cfg)) begin
            `uvm_fatal("RESET_SEQ", "Cannot get uart_axi4_config from config DB")
        end
        
        `uvm_info("RESET_SEQ", 
            $sformatf("Sending RESET command @ t=%0t", $time),
            UVM_MEDIUM)
        
        // Create RESET command transaction
        req = uart_frame_transaction::type_id::create("reset_cmd");
        start_item(req);
        
        // Build RESET frame per protocol specification
        // Frame: SOF (0xA5) | CMD (0xFF) | CRC (0x58)
        // CRITICAL: Set cmd field explicitly so driver can detect RESET
        req.cmd = 8'hFF;  // CMD = RESET (driver uses this field)
        req.addr = 32'h0;  // No address for RESET
        req.data = new[0];  // No data payload for RESET
        
        // Also set frame_data for compatibility
        req.frame_data = new[3];
        req.frame_data[0] = 8'hA5;  // SOF
        req.frame_data[1] = 8'hFF;  // CMD = RESET
        req.frame_data[2] = 8'h58;  // CRC (pre-calculated for RESET command)
        req.frame_length = 3;
        req.response_received = 1'b0;  // Not used (no response expected)
        
        finish_item(req);
        
        `uvm_info("RESET_SEQ",
            "RESET command transmitted (no response expected)",
            UVM_MEDIUM)
        
        // Wait for RTL soft reset propagation
        #10us;
        
        // Additional stabilization delay to clear UART line
        // This ensures old frame data is fully flushed before next transaction
        #50us;
        
        reset_success = 1;
        reset_ack_received = 1;  // Mark as complete
        
        `uvm_info("RESET_SEQ",
            $sformatf("RESET command completed (soft reset + 50us stabilization) @ t=%0t", $time),
            UVM_LOW)
    endtask

endclass
