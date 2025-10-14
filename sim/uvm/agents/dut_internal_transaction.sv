// DUT Internal State Transaction for Enhanced Monitoring
// Implements QA-2.1: DUT internal state visibility for debugging
// Author: QA Framework - FastMCP v2.0
// Date: 2025-10-14

`timescale 1ns / 1ps

class dut_internal_transaction extends uvm_transaction;
    `uvm_object_utils(dut_internal_transaction)

    // DUT Internal State Fields
    rand int unsigned internal_state;      // Current FSM state
    rand int unsigned fifo_level;         // FIFO fill level
    rand int unsigned error_flags;        // Error condition flags
    rand bit          frame_valid;        // Frame validation status
    rand bit          crc_valid;          // CRC validation status
    rand bit          timeout_active;     // Timeout timer status
    
    // AXI Master State
    rand bit          axi_busy;           // AXI master busy flag
    rand bit          axi_error;          // AXI master error flag
    rand int unsigned axi_pending_count;  // Pending AXI transactions
    
    // UART Interface State  
    rand bit          uart_rx_active;     // UART RX activity
    rand bit          uart_tx_active;     // UART TX activity
    rand int unsigned uart_error_count;   // UART error counter
    
    // Timing Information
    time              timestamp;          // Transaction timestamp
    time              state_duration;     // Time in current state
    
    // Quality Metrics
    rand real         processing_efficiency; // Processing speed metric
    rand int unsigned resource_utilization;  // Resource usage percentage

    // Constructor
    function new(string name = "dut_internal_transaction");
        super.new(name);
        timestamp = $time;
    endfunction

    // Copy Function
    virtual function void do_copy(uvm_object rhs);
        dut_internal_transaction rhs_;
        if (!$cast(rhs_, rhs)) begin
            `uvm_fatal("DUT_TRANS", "Failed to cast rhs to dut_internal_transaction")
        end
        
        super.do_copy(rhs_);
        internal_state = rhs_.internal_state;
        fifo_level = rhs_.fifo_level;
        error_flags = rhs_.error_flags;
        frame_valid = rhs_.frame_valid;
        crc_valid = rhs_.crc_valid;
        timeout_active = rhs_.timeout_active;
        axi_busy = rhs_.axi_busy;
        axi_error = rhs_.axi_error;
        axi_pending_count = rhs_.axi_pending_count;
        uart_rx_active = rhs_.uart_rx_active;
        uart_tx_active = rhs_.uart_tx_active;
        uart_error_count = rhs_.uart_error_count;
        timestamp = rhs_.timestamp;
        state_duration = rhs_.state_duration;
        processing_efficiency = rhs_.processing_efficiency;
        resource_utilization = rhs_.resource_utilization;
    endfunction

    // Compare Function
    virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        dut_internal_transaction rhs_;
        if (!$cast(rhs_, rhs)) return 0;
        
        return (super.do_compare(rhs_, comparer) &&
                (internal_state == rhs_.internal_state) &&
                (fifo_level == rhs_.fifo_level) &&
                (error_flags == rhs_.error_flags) &&
                (frame_valid == rhs_.frame_valid) &&
                (crc_valid == rhs_.crc_valid) &&
                (timeout_active == rhs_.timeout_active) &&
                (axi_busy == rhs_.axi_busy) &&
                (axi_error == rhs_.axi_error) &&
                (axi_pending_count == rhs_.axi_pending_count) &&
                (uart_rx_active == rhs_.uart_rx_active) &&
                (uart_tx_active == rhs_.uart_tx_active) &&
                (uart_error_count == rhs_.uart_error_count));
    endfunction

    // Convert to String
    virtual function string convert2string();
        string state_name;
        case (internal_state)
            0: state_name = "IDLE";
            1: state_name = "RECEIVING";
            2: state_name = "PROCESSING";
            3: state_name = "RESPONDING";
            default: state_name = $sformatf("UNKNOWN_%0d", internal_state);
        endcase
        
        return $sformatf({
            "DUT_INTERNAL_TRANSACTION:\n",
            "  State: %s (%0d)\n",
            "  FIFO Level: %0d\n",
            "  Error Flags: 0x%02x\n",
            "  Frame Valid: %b\n", 
            "  CRC Valid: %b\n",
            "  Timeout Active: %b\n",
            "  AXI Busy: %b\n",
            "  AXI Error: %b\n",
            "  AXI Pending: %0d\n",
            "  UART RX Active: %b\n",
            "  UART TX Active: %b\n",
            "  UART Errors: %0d\n",
            "  Timestamp: %0t\n",
            "  State Duration: %0t\n",
            "  Processing Efficiency: %.2f%%\n",
            "  Resource Utilization: %0d%%"
        }, state_name, internal_state, fifo_level, error_flags, 
           frame_valid, crc_valid, timeout_active, axi_busy, axi_error,
           axi_pending_count, uart_rx_active, uart_tx_active, uart_error_count,
           timestamp, state_duration, processing_efficiency, resource_utilization);
    endfunction

    // Constraints for Realistic Values
    constraint valid_ranges {
        internal_state inside {[0:4]};
        fifo_level inside {[0:64]};
        error_flags inside {[0:255]};
        axi_pending_count inside {[0:16]};
        uart_error_count inside {[0:100]};
        processing_efficiency inside {[0.0:100.0]};
        resource_utilization inside {[0:100]};
    }

    // State Analysis Methods
    virtual function bit is_error_state();
        return (internal_state == 4) || (error_flags != 0) || axi_error || (uart_error_count > 0);
    endfunction

    virtual function bit is_active_state();
        return (internal_state inside {1, 2, 3}) || axi_busy || uart_rx_active || uart_tx_active;
    endfunction

    virtual function bit is_idle_state();
        return (internal_state == 0) && !axi_busy && !uart_rx_active && !uart_tx_active;
    endfunction

    virtual function real get_utilization_ratio();
        return real'(resource_utilization) / 100.0;
    endfunction

endclass