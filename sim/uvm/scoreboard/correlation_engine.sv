`timescale 1ns / 1ps

// Phase 3: Correlation Engine for UART-AXI4 Scoreboard
// Created: October 11, 2025
// Purpose: Correlate UART frames and AXI transactions for verification

// Forward declarations and typedefs
typedef uart_frame_transaction uart_frame_queue_t[$];
typedef axi4_lite_transaction axi_transaction_queue_t[$];

class correlation_engine extends uvm_component;
    `uvm_component_utils(correlation_engine)

    // Internal queues for correlation - using dynamic arrays
    uart_frame_transaction uart_frames[$];
    axi4_lite_transaction axi_transactions[$];

    function new(string name = "correlation_engine", uvm_component parent = null);
        super.new(name, parent);
        // Queues are automatically initialized
    endfunction

    // Add UART frame for correlation
    function void add_uart_frame(uart_frame_transaction frame);
        uart_frames.push_back(frame);
    endfunction

    // Add AXI transaction for correlation
    function void add_axi_transaction(axi4_lite_transaction trans);
        axi_transactions.push_back(trans);
    endfunction

    // Correlate UART frames and AXI transactions
    function void correlate();
        // Simple matching logic (expand as needed)
        foreach (uart_frames[i]) begin
            foreach (axi_transactions[j]) begin
                if (uart_frames[i].addr == axi_transactions[j].addr) begin
                    `uvm_info("CORRELATION_ENGINE", $sformatf("Match: UART frame %0d <-> AXI trans %0d", i, j), UVM_MEDIUM)
                end
            end
        end
    endfunction

    // Clear queues after correlation
    function void clear();
        uart_frames.delete();
        axi_transactions.delete();
    endfunction

endclass
