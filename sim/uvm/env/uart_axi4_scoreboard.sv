`timescale 1ns / 1ps

// UVM Scoreboard for UART-AXI4 Bridge
class uart_axi4_scoreboard extends uvm_scoreboard;
    
    `uvm_component_utils(uart_axi4_scoreboard)
    
    // Analysis ports for receiving transactions
    `uvm_analysis_imp_decl(_uart)
    `uvm_analysis_imp_decl(_axi)
    uvm_analysis_imp_uart #(uart_frame_transaction, uart_axi4_scoreboard) uart_analysis_imp;
    uvm_analysis_imp_axi #(axi4_lite_transaction, uart_axi4_scoreboard) axi_analysis_imp;
    
    // Configuration
    uart_axi4_env_config cfg;
    
    // Queues for matching transactions
    uart_frame_transaction uart_queue[$];
    axi4_lite_transaction axi_queue[$];
    
    // Statistics
    int uart_transactions_received = 0;
    int axi4_lite_transactions_received = 0;
    int match_count = 0;
    int mismatch_count = 0;
    int error_frame_count = 0;
    int crc_error_count = 0;
    int timeout_count = 0;
    int protocol_error_count = 0;
    int critical_error_count = 0;
    int transaction_count = 0;
    int total_bytes_transferred = 0;
    int total_test_time = 0;
    int average_latency_ns = 0;
    int peak_latency_ns = 0;
    
    function new(string name = "uart_axi4_scoreboard", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        uart_analysis_imp = new("uart_analysis_imp", this);
        axi_analysis_imp = new("axi_analysis_imp", this);
        
        if (!uvm_config_db#(uart_axi4_env_config)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("SCOREBOARD", "Failed to get configuration object")
        end
    endfunction
    
    // Receive UART transactions
    virtual function void write_uart(uart_frame_transaction tr);
        uart_frame_transaction uart_tr;
        
        if (tr.direction == UART_TX && tr.parse_error_kind != PARSE_ERROR_NONE) begin
            `uvm_warning("SCOREBOARD", $sformatf("Skipping UART_TX transaction due to monitor parse error: %s", tr.parse_error_kind.name()))
            return;
        end

        $cast(uart_tr, tr.clone());
        uart_queue.push_back(uart_tr);
        uart_transactions_received++;

        `uvm_info("SCOREBOARD", $sformatf("Received UART transaction: CMD=0x%02X, ADDR=0x%08X", 
                  uart_tr.cmd, uart_tr.addr), UVM_DEBUG)
        
        // Check for matching AXI transaction
        check_for_matches();
    endfunction
    
    // Receive AXI transactions
    virtual function void write_axi(axi4_lite_transaction tr);
        axi4_lite_transaction axi_tr;
        
        $cast(axi_tr, tr.clone());
        axi_queue.push_back(axi_tr);
        axi4_lite_transactions_received++;
        
        `uvm_info("SCOREBOARD", $sformatf("Received AXI transaction: ADDR=0x%08X, WDATA=0x%08X, WSTRB=0x%X", 
                  axi_tr.addr, axi_tr.wdata, axi_tr.wstrb), UVM_DEBUG)
        
        // Check for matching UART transaction
        check_for_matches();
    endfunction
    
    // Check for transaction matches
    virtual function void check_for_matches();
        uart_frame_transaction uart_tr;
        axi4_lite_transaction axi_tr;
        bit match_found = 0;
        
        // Simple matching: find UART and AXI transactions with same address
        for (int i = 0; i < uart_queue.size(); i++) begin
            uart_tr = uart_queue[i];
            
            for (int j = 0; j < axi_queue.size(); j++) begin
                axi_tr = axi_queue[j];
                
                if (uart_tr.addr == axi_tr.addr) begin
                    // Found matching addresses, now verify transaction details
                    if (verify_transaction_match(uart_tr, axi_tr)) begin
                        match_count++;
                        match_found = 1;
                        `uvm_info("SCOREBOARD", $sformatf("Transaction match found: ADDR=0x%08X", uart_tr.addr), UVM_MEDIUM)
                        
                        // Remove matched transactions
                        uart_queue.delete(i);
                        axi_queue.delete(j);
                        break;
                    end else begin
                        mismatch_count++;
                        `uvm_error("SCOREBOARD", $sformatf("Transaction mismatch at ADDR=0x%08X", uart_tr.addr))
                    end
                end
            end
            
            if (match_found) break;
        end
    endfunction
    
    // Verify that UART and AXI transactions match
    virtual function bit verify_transaction_match(uart_frame_transaction uart_tr, axi4_lite_transaction axi_tr);
        bit is_write = !uart_tr.cmd[7]; // RW bit (inverted)
        logic [1:0] size = uart_tr.cmd[5:4];
        logic [3:0] wstrb_expected;
        
        // Check transaction type matches
        if (is_write != axi_tr.is_write) begin
            `uvm_error("SCOREBOARD", "Transaction type mismatch (read/write)")
            return 0;
        end
        
        // Check WSTRB for write transactions
        if (is_write) begin
            wstrb_expected = calculate_expected_wstrb(uart_tr.addr, size);
            if (axi_tr.wstrb != wstrb_expected) begin
                `uvm_error("SCOREBOARD", $sformatf("WSTRB mismatch: expected 0x%X, got 0x%X", 
                          wstrb_expected, axi_tr.wstrb))
                return 0;
            end
            
            // Check write data matches
            if (!verify_write_data(uart_tr, axi_tr)) begin
                return 0;
            end
        end
        
        return 1;
    endfunction
    
    // Calculate expected WSTRB based on address and size
    virtual function logic [3:0] calculate_expected_wstrb(logic [31:0] addr, logic [1:0] size);
        case (size)
            2'b00: return 4'b0001 << addr[1:0];        // 8-bit
            2'b01: return addr[1] ? 4'b1100 : 4'b0011; // 16-bit
            2'b10: return 4'b1111;                     // 32-bit
            default: return 4'b0000;                   // Invalid
        endcase
    endfunction
    
    // Verify write data matches between UART and AXI
    virtual function bit verify_write_data(uart_frame_transaction uart_tr, axi4_lite_transaction axi_tr);
        logic [1:0] size = uart_tr.cmd[5:4];
        logic [31:0] expected_wdata = 0;
        
        // Pack UART data into expected AXI wdata format (little-endian)
        case (size)
            2'b00: begin // 8-bit
                expected_wdata[7:0] = uart_tr.data[0];
            end
            2'b01: begin // 16-bit
                expected_wdata[7:0] = uart_tr.data[0];
                expected_wdata[15:8] = uart_tr.data[1];
            end
            2'b10: begin // 32-bit
                expected_wdata[7:0] = uart_tr.data[0];
                expected_wdata[15:8] = uart_tr.data[1];
                expected_wdata[23:16] = uart_tr.data[2];
                expected_wdata[31:24] = uart_tr.data[3];
            end
        endcase
        
        if (axi_tr.wdata != expected_wdata) begin
            `uvm_error("SCOREBOARD", $sformatf("Write data mismatch: expected 0x%08X, got 0x%08X", 
                      expected_wdata, axi_tr.wdata))
            return 0;
        end
        
        return 1;
    endfunction
    
    // Final phase - report statistics
    virtual function void final_phase(uvm_phase phase);
        `uvm_info("SCOREBOARD", "=== SCOREBOARD FINAL REPORT ===", UVM_LOW)
        `uvm_info("SCOREBOARD", $sformatf("UART transactions received: %0d", uart_transactions_received), UVM_LOW)
        `uvm_info("SCOREBOARD", $sformatf("AXI transactions received: %0d", axi4_lite_transactions_received), UVM_LOW)
        `uvm_info("SCOREBOARD", $sformatf("Matches found: %0d", match_count), UVM_LOW)
        `uvm_info("SCOREBOARD", $sformatf("Mismatches found: %0d", mismatch_count), UVM_LOW)
        `uvm_info("SCOREBOARD", $sformatf("Unmatched UART transactions: %0d", uart_queue.size()), UVM_LOW)
        `uvm_info("SCOREBOARD", $sformatf("Unmatched AXI transactions: %0d", axi_queue.size()), UVM_LOW)
        
        if (mismatch_count > 0) begin
            `uvm_error("SCOREBOARD", "Test failed due to transaction mismatches")
        end
        
        if (uart_queue.size() > 0 || axi_queue.size() > 0) begin
            `uvm_warning("SCOREBOARD", "Unmatched transactions remain in queues")
        end
    endfunction

endclass
