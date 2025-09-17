// UART-AXI4 Bridge Scoreboard
// Target Board: Zybo Z7-20
// Date: July 26, 2025
// Description: UVM scoreboard for checking UART-AXI4 bridge functionality

`ifndef UART_AXI4_SCOREBOARD_SV
`define UART_AXI4_SCOREBOARD_SV

class uart_axi4_scoreboard extends uvm_scoreboard;
    
    // Analysis exports
    uvm_analysis_export #(axi4_lite_transaction) axi_export;
    uvm_analysis_export #(uart_transaction) uart_tx_export;
    uvm_analysis_export #(uart_transaction) uart_rx_export;
    
    // Analysis FIFOs
    uvm_tlm_analysis_fifo #(axi4_lite_transaction) axi_fifo;
    uvm_tlm_analysis_fifo #(uart_transaction) uart_tx_fifo;
    uvm_tlm_analysis_fifo #(uart_transaction) uart_rx_fifo;
    
    // Expected data queues
    bit [7:0] expected_tx_queue[$];
    bit [7:0] expected_rx_queue[$];
    
    // Statistics
    int axi_transactions_received;
    int uart_tx_transactions_received;
    int uart_rx_transactions_received;
    int match_count;
    int mismatches;
    int errors;
    
    // Register shadow model
    typedef struct {
        bit [31:0] control_reg;
        bit [31:0] status_reg;
        bit [31:0] fifo_status;
        bit [31:0] error_status;
        bit [31:0] fifo_thresh;
    } register_model_t;
    
    register_model_t reg_model;
    
    // UVM registration
    `uvm_component_utils(uart_axi4_scoreboard)
    
    // Constructor
    function new(string name = "uart_axi4_scoreboard", uvm_component parent = null);
        super.new(name, parent);
        
        // Initialize statistics
        axi_transactions_received = 0;
        uart_tx_transactions_received = 0;
        uart_rx_transactions_received = 0;
        match_count = 0;
        mismatches = 0;
        errors = 0;
        
        // Initialize register model
        reg_model.control_reg = 32'h00000000;
        reg_model.status_reg = 32'h00000000;
        reg_model.fifo_status = 32'h00000101; // Both FIFOs empty initially
        reg_model.error_status = 32'h00000000;
        reg_model.fifo_thresh = 32'h00200010; // Default thresholds
    endfunction
    
    // Build phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Create analysis exports
        axi_export = new("axi_export", this);
        uart_tx_export = new("uart_tx_export", this);
        uart_rx_export = new("uart_rx_export", this);
        
        // Create analysis FIFOs
        axi_fifo = new("axi_fifo", this);
        uart_tx_fifo = new("uart_tx_fifo", this);
        uart_rx_fifo = new("uart_rx_fifo", this);
    endfunction
    
    // Connect phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect exports to FIFOs
        axi_export.connect(axi_fifo.analysis_export);
        uart_tx_export.connect(uart_tx_fifo.analysis_export);
        uart_rx_export.connect(uart_rx_fifo.analysis_export);
    endfunction
    
    // Run phase
    virtual task run_phase(uvm_phase phase);
        fork
            process_axi_transactions();
            process_uart_tx_transactions();
            process_uart_rx_transactions();
            check_expected_data();
        join
    endtask
    
    // Process AXI4-Lite transactions
    task process_axi_transactions();
        axi4_lite_transaction axi_tr;
        
        forever begin
            axi_fifo.get(axi_tr);
            axi_transactions_received++;
            
            `uvm_info("SCOREBOARD", $sformatf("AXI Transaction: %s", axi_tr.convert2string()), UVM_HIGH)
            
            // Update register model and generate expected UART data
            process_axi_transaction(axi_tr);
        end
    endtask
    
    // Process UART TX transactions
    task process_uart_tx_transactions();
        uart_transaction uart_tr;
        
        forever begin
            uart_tx_fifo.get(uart_tr);
            uart_tx_transactions_received++;
            
            `uvm_info("SCOREBOARD", $sformatf("UART TX: %s", uart_tr.convert2string()), UVM_HIGH)
            
            // Check against expected data
            check_uart_tx_data(uart_tr);
        end
    endtask
    
    // Process UART RX transactions
    task process_uart_rx_transactions();
        uart_transaction uart_tr;
        
        forever begin
            uart_rx_fifo.get(uart_tr);
            uart_rx_transactions_received++;
            
            `uvm_info("SCOREBOARD", $sformatf("UART RX: %s", uart_tr.convert2string()), UVM_HIGH)
            
            // Generate expected AXI read data
            expected_rx_queue.push_back(uart_tr.data);
        end
    endtask
    
    // Process individual AXI transaction
    function void process_axi_transaction(axi4_lite_transaction tr);
        case (tr.addr)
            ADDR_CONTROL_REG: begin
                if (tr.trans_type == axi4_lite_transaction::WRITE) begin
                    reg_model.control_reg = tr.data;
                    `uvm_info("SCOREBOARD", $sformatf("Control register updated: 0x%08h", tr.data), UVM_MEDIUM)
                end
            end
            
            ADDR_TX_DATA_REG: begin
                if (tr.trans_type == axi4_lite_transaction::WRITE) begin
                    // Expect this data to appear on UART TX
                    expected_tx_queue.push_back(tr.data[7:0]);
                    `uvm_info("SCOREBOARD", $sformatf("Expected TX data queued: 0x%02h", tr.data[7:0]), UVM_MEDIUM)
                end
            end
            
            ADDR_RX_DATA_REG: begin
                if (tr.trans_type == axi4_lite_transaction::READ) begin
                    // Check if we have expected RX data
                    if (expected_rx_queue.size() > 0) begin
                        bit [7:0] expected_data = expected_rx_queue.pop_front();
                        if (tr.rdata[7:0] == expected_data) begin
                            match_count++;
                            `uvm_info("SCOREBOARD", $sformatf("RX data match: expected=0x%02h, actual=0x%02h", 
                                     expected_data, tr.rdata[7:0]), UVM_MEDIUM)
                        end else begin
                            mismatches++;
                            `uvm_error("SCOREBOARD", $sformatf("RX data mismatch: expected=0x%02h, actual=0x%02h", 
                                      expected_data, tr.rdata[7:0]))
                        end
                    end
                end
            end
            
            ADDR_FIFO_THRESH: begin
                if (tr.trans_type == axi4_lite_transaction::WRITE) begin
                    reg_model.fifo_thresh = tr.data;
                    `uvm_info("SCOREBOARD", $sformatf("FIFO threshold updated: TX=%0d, RX=%0d", 
                             tr.data[23:16], tr.data[7:0]), UVM_MEDIUM)
                end
            end
            
            default: begin
                if (tr.resp != AXI_RESP_OKAY) begin
                    `uvm_info("SCOREBOARD", $sformatf("Expected error response for invalid address 0x%08h", 
                             tr.addr), UVM_MEDIUM)
                end else begin
                    `uvm_warning("SCOREBOARD", $sformatf("Unexpected OKAY response for address 0x%08h", tr.addr))
                end
            end
        endcase
    endfunction
    
    // Check UART TX data against expected
    function void check_uart_tx_data(uart_transaction tr);
        if (expected_tx_queue.size() > 0) begin
            bit [7:0] expected_data = expected_tx_queue.pop_front();
            if (tr.data == expected_data) begin
                match_count++;
                `uvm_info("SCOREBOARD", $sformatf("TX data match: expected=0x%02h, actual=0x%02h", 
                         expected_data, tr.data), UVM_MEDIUM)
            end else begin
                mismatches++;
                `uvm_error("SCOREBOARD", $sformatf("TX data mismatch: expected=0x%02h, actual=0x%02h", 
                          expected_data, tr.data))
            end
        end else begin
            `uvm_warning("SCOREBOARD", $sformatf("Unexpected UART TX data: 0x%02h", tr.data))
        end
        
        // Check for errors
        if (tr.frame_error || tr.parity_error || tr.overrun_error) begin
            errors++;
            `uvm_info("SCOREBOARD", $sformatf("UART error detected: frame=%b, parity=%b, overrun=%b", 
                     tr.frame_error, tr.parity_error, tr.overrun_error), UVM_MEDIUM)
        end
    endfunction
    
    // Periodic check for expected data
    task check_expected_data();
        forever begin
            #1us;
            
            if (expected_tx_queue.size() > 100) begin
                `uvm_warning("SCOREBOARD", $sformatf("TX queue growing large: %0d entries", expected_tx_queue.size()))
            end
            
            if (expected_rx_queue.size() > 100) begin
                `uvm_warning("SCOREBOARD", $sformatf("RX queue growing large: %0d entries", expected_rx_queue.size()))
            end
        end
    endtask
    
    // Report status
    function void report_status();
        `uvm_info("SCOREBOARD", "=== Scoreboard Status ===", UVM_LOW)
        `uvm_info("SCOREBOARD", $sformatf("AXI transactions: %0d", axi_transactions_received), UVM_LOW)
        `uvm_info("SCOREBOARD", $sformatf("UART TX transactions: %0d", uart_tx_transactions_received), UVM_LOW)
        `uvm_info("SCOREBOARD", $sformatf("UART RX transactions: %0d", uart_rx_transactions_received), UVM_LOW)
        `uvm_info("SCOREBOARD", $sformatf("Data matches: %0d", match_count), UVM_LOW)
        `uvm_info("SCOREBOARD", $sformatf("Data mismatches: %0d", mismatches), UVM_LOW)
        `uvm_info("SCOREBOARD", $sformatf("Errors detected: %0d", errors), UVM_LOW)
        `uvm_info("SCOREBOARD", $sformatf("Pending TX queue: %0d", expected_tx_queue.size()), UVM_LOW)
        `uvm_info("SCOREBOARD", $sformatf("Pending RX queue: %0d", expected_rx_queue.size()), UVM_LOW)
        `uvm_info("SCOREBOARD", "========================", UVM_LOW)
        
        if (mismatches > 0) begin
            `uvm_error("SCOREBOARD", $sformatf("Test failed with %0d mismatches", mismatches))
        end else if (match_count > 0) begin
            `uvm_info("SCOREBOARD", "Test passed - all data matched", UVM_LOW)
        end
    endfunction
    
    // Report phase
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        report_status();
    endfunction

endclass

`endif // UART_AXI4_SCOREBOARD_SV
