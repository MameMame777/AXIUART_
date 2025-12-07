
//------------------------------------------------------------------------------
// Simplified AXIUART Scoreboard (UBUS Style)
//------------------------------------------------------------------------------

class axiuart_scoreboard extends uvm_scoreboard;
    
    `uvm_component_utils(axiuart_scoreboard)
    
    // Analysis exports
    uvm_analysis_export #(uart_transaction) uart_export;
    uvm_analysis_export #(uart_transaction) axi_export;
    
    // FIFOs
    uvm_tlm_analysis_fifo #(uart_transaction) uart_fifo;
    uvm_tlm_analysis_fifo #(uart_transaction) axi_fifo;
    
    // Statistics
    int match_count;
    int mismatch_count;
    
    function new(string name = "axiuart_scoreboard", uvm_component parent = null);
        super.new(name, parent);
        match_count = 0;
        mismatch_count = 0;
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        uart_export = new("uart_export", this);
        axi_export = new("axi_export", this);
        
        uart_fifo = new("uart_fifo", this);
        axi_fifo = new("axi_fifo", this);
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        uart_export.connect(uart_fifo.analysis_export);
        axi_export.connect(axi_fifo.analysis_export);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        uart_transaction uart_trans, axi_trans;
        
        forever begin
            fork
                uart_fifo.get(uart_trans);
                axi_fifo.get(axi_trans);
            join
            
            compare_transactions(uart_trans, axi_trans);
        end
    endtask
    
    // Compare UART and AXI transactions
    virtual function void compare_transactions(uart_transaction uart_trans, uart_transaction axi_trans);
        if (uart_trans.address == axi_trans.address && uart_trans.data == axi_trans.data) begin
            match_count++;
            `uvm_info("SCOREBOARD", $sformatf("MATCH: ADDR=0x%08h DATA=0x%08h", 
                     uart_trans.address, uart_trans.data), UVM_MEDIUM)
        end else begin
            mismatch_count++;
            `uvm_error("SCOREBOARD", $sformatf("MISMATCH: UART[ADDR=0x%08h DATA=0x%08h] vs AXI[ADDR=0x%08h DATA=0x%08h]",
                      uart_trans.address, uart_trans.data, axi_trans.address, axi_trans.data))
        end
    endfunction
    
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        
        `uvm_info("SCOREBOARD", $sformatf("Final Results: MATCHES=%0d MISMATCHES=%0d", match_count, mismatch_count), UVM_LOW)
        
        if (mismatch_count == 0) begin
            `uvm_info("SCOREBOARD", "*** TEST PASSED ***", UVM_LOW)
        end else begin
            `uvm_error("SCOREBOARD", "*** TEST FAILED ***")
        end
    endfunction
    
endclass
