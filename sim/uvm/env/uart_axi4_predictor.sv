`timescale 1ns / 1ps

// UVM Predictor for UART-AXI4 Bridge
// Generates expected transactions based on stimulus to compare with actual results

class uart_axi4_predictor extends uvm_component;
    
    `uvm_component_utils(uart_axi4_predictor)
    
    // Configuration
    uart_axi4_env_config cfg;
    
    // Analysis ports for receiving stimulus
    `uvm_analysis_imp_decl(_uart_stim)
    `uvm_analysis_imp_decl(_axi_stim)
    uvm_analysis_imp_uart_stim #(uart_frame_transaction, uart_axi4_predictor) uart_stim_imp;
    uvm_analysis_imp_axi_stim #(axi4_lite_transaction, uart_axi4_predictor) axi_stim_imp;
    
    // Analysis ports for sending expected transactions
    uvm_analysis_port #(uart_frame_transaction) uart_expected_port;
    uvm_analysis_port #(axi4_lite_transaction) axi_expected_port;
    
    function new(string name = "uart_axi4_predictor", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Create analysis imports for receiving stimulus
        uart_stim_imp = new("uart_stim_imp", this);
        axi_stim_imp = new("axi_stim_imp", this);
        
        // Create analysis ports for sending predictions
        uart_expected_port = new("uart_expected_port", this);
        axi_expected_port = new("axi_expected_port", this);
        
        // Get configuration
        if (!uvm_config_db#(uart_axi4_env_config)::get(this, "", "cfg", cfg)) begin
            `uvm_warning("PREDICTOR", "No configuration found, using defaults")
        end
    endfunction
    
    // Predict expected AXI transaction from UART stimulus
    virtual function void write_uart_stim(uart_frame_transaction uart_tr);
        axi4_lite_transaction expected_axi;
        
        `uvm_info("PREDICTOR", $sformatf("Predicting AXI from UART: CMD=0x%02X, ADDR=0x%08X", 
                  uart_tr.cmd, uart_tr.addr), UVM_DEBUG)
        
        // Create expected AXI transaction based on UART command
        expected_axi = axi4_lite_transaction::type_id::create("expected_axi");
        
        // Map UART frame to AXI transaction
        expected_axi.addr = uart_tr.addr;
        expected_axi.write = (uart_tr.cmd == 8'h01); // Assuming 0x01 is write command
        
        if (expected_axi.write) begin
            // For write transactions, predict data from UART payload
            if (uart_tr.data.size() >= 4) begin
                expected_axi.wdata = {uart_tr.data[3], uart_tr.data[2], uart_tr.data[1], uart_tr.data[0]};
                expected_axi.wstrb = 4'hF; // All bytes valid
            end else begin
                // Partial write - adjust strobe based on data size
                expected_axi.wdata = 0;
                expected_axi.wstrb = 0;
                for (int i = 0; i < uart_tr.data.size(); i++) begin
                    expected_axi.wdata |= (uart_tr.data[i] << (i * 8));
                    expected_axi.wstrb |= (1 << i);
                end
            end
        end else begin
            // Read transaction
            expected_axi.wdata = 0;
            expected_axi.wstrb = 4'h0;
        end
        
        // Send expected AXI transaction to scoreboard
        axi_expected_port.write(expected_axi);
        
        `uvm_info("PREDICTOR", $sformatf("Predicted AXI: ADDR=0x%08X, %s, WDATA=0x%08X", 
                  expected_axi.addr, expected_axi.write ? "WRITE" : "READ", expected_axi.wdata), UVM_DEBUG)
    endfunction
    
    // Predict expected UART response from AXI stimulus (for responses)
    virtual function void write_axi_stim(axi4_lite_transaction axi_tr);
        uart_frame_transaction expected_uart;
        
        `uvm_info("PREDICTOR", $sformatf("Predicting UART from AXI: ADDR=0x%08X, %s", 
                  axi_tr.addr, axi_tr.write ? "WRITE" : "READ"), UVM_DEBUG)
        
        // For read transactions, predict UART response frame
        if (!axi_tr.write) begin
            expected_uart = uart_frame_transaction::type_id::create("expected_uart");
            expected_uart.cmd = 8'h02; // Assuming 0x02 is read response
            expected_uart.addr = axi_tr.addr;
            expected_uart.len = 4; // 32-bit read
            
            // For this predictor, we assume the read data will be available
            // In a real implementation, this would be more sophisticated
            expected_uart.data = new[4];
            expected_uart.data[0] = axi_tr.rdata[7:0];
            expected_uart.data[1] = axi_tr.rdata[15:8];
            expected_uart.data[2] = axi_tr.rdata[23:16];
            expected_uart.data[3] = axi_tr.rdata[31:24];
            
            // Send expected UART transaction to scoreboard
            uart_expected_port.write(expected_uart);
            
            `uvm_info("PREDICTOR", $sformatf("Predicted UART response: CMD=0x%02X, ADDR=0x%08X, LEN=%0d", 
                      expected_uart.cmd, expected_uart.addr, expected_uart.len), UVM_DEBUG)
        end
    endfunction
    
endclass