
//------------------------------------------------------------------------------
// Simplified UART Driver (UBUS Style)
//------------------------------------------------------------------------------

class uart_driver extends uvm_driver #(uart_transaction);
    
    `uvm_component_utils(uart_driver)
    
    // Virtual interface
    virtual uart_if vif;
    
    // Baud rate timing
    int bit_period_ns = 8680;  // 115200 baud default
    
    function new(string name = "uart_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if (!uvm_config_db#(virtual uart_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("UART_DRIVER", "Failed to get virtual interface")
        end
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        uart_transaction req;
        
        // Initialize signals
        vif.uart_rx = 1'b1;
        vif.uart_cts_n = 1'b0;
        vif.rst = 1'b0;
        vif.rst_n = 1'b1;
        
        forever begin
            seq_item_port.get_next_item(req);
            `uvm_info("UART_DRIVER", $sformatf("Driving: %s", req.convert2string()), UVM_HIGH)
            
            if (req.is_reset) begin
                handle_reset(req);
            end else begin
                drive_transaction(req);
            end
            
            seq_item_port.item_done();
        end
    endtask
    
    // Handle reset transaction
    virtual task handle_reset(uart_transaction trans);
        `uvm_info("UART_DRIVER", $sformatf("Executing reset: %0d cycles", trans.reset_cycles), UVM_MEDIUM)
        
        vif.rst = 1'b1;
        vif.rst_n = 1'b0;
        repeat(trans.reset_cycles) @(posedge vif.clk);
        vif.rst = 1'b0;
        vif.rst_n = 1'b1;
        repeat(10) @(posedge vif.clk);
        
        `uvm_info("UART_DRIVER", "Reset completed", UVM_MEDIUM)
    endtask
    
    // Drive UART frame
    virtual task drive_transaction(uart_transaction trans);
        // Build UART frame (SOF + LENGTH + DATA + CRC)
        bit [7:0] frame[];
        int frame_size = trans.frame_data.size();
        
        frame = new[frame_size + 3];  // SOF + LENGTH + DATA + CRC
        frame[0] = 8'hAA;  // Start of frame
        frame[1] = frame_size[7:0];
        
        for (int i = 0; i < frame_size; i++) begin
            frame[i+2] = trans.frame_data[i];
        end
        
        // Simple CRC (XOR of all bytes)
        frame[frame_size+2] = 8'h00;
        for (int i = 0; i < frame_size+2; i++) begin
            frame[frame_size+2] ^= frame[i];
        end
        
        // Send frame
        foreach (frame[i]) begin
            send_uart_byte(frame[i]);
        end
        
        // Inter-frame gap
        repeat(10) @(posedge vif.clk);
    endtask
    
    // Send one UART byte (8N1 format)
    virtual task send_uart_byte(bit [7:0] data);
        // Start bit
        vif.uart_rx = 1'b0;
        #bit_period_ns;
        
        // Data bits (LSB first)
        for (int i = 0; i < 8; i++) begin
            vif.uart_rx = data[i];
            #bit_period_ns;
        end
        
        // Stop bit
        vif.uart_rx = 1'b1;
        #bit_period_ns;
    endtask
    
endclass
