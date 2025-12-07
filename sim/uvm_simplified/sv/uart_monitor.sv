
//------------------------------------------------------------------------------
// Simplified UART Monitor (UBUS Style)
//------------------------------------------------------------------------------

class uart_monitor extends uvm_monitor;
    
    `uvm_component_utils(uart_monitor)
    
    // Virtual interface
    virtual uart_if vif;
    
    // Analysis port
    uvm_analysis_port #(uart_transaction) item_collected_port;
    
    function new(string name = "uart_monitor", uvm_component parent = null);
        super.new(name, parent);
        item_collected_port = new("item_collected_port", this);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if (!uvm_config_db#(virtual uart_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("UART_MONITOR", "Failed to get virtual interface")
        end
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        uart_transaction trans;
        
        forever begin
            // Wait for UART activity and collect transaction
            trans = uart_transaction::type_id::create("trans");
            collect_transaction(trans);
            
            // Only broadcast if we got a valid transaction
            if (trans.frame_data.size() > 0) begin
                item_collected_port.write(trans);
                `uvm_info("UART_MONITOR", $sformatf("Collected: %s", trans.convert2string()), UVM_DEBUG)
            end
        end
    endtask
    
    // Simple frame collection
    virtual task collect_transaction(uart_transaction trans);
        bit [7:0] byte_data;
        bit [7:0] temp_byte;
        int frame_size;
        
        // Wait for start of frame (0xAA) - loop until found
        do begin
            wait_for_byte(temp_byte);
        end while (temp_byte != 8'hAA);
        
        // Get length byte
        wait_for_byte(temp_byte);
        frame_size = temp_byte;
        
        // Collect frame data
        trans.frame_data = new[frame_size];
        for (int i = 0; i < frame_size; i++) begin
            wait_for_byte(temp_byte);
            trans.frame_data[i] = temp_byte;
        end
        
        // Extract address and data from frame (AXIUART protocol)
        if (frame_size >= 8) begin
            trans.address = {trans.frame_data[0], trans.frame_data[1], 
                           trans.frame_data[2], trans.frame_data[3]};
            trans.data = {trans.frame_data[4], trans.frame_data[5],
                         trans.frame_data[6], trans.frame_data[7]};
        end
    endtask
    
    // Wait for one UART byte
    virtual task wait_for_byte(output bit [7:0] data);
        // Simplified: wait for RX valid and capture data
        @(posedge vif.clk);
        while (!vif.rx_valid) @(posedge vif.clk);
        data = vif.rx_data;
    endtask
    
endclass
