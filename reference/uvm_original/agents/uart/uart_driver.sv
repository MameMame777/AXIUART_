// UART UVM Driver
// Target Board: Zybo Z7-20
// Date: July 26, 2025
// Description: UVM driver for UART interface with MXD waveform dump support

`ifndef UART_DRIVER_SV
`define UART_DRIVER_SV

class uart_driver extends uvm_driver #(uart_transaction);
    
    // Virtual interface
    virtual uart_if vif;
    
    // Internal state
    bit [UART_DATA_WIDTH-1:0] tx_shift_reg;
    int tx_bit_count;
    bit tx_active;
    
    // Timing control
    int bit_time_ns;
    
    // UVM registration
    `uvm_component_utils(uart_driver)
    
    // Constructor
    function new(string name = "uart_driver", uvm_component parent = null);
        super.new(name, parent);
        tx_active = 0;
        tx_bit_count = 0;
        // Calculate bit time in nanoseconds for 115200 baud
        bit_time_ns = 1000000000 / UART_BAUD_RATE;
    endfunction
    
    // Build phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual uart_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("NOVIF", "Virtual interface not found")
        end
        
        // Enable MXD waveform dump
        `ifdef DSIM
            $dumpfile("uart_waves.mxd");
            $dumpvars(0, vif);
            `uvm_info("UART_DRV", "MXD waveform dump enabled for UART interface", UVM_LOW)
        `endif
    endfunction
    
    // Run phase
    virtual task run_phase(uvm_phase phase);
        // Initialize UART signals
        initialize_signals();
        
        forever begin
            seq_item_port.get_next_item(req);
            drive_transaction(req);
            seq_item_port.item_done();
        end
    endtask
    
    // Initialize UART signals
    task initialize_signals();
        vif.tx <= 1'b1;      // UART idle state is high
        vif.rts <= 1'b1;     // Ready to send (active low, so 1 means not ready initially)
        @(posedge vif.clk);
        `uvm_info("UART_DRV", "UART signals initialized", UVM_MEDIUM)
    endtask
    
    // Drive transaction
    task drive_transaction(uart_transaction tr);
        case (tr.trans_type)
            uart_transaction::TX: drive_tx(tr);
            uart_transaction::RX: drive_rx_ready(tr);
            default: `uvm_error("UART_DRV", $sformatf("Unknown transaction type: %s", tr.trans_type.name()))
        endcase
    endtask
    
    // Drive TX transaction
    task drive_tx(uart_transaction tr);
        bit [FRAME_BITS-1:0] frame_data;
        int bit_periods;
        
        `uvm_info("UART_DRV", $sformatf("Driving TX: %s", tr.convert2string()), UVM_MEDIUM)
        
        // Handle flow control
        if (tr.use_flow_control) begin
            handle_flow_control(tr);
        end
        
        // Build frame: START + DATA + STOP (no parity)
        frame_data[0] = 1'b0;                    // Start bit
        frame_data[8:1] = tr.data;               // Data bits (LSB first)
        frame_data[9] = tr.frame_error ? 1'b0 : 1'b1;  // Stop bit (with potential error)
        
        // Calculate bit periods with variation
        bit_periods = tr.bit_period;
        
        // Send frame
        for (int i = 0; i < FRAME_BITS; i++) begin
            vif.tx <= frame_data[i];
            repeat(bit_periods) @(posedge vif.clk);
            
            // Add MXD marker for debugging
            `ifdef DSIM
                if (i == 0) $display("UART_TX_START: data=0x%02h at time=%0t", tr.data, $time);
                if (i == FRAME_BITS-1) $display("UART_TX_END: data=0x%02h at time=%0t", tr.data, $time);
            `endif
        end
        
        // Inter-frame gap
        vif.tx <= 1'b1;  // Return to idle
        if (tr.frame_gap > 0) begin
            repeat(tr.frame_gap) @(posedge vif.clk);
        end
        
        `uvm_info("UART_DRV", $sformatf("TX completed: data=0x%02h", tr.data), UVM_HIGH)
    endtask
    
    // Handle flow control
    task handle_flow_control(uart_transaction tr);
        // Set RTS based on transaction
        vif.rts <= ~tr.rts_assert;  // RTS is active low
        
        // Wait for CTS if required
        if (tr.use_flow_control && tr.cts_ready) begin
            // Wait for CTS to be ready (active low)
            wait(vif.cts == 1'b0);
            `uvm_info("UART_DRV", "CTS ready detected", UVM_HIGH)
        end
        
        @(posedge vif.clk);
    endtask
    
    // Drive RX ready signals (for receive operations)
    task drive_rx_ready(uart_transaction tr);
        `uvm_info("UART_DRV", $sformatf("Setting RX ready: %s", tr.convert2string()), UVM_MEDIUM)
        
        // Handle flow control for RX
        if (tr.use_flow_control) begin
            vif.rts <= ~tr.rts_assert;  // Signal readiness to receive
        end
        
        // Small delay to allow RX setup
        repeat(5) @(posedge vif.clk);
    endtask
    
    // Reset response
    virtual task reset_phase(uvm_phase phase);
        super.reset_phase(phase);
        
        // Wait for reset deassertion
        wait(!vif.rst);
        
        // Reinitialize after reset
        initialize_signals();
        
        `uvm_info("UART_DRV", "Driver reset completed", UVM_MEDIUM)
    endtask

endclass

`endif // UART_DRIVER_SV
