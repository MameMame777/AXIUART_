// UART UVM Monitor
// Target Board: Zybo Z7-20
// Date: July 26, 2025
// Description: UVM monitor for UART interface with MXD waveform dump support

`ifndef UART_MONITOR_SV
`define UART_MONITOR_SV

class uart_monitor extends uvm_monitor;
    
    // Virtual interface
    virtual uart_if vif;
    
    // Analysis ports
    uvm_analysis_port #(uart_transaction) tx_ap;
    uvm_analysis_port #(uart_transaction) rx_ap;
    
    // Coverage
    uart_transaction tr_cov;
    
    // Coverage group
    covergroup uart_cg;
        option.per_instance = 1;
        
        trans_type_cp: coverpoint tr_cov.trans_type {
            bins tx = {uart_transaction::TX};
            bins rx = {uart_transaction::RX};
        }
        
        data_cp: coverpoint tr_cov.data {
            bins ascii_ctrl    = {[8'h00:8'h1F]};
            bins ascii_print   = {[8'h20:8'h7E]};
            bins ascii_ext     = {[8'h7F:8'hFF]};
            bins common_chars  = {8'h0A, 8'h0D, 8'h20, 8'h00};  // LF, CR, SPACE, NULL
        }
        
        error_cp: coverpoint {tr_cov.parity_error, tr_cov.frame_error, tr_cov.overrun_error} {
            bins no_error    = {3'b000};
            bins parity_err  = {3'b100};
            bins frame_err   = {3'b010};
            bins overrun_err = {3'b001};
            bins multiple_err = {3'b011, 3'b101, 3'b110, 3'b111};
        }
        
        flow_control_cp: coverpoint {tr_cov.use_flow_control, tr_cov.rts_assert, tr_cov.cts_ready} {
            bins no_flow_ctrl = {3'b0xx};
            bins flow_ctrl_ok = {3'b111};
            bins rts_not_ready = {3'b101, 3'b100};
            bins cts_not_ready = {3'b110};
        }
        
        // Cross coverage
        data_error_cross: cross data_cp, error_cp;
        trans_flow_cross: cross trans_type_cp, flow_control_cp;
    endgroup
    
    // UVM registration
    `uvm_component_utils(uart_monitor)
    
    // Constructor
    function new(string name = "uart_monitor", uvm_component parent = null);
        super.new(name, parent);
        tx_ap = new("tx_ap", this);
        rx_ap = new("rx_ap", this);
        uart_cg = new();
    endfunction
    
    // Build phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual uart_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("NOVIF", "Virtual interface not found")
        end
        
        // Enable MXD waveform dump
        `ifdef DSIM
            $dumpfile("uart_monitor_waves.mxd");
            $dumpvars(0, vif);
            `uvm_info("UART_MON", "MXD waveform dump enabled for UART monitor", UVM_LOW)
        `endif
    endfunction
    
    // Run phase
    virtual task run_phase(uvm_phase phase);
        fork
            monitor_tx();
            monitor_rx();
            monitor_flow_control();
        join
    endtask
    
    // Monitor TX line
    task monitor_tx();
        uart_transaction tr;
        bit [UART_DATA_WIDTH-1:0] data;
        bit start_detected;
        bit frame_error;
        int bit_count;
        time start_time, bit_time;
        
        forever begin
            // Wait for start bit (high to low transition)
            @(negedge vif.tx);
            start_time = $time;
            start_detected = 1;
            frame_error = 0;
            bit_count = 0;
            data = 8'h00;
            
            `ifdef DSIM
                $display("UART_TX_MONITOR: Start bit detected at time=%0t", $time);
            `endif
            
            // Sample start bit in the middle
            #(bit_time_ns()/2);
            if (vif.tx !== 1'b0) begin
                `uvm_warning("UART_MON", "Invalid start bit detected")
                continue;
            end
            
            // Sample data bits
            for (int i = 0; i < DATA_BITS; i++) begin
                #(bit_time_ns());
                data[i] = vif.tx;
                bit_count++;
                
                `ifdef DSIM
                    $display("UART_TX_MONITOR: Bit[%0d]=%b at time=%0t", i, vif.tx, $time);
                `endif
            end
            
            // Sample stop bit
            #(bit_time_ns());
            if (vif.tx !== 1'b1) begin
                frame_error = 1;
                `uvm_warning("UART_MON", $sformatf("Frame error detected: stop bit = %b", vif.tx))
            end
            
            // Create transaction
            tr = uart_transaction::type_id::create("uart_tx_tr");
            tr.trans_type = uart_transaction::TX;
            tr.data = data;
            tr.frame_error = frame_error;
            tr.parity_error = 0;  // No parity in this implementation
            tr.overrun_error = 0; // Detected at higher level
            
            // Check flow control state
            tr.use_flow_control = (vif.rts == 1'b0);  // RTS active low
            tr.rts_assert = (vif.rts == 1'b0);
            tr.cts_ready = (vif.cts == 1'b0);         // CTS active low
            
            // Send to analysis port and update coverage
            tx_ap.write(tr);
            tr_cov = tr;
            uart_cg.sample();
            
            `uvm_info("UART_MON", $sformatf("TX monitored: %s", tr.convert2string()), UVM_HIGH)
            
            `ifdef DSIM
                $display("UART_TX_MONITOR: Frame complete - data=0x%02h, errors(f=%b) at time=%0t", 
                        data, frame_error, $time);
            `endif
        end
    endtask
    
    // Monitor RX line
    task monitor_rx();
        uart_transaction tr;
        bit [UART_DATA_WIDTH-1:0] data;
        bit frame_error;
        int bit_count;
        time start_time;
        
        forever begin
            // Wait for start bit on RX
            @(negedge vif.rx);
            start_time = $time;
            frame_error = 0;
            bit_count = 0;
            data = 8'h00;
            
            `ifdef DSIM
                $display("UART_RX_MONITOR: Start bit detected at time=%0t", $time);
            `endif
            
            // Sample start bit in the middle
            #(bit_time_ns()/2);
            if (vif.rx !== 1'b0) begin
                `uvm_warning("UART_MON", "Invalid RX start bit detected")
                continue;
            end
            
            // Sample data bits
            for (int i = 0; i < DATA_BITS; i++) begin
                #(bit_time_ns());
                data[i] = vif.rx;
                bit_count++;
                
                `ifdef DSIM
                    $display("UART_RX_MONITOR: Bit[%0d]=%b at time=%0t", i, vif.rx, $time);
                `endif
            end
            
            // Sample stop bit
            #(bit_time_ns());
            if (vif.rx !== 1'b1) begin
                frame_error = 1;
                `uvm_warning("UART_MON", $sformatf("RX Frame error: stop bit = %b", vif.rx))
            end
            
            // Create transaction
            tr = uart_transaction::type_id::create("uart_rx_tr");
            tr.trans_type = uart_transaction::RX;
            tr.data = data;
            tr.frame_error = frame_error;
            tr.parity_error = 0;
            tr.overrun_error = 0;
            
            // Check flow control state
            tr.use_flow_control = (vif.rts == 1'b0);
            tr.rts_assert = (vif.rts == 1'b0);
            tr.cts_ready = (vif.cts == 1'b0);
            
            // Send to analysis port and update coverage
            rx_ap.write(tr);
            tr_cov = tr;
            uart_cg.sample();
            
            `uvm_info("UART_MON", $sformatf("RX monitored: %s", tr.convert2string()), UVM_HIGH)
            
            `ifdef DSIM
                $display("UART_RX_MONITOR: Frame complete - data=0x%02h, errors(f=%b) at time=%0t", 
                        data, frame_error, $time);
            `endif
        end
    endtask
    
    // Monitor flow control signals
    task monitor_flow_control();
        bit prev_rts, prev_cts;
        
        forever begin
            @(vif.rts, vif.cts);
            
            if (vif.rts !== prev_rts) begin
                `uvm_info("UART_MON", $sformatf("RTS changed: %b -> %b at time=%0t", 
                         prev_rts, vif.rts, $time), UVM_MEDIUM)
                prev_rts = vif.rts;
                
                `ifdef DSIM
                    $display("UART_FLOW: RTS=%b at time=%0t", vif.rts, $time);
                `endif
            end
            
            if (vif.cts !== prev_cts) begin
                `uvm_info("UART_MON", $sformatf("CTS changed: %b -> %b at time=%0t", 
                         prev_cts, vif.cts, $time), UVM_MEDIUM)
                prev_cts = vif.cts;
                
                `ifdef DSIM
                    $display("UART_FLOW: CTS=%b at time=%0t", vif.cts, $time);
                `endif
            end
        end
    endtask
    
    // Calculate bit time in ns
    function int bit_time_ns();
        return 1000000000 / UART_BAUD_RATE;
    endfunction
    
    // Report phase
    virtual function void report_phase(uvm_phase phase);
        `uvm_info("UART_MON", $sformatf("UART Coverage: %.2f%%", uart_cg.get_coverage()), UVM_LOW)
    endfunction

endclass

`endif // UART_MONITOR_SV
