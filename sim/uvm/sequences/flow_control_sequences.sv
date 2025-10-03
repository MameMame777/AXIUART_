`timescale 1ns / 1ps

// Flow Control Sequences for RTS/CTS Hardware Flow Control Testing
// These sequences test the PMOD-compliant 4-wire UART implementation

// Basic RTS monitoring sequence
class uart_rts_monitor_sequence extends uvm_sequence #(uart_frame_transaction);
    `uvm_object_utils(uart_rts_monitor_sequence)
    
    function new(string name = "uart_rts_monitor_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction req;
        
        `uvm_info("RTS_MONITOR_SEQ", "Starting RTS monitoring sequence", UVM_MEDIUM);
        
        // Create multiple write transactions to fill RX FIFO
        for (int i = 0; i < 10; i++) begin
            req = uart_frame_transaction::type_id::create("req");
            start_item(req);
            
            // Write to test register
            if (!req.randomize() with {
                cmd == WRITE_CMD;
                addr == TEST_REG_ADDR;
                data.size() == 4;
            }) begin
                `uvm_fatal("RTS_MONITOR_SEQ", "Failed to randomize transaction");
            end
            
            `uvm_info("RTS_MONITOR_SEQ", $sformatf("Write transaction %0d to fill FIFO", i), UVM_MEDIUM);
            finish_item(req);
            
            // Small delay between transactions
            #1000ns;
        end
        
        `uvm_info("RTS_MONITOR_SEQ", "RTS monitoring sequence completed", UVM_MEDIUM);
    endtask
endclass

// CTS flow control sequence
class uart_cts_flow_control_sequence extends uvm_sequence #(uart_frame_transaction);
    `uvm_object_utils(uart_cts_flow_control_sequence)
    
    int backpressure_cycles = 1000;
    
    function new(string name = "uart_cts_flow_control_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction req;
        
        `uvm_info("CTS_FLOW_SEQ", "Starting CTS flow control sequence", UVM_MEDIUM);
        
        // Start a read transaction that will trigger TX response
        req = uart_frame_transaction::type_id::create("req");
        start_item(req);
        
        if (!req.randomize() with {
            cmd == READ_CMD;
            addr == TEST_REG_ADDR;
        }) begin
            `uvm_fatal("CTS_FLOW_SEQ", "Failed to randomize transaction");
        end
        
        `uvm_info("CTS_FLOW_SEQ", "Initiating read transaction", UVM_MEDIUM);
        finish_item(req);
        
        `uvm_info("CTS_FLOW_SEQ", "CTS flow control sequence completed", UVM_MEDIUM);
    endtask
endclass

// Combined RTS/CTS stress test sequence
class uart_flow_control_stress_sequence extends uvm_sequence #(uart_frame_transaction);
    `uvm_object_utils(uart_flow_control_stress_sequence)
    
    int num_transactions = 20;
    
    function new(string name = "uart_flow_control_stress_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction req;
        
        `uvm_info("FLOW_STRESS_SEQ", "Starting flow control stress sequence", UVM_MEDIUM);
        
        // Generate mixed read/write transactions to stress flow control
        for (int i = 0; i < num_transactions; i++) begin
            req = uart_frame_transaction::type_id::create("req");
            start_item(req);
            
            // Randomize between read and write
            if (!req.randomize() with {
                cmd inside {READ_CMD, WRITE_CMD};
                addr inside {TEST_REG_ADDR, STATUS_REG_ADDR, FIFO_STATUS_REG_ADDR};
                if (cmd == WRITE_CMD) {
                    data.size() inside {1, 2, 4};
                }
            }) begin
                `uvm_fatal("FLOW_STRESS_SEQ", "Failed to randomize transaction");
            end
            
            `uvm_info("FLOW_STRESS_SEQ", $sformatf("Transaction %0d: %s to 0x%08X", 
                      i, (req.cmd == READ_CMD) ? "READ" : "WRITE", req.addr), UVM_MEDIUM);
            
            finish_item(req);
            
            // Variable delay between transactions to create different flow patterns
            #($urandom_range(500, 2000) * 1ns);
        end
        
        `uvm_info("FLOW_STRESS_SEQ", "Flow control stress sequence completed", UVM_MEDIUM);
    endtask
endclass