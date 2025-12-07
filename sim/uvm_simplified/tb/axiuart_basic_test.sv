
//------------------------------------------------------------------------------
// Basic Test for AXIUART (UBUS Style)
//------------------------------------------------------------------------------

class axiuart_basic_test extends uvm_test;
    
    `uvm_component_utils(axiuart_basic_test)
    
    axiuart_env env;
    
    function new(string name = "axiuart_basic_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = axiuart_env::type_id::create("env", this);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        axiuart_reset_sequence reset_seq;
        axiuart_write_sequence write_seq;
        
        phase.raise_objection(this);
        
        `uvm_info("TEST", "===============================================", UVM_LOW)
        `uvm_info("TEST", "     AXIUART BASIC TEST (Simplified)", UVM_LOW)
        `uvm_info("TEST", "===============================================", UVM_LOW)
        
        // Wait for clock stabilization
        repeat(2) @(posedge env.uart_agt.driver.vif.clk);
        
        // Step 1: Reset DUT
        `uvm_info("TEST", "Executing DUT reset", UVM_MEDIUM)
        reset_seq = axiuart_reset_sequence::type_id::create("reset_seq");
        reset_seq.reset_cycles = 100;
        reset_seq.start(env.uart_agt.sequencer);
        `uvm_info("TEST", "Reset completed", UVM_MEDIUM)
        
        // Step 2: Execute write transactions
        `uvm_info("TEST", "Starting write sequence", UVM_MEDIUM)
        write_seq = axiuart_write_sequence::type_id::create("write_seq");
        write_seq.num_transactions = 5;
        write_seq.start(env.uart_agt.sequencer);
        `uvm_info("TEST", "Write sequence completed", UVM_MEDIUM)
        
        // Wait for processing
        #10us;
        
        `uvm_info("TEST", "Test completed", UVM_LOW)
        `uvm_info("TEST", "===============================================", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass

//------------------------------------------------------------------------------
// Reset Sequence
//------------------------------------------------------------------------------

class axiuart_reset_sequence extends uvm_sequence #(uart_transaction);
    
    `uvm_object_utils(axiuart_reset_sequence)
    
    int reset_cycles = 100;
    
    function new(string name = "axiuart_reset_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_transaction req;
        
        `uvm_info("RESET_SEQ", $sformatf("Starting reset: %0d cycles", reset_cycles), UVM_MEDIUM)
        
        req = uart_transaction::type_id::create("reset_req");
        start_item(req);
        req.is_reset = 1;
        req.reset_cycles = this.reset_cycles;
        finish_item(req);
        
        `uvm_info("RESET_SEQ", "Reset completed", UVM_MEDIUM)
    endtask
    
endclass

//------------------------------------------------------------------------------
// Write Sequence
//------------------------------------------------------------------------------

class axiuart_write_sequence extends uvm_sequence #(uart_transaction);
    
    `uvm_object_utils(axiuart_write_sequence)
    
    int num_transactions = 5;
    
    function new(string name = "axiuart_write_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_transaction trans;
        
        `uvm_info("WRITE_SEQ", $sformatf("Starting %0d write transactions", num_transactions), UVM_MEDIUM)
        
        repeat(num_transactions) begin
            trans = uart_transaction::type_id::create("trans");
            
            start_item(trans);
            assert(trans.randomize() with {
                is_read == 0;
                is_reset == 0;
                address inside {32'h0000, 32'h0004, 32'h0008, 32'h000C};
                data inside {[32'h00000001:32'h000000FF]};
            });
            
            // Build UART frame manually (CMD + ADDR + DATA)
            trans.frame_data = new[9];
            trans.frame_data[0] = 8'h02;  // Write command
            trans.frame_data[1] = trans.address[31:24];
            trans.frame_data[2] = trans.address[23:16];
            trans.frame_data[3] = trans.address[15:8];
            trans.frame_data[4] = trans.address[7:0];
            trans.frame_data[5] = trans.data[31:24];
            trans.frame_data[6] = trans.data[23:16];
            trans.frame_data[7] = trans.data[15:8];
            trans.frame_data[8] = trans.data[7:0];
            
            finish_item(trans);
            
            `uvm_info("WRITE_SEQ", $sformatf("Sent: ADDR=0x%08h DATA=0x%08h", 
                     trans.address, trans.data), UVM_MEDIUM)
        end
        
        `uvm_info("WRITE_SEQ", "All write transactions completed", UVM_MEDIUM)
    endtask
    
endclass
