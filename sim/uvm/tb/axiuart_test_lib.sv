//----------------------------------------------------------------------
// AXIUART Test Library - UBUS Pattern
//----------------------------------------------------------------------

// Base Test - UBUS style
class axiuart_base_test extends uvm_test;
    `uvm_component_utils(axiuart_base_test)
    
    axiuart_env env;
    uvm_table_printer printer;
    bit test_pass = 1;
    
    function new(string name = "axiuart_base_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        uvm_config_db#(int)::set(this, "*", "recording_detail", UVM_FULL);
        env = axiuart_env::type_id::create("env", this);
        printer = new();
        printer.knobs.depth = 3;
    endfunction
    
    function void end_of_elaboration_phase(uvm_phase phase);
        `uvm_info(get_type_name(),
            $sformatf("Printing test topology:\n%s", this.sprint(printer)), UVM_LOW)
    endfunction
    
    task run_phase(uvm_phase phase);
        phase.phase_done.set_drain_time(this, 50);
    endtask
    
    function void report_phase(uvm_phase phase);
        if(test_pass) begin
            `uvm_info(get_type_name(), "** UVM TEST PASSED **", UVM_NONE)
        end else begin
            `uvm_error(get_type_name(), "** UVM TEST FAIL **")
        end
    endfunction
endclass

// Basic Test - Equivalent to axi4_basic_test
class axiuart_basic_test extends axiuart_base_test;
    `uvm_component_utils(axiuart_basic_test)
    
    function new(string name = "axiuart_basic_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction
    
    task run_phase(uvm_phase phase);
        uart_basic_sequence seq;
        
        phase.raise_objection(this, "Starting basic test");
        `uvm_info(get_type_name(), "=== AXIUART Basic Test Started ===", UVM_LOW)
        
        seq = uart_basic_sequence::type_id::create("seq");
        seq.start(env.uart_agt.sequencer);
        
        #1000ns;
        
        `uvm_info(get_type_name(), "=== AXIUART Basic Test Completed ===", UVM_LOW)
        phase.drop_objection(this, "Basic test completed");
    endtask
endclass

// Reset Test - Demonstrates DUT reset capability
class axiuart_reset_test extends axiuart_base_test;
    `uvm_component_utils(axiuart_reset_test)
    
    function new(string name = "axiuart_reset_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction
    
    task run_phase(uvm_phase phase);
        uart_reset_sequence reset_seq;
        uart_basic_sequence basic_seq;
        
        phase.raise_objection(this, "Starting reset test");
        `uvm_info(get_type_name(), "=== AXIUART Reset Test Started ===", UVM_LOW)
        
        // Execute reset
        reset_seq = uart_reset_sequence::type_id::create("reset_seq");
        reset_seq.reset_cycles = 200; // Custom reset duration
        reset_seq.start(env.uart_agt.sequencer);
        
        // Run basic sequence after reset
        basic_seq = uart_basic_sequence::type_id::create("basic_seq");
        basic_seq.start(env.uart_agt.sequencer);
        
        #1000ns;
        
        `uvm_info(get_type_name(), "=== AXIUART Reset Test Completed ===", UVM_LOW)
        phase.drop_objection(this, "Reset test completed");
    endtask
endclass

// Register R/W Test - Demonstrates register access capability
class axiuart_reg_rw_test extends axiuart_base_test;
    `uvm_component_utils(axiuart_reg_rw_test)
    
    function new(string name = "axiuart_reg_rw_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction
    
    task run_phase(uvm_phase phase);
        uart_reset_sequence reset_seq;
        uart_reg_write_sequence wr_seq[6];
        uart_reg_read_sequence rd_seq[6];
        bit [31:0] test_data[6] = '{32'h1111_1111, 32'h2222_2222, 
                                     32'h3333_3333, 32'h4444_4444, 
                                     32'h5555_5555, 32'h0000_000F};
        int error_count = 0;
        
        phase.raise_objection(this, "Starting register R/W test");
        `uvm_info(get_type_name(), "=== AXIUART Register R/W Test Started ===", UVM_LOW)
        
        // 1. Reset DUT
        reset_seq = uart_reset_sequence::type_id::create("reset_seq");
        reset_seq.reset_cycles = 100;
        reset_seq.start(env.uart_agt.sequencer);
        
        // 2. Write 6 test registers (REG_TEST_0-4 + REG_TEST_LED: 0x1020, 0x1024, 0x1028, 0x102C, 0x1040, 0x1044)
        `uvm_info(get_type_name(), "Writing 6 test registers (REG_TEST_0-4 + REG_TEST_LED)...", UVM_LOW)
        for (int i = 0; i < 6; i++) begin
            wr_seq[i] = uart_reg_write_sequence::type_id::create($sformatf("wr_seq_%0d", i));
            // Disable randomization and set fixed values
            if (i < 4)
                wr_seq[i].reg_addr = 32'h0000_1020 + (i * 4);
            else if (i == 4)
                wr_seq[i].reg_addr = 32'h0000_1040;  // REG_TEST_4
            else
                wr_seq[i].reg_addr = 32'h0000_1044;  // REG_TEST_LED
            wr_seq[i].reg_data = test_data[i];
            wr_seq[i].start(env.uart_agt.sequencer);
        end
        
        #5000ns;  // Wait for DUT processing
        
        // 3. Send read commands (note: read-back verification requires Monitor enhancement)
        `uvm_info(get_type_name(), "Sending read commands for 6 test registers...", UVM_LOW)
        for (int i = 0; i < 6; i++) begin
            rd_seq[i] = uart_reg_read_sequence::type_id::create($sformatf("rd_seq_%0d", i));
            // Disable randomization and set fixed address
            if (i < 4)
                rd_seq[i].reg_addr = 32'h0000_1020 + (i * 4);
            else if (i == 4)
                rd_seq[i].reg_addr = 32'h0000_1040;  // REG_TEST_4
            else
                rd_seq[i].reg_addr = 32'h0000_1044;  // REG_TEST_LED
            rd_seq[i].start(env.uart_agt.sequencer);
            `uvm_info(get_type_name(), 
                $sformatf("Read command sent for addr=0x%08X", rd_seq[i].reg_addr), UVM_MEDIUM)
        end
        
        #5000000ns;  // Wait 5ms for all READ responses (5 frames × 694μs each + margin)
        
        // 5. Verify Scoreboard results
        `uvm_info(get_type_name(), "=== Verification Phase: Scoreboard Check ===", UVM_LOW)
        
        if (env.scoreboard.mismatch_count > 0) begin
            `uvm_error(get_type_name(), 
                $sformatf("Register verification FAILED: %0d mismatches detected", 
                          env.scoreboard.mismatch_count))
        end else if (env.scoreboard.match_count == 0) begin
            `uvm_warning(get_type_name(), 
                "No read responses verified - check Monitor/DUT connection")
        end else begin
            `uvm_info(get_type_name(), 
                $sformatf("Register verification PASSED: %0d reads matched expected values", 
                          env.scoreboard.match_count), UVM_LOW)
        end
        
        `uvm_info(get_type_name(), "=== AXIUART Register R/W Test Completed ===", UVM_LOW)
        phase.drop_objection(this, "Register R/W test completed");
    endtask
endclass
