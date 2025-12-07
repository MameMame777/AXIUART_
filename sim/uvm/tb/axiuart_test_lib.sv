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
