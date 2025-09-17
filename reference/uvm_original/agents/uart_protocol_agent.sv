/*
 * UVM Agent and Environment Classes for UART Protocol Testing
 * Purpose: Complete UVM environment with Agent/Environment hierarchy
 * Features: UVM-1.2 compliant architecture following best practices
 */

// UART Protocol Agent
class uart_protocol_agent extends uvm_agent;
    `uvm_component_utils(uart_protocol_agent)
    
    // Agent components
    uart_protocol_driver    driver;
    uart_protocol_monitor   monitor;
    uvm_sequencer #(uart_protocol_transaction) sequencer;
    
    // Configuration
    bit is_active = UVM_ACTIVE;
    
    // Constructor
    function new(string name = "uart_protocol_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        if (!uvm_config_db#(bit)::get(this, "", "is_active", is_active)) begin
            `uvm_info(get_type_name(), "is_active not set, defaulting to UVM_ACTIVE", UVM_MEDIUM)
        end
        
        // Create monitor (always present)
        monitor = uart_protocol_monitor::type_id::create("monitor", this);
        
        // Create driver and sequencer if active
        if (is_active == UVM_ACTIVE) begin
            driver = uart_protocol_driver::type_id::create("driver", this);
            sequencer = uvm_sequencer#(uart_protocol_transaction)::type_id::create("sequencer", this);
        end
    endfunction
    
    // Connect phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        if (is_active == UVM_ACTIVE) begin
            driver.seq_item_port.connect(sequencer.seq_item_export);
        end
    endfunction
    
endclass

// UART Protocol Environment
class uart_protocol_environment extends uvm_env;
    `uvm_component_utils(uart_protocol_environment)
    
    // Environment components
    uart_protocol_agent     agent;
    uart_protocol_scoreboard scoreboard;
    
    // Constructor
    function new(string name = "uart_protocol_environment", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Create components
        agent = uart_protocol_agent::type_id::create("agent", this);
        scoreboard = uart_protocol_scoreboard::type_id::create("scoreboard", this);
    endfunction
    
    // Connect phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect monitor to scoreboard
        agent.monitor.ap.connect(scoreboard.sb_export);
    endfunction
    
endclass

// UART Protocol Test Base Class
class uart_protocol_test_base extends uvm_test;
    `uvm_component_utils(uart_protocol_test_base)
    
    // Test environment
    uart_protocol_environment env;
    
    // Constructor
    function new(string name = "uart_protocol_test_base", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Create environment
        env = uart_protocol_environment::type_id::create("env", this);
        
        // Configure virtual interfaces (will be set by testbench)
        `uvm_info(get_type_name(), "UART Protocol test environment created", UVM_MEDIUM)
    endfunction
    
    // End of elaboration phase
    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        
        // Print UVM hierarchy topology via environment
        if (env != null) begin
            env.print();
        end
    endfunction
    
    // Run phase (to be overridden by specific tests)
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "=== Starting UART Protocol Test ===", UVM_MEDIUM)
        
        // Wait for reset release
        #100;
        
        `uvm_info(get_type_name(), "Base test run_phase - should be overridden", UVM_MEDIUM)
        
        // Default test duration
        #1000000;
        
        `uvm_info(get_type_name(), "=== UART Protocol Test Completed ===", UVM_MEDIUM)
        
        phase.drop_objection(this);
    endtask
    
endclass

// Basic UART Protocol Test
class uart_protocol_basic_test extends uart_protocol_test_base;
    `uvm_component_utils(uart_protocol_basic_test)
    
    // Constructor
    function new(string name = "uart_protocol_basic_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Run phase
    virtual task run_phase(uvm_phase phase);
        uart_basic_test_sequence seq;
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "=== Starting Basic UART Protocol Test ===", UVM_MEDIUM)
        
        // Wait for reset release
        #100;
        
        // Create and run test sequence
        seq = uart_basic_test_sequence::type_id::create("seq");
        seq.start(env.agent.sequencer);
        
        // Allow some time for final transactions
        #10000;
        
        `uvm_info(get_type_name(), "=== Basic UART Protocol Test Completed ===", UVM_MEDIUM)
        
        phase.drop_objection(this);
    endtask
    
endclass

// Coverage-enabled UART Protocol Test
class uart_protocol_coverage_test extends uart_protocol_test_base;
    `uvm_component_utils(uart_protocol_coverage_test)
    
    // Functional coverage
    covergroup uart_protocol_cg @(posedge env.agent.monitor.axi_vif.aclk);
        
        address_cp: coverpoint env.agent.monitor.axi_vif.awaddr {
            bins control_reg    = {8'h00};
            bins status_reg     = {8'h04};
            bins tx_data_reg    = {8'h08};
            bins rx_data_reg    = {8'h0C};
            bins baud_reg       = {8'h10};
            bins int_enable_reg = {8'h14};
            bins int_status_reg = {8'h18};
            bins fifo_config    = {8'h1C};
        }
        
        write_type_cp: coverpoint env.agent.monitor.axi_vif.awvalid {
            bins write_valid = {1'b1};
        }
        
        read_type_cp: coverpoint env.agent.monitor.axi_vif.arvalid {
            bins read_valid = {1'b1};
        }
        
        // Cross coverage
        addr_write_cross: cross address_cp, write_type_cp;
        
    endgroup
    
    // Constructor
    function new(string name = "uart_protocol_coverage_test", uvm_component parent = null);
        super.new(name, parent);
        uart_protocol_cg = new();
    endfunction
    
    // Run phase
    virtual task run_phase(uvm_phase phase);
        uart_basic_test_sequence seq;
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "=== Starting Coverage UART Protocol Test ===", UVM_MEDIUM)
        
        // Wait for reset release
        #100;
        
        // Create and run extended test sequence
        seq = uart_basic_test_sequence::type_id::create("seq");
        seq.start(env.agent.sequencer);
        
        // Allow coverage collection time
        #50000;
        
        `uvm_info(get_type_name(), "=== Coverage UART Protocol Test Completed ===", UVM_MEDIUM)
        
        phase.drop_objection(this);
    endtask
    
    // Report phase
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        
        `uvm_info(get_type_name(), $sformatf("Functional Coverage: %0.2f%%", 
                 uart_protocol_cg.get_inst_coverage()), UVM_MEDIUM)
    endfunction
    
endclass
