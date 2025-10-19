`timescale 1ns / 1ps

// Enhanced test suite for comprehensive coverage improvement
// Integrates register sweep, functional coverage, and error injection

// Import statements removed - will be handled by package inclusion order
// import axiuart_cov_pkg::*;
// import axiuart_error_sequences_pkg::*;

// Comprehensive coverage test with all new features
class axiuart_comprehensive_coverage_test extends enhanced_uart_axi4_base_test;
    `uvm_component_utils(axiuart_comprehensive_coverage_test)
    
    // Coverage and sequence control (references moved to runtime)
    // axiuart_functional_coverage func_cov;
    
    function new(string name="axiuart_comprehensive_coverage_test", uvm_component parent=null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        configure_test_specific_reporting();
        
        // Enable comprehensive coverage collection
        uvm_config_db#(bit)::set(this, "*", "coverage_enabled", 1);
        uvm_config_db#(bit)::set(this, "*", "frame_cov_en", 1);
        uvm_config_db#(bit)::set(this, "*", "crc_cov_en", 1);
        uvm_config_db#(bit)::set(this, "*", "axi_cov_en", 1);
        uvm_config_db#(bit)::set(this, "*", "fifo_cov_en", 1);
        uvm_config_db#(bit)::set(this, "*", "error_cov_en", 1);
        uvm_config_db#(bit)::set(this, "*", "state_cov_en", 1);
        uvm_config_db#(bit)::set(this, "*", "cross_cov_en", 1);
        
        // Create functional coverage subscriber
        func_cov = axiuart_functional_coverage::type_id::create("func_cov", this);
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect functional coverage to monitors
        if (env.uart_agt.monitor.analysis_port != null) begin
            env.uart_agt.monitor.analysis_port.connect(func_cov.analysis_export);
        end
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this, "Running comprehensive coverage test");
        
        `uvm_info(get_type_name(), "=== Starting AXIUART Comprehensive Coverage Test ===", UVM_LOW)
        
        // Phase 1: Register Coverage (Toggle Coverage Focus)
        run_register_coverage_phase();
        
        // Phase 2: Basic Functional Coverage
        run_functional_coverage_phase();
        
        // Phase 3: Error Injection Coverage
        run_error_injection_phase();
        
        // Phase 4: Stress and Corner Cases
        run_stress_test_phase();
        
        // Allow final transactions to complete
        #2000;
        
        `uvm_info(get_type_name(), "=== AXIUART Comprehensive Coverage Test Completed ===", UVM_LOW)
        
        phase.drop_objection(this, "Comprehensive coverage test finished");
    endtask
    
    virtual task run_register_coverage_phase();
        // axiuart_register_sweep_sequence reg_sweep;  // Moved to external file
        
        `uvm_info(get_type_name(), "Phase 1: Register Coverage (Toggle Focus)", UVM_MEDIUM)
        
        // Create and execute register sweep sequence
        begin
            axiuart_register_sweep_sequence reg_sweep;
            reg_sweep = axiuart_register_sweep_sequence::type_id::create("reg_sweep");
            reg_sweep.start(env.uart_agt.sequencer);
        end
        
        #500; // Allow register operations to complete
    endtask
    
    virtual task run_functional_coverage_phase();
        `uvm_info(get_type_name(), "Phase 2: Functional Coverage", UVM_MEDIUM)
        
        // Run various frame lengths and types
        repeat (20) begin
            uart_comprehensive_sequence func_seq;
            func_seq = uart_comprehensive_sequence::type_id::create("func_seq");
            if (!func_seq.randomize() with {
                num_transactions inside {[5:15]};
            }) begin
                `uvm_error(get_type_name(), "Failed to randomize functional sequence")
            end
            func_seq.start(env.uart_agt.sqr);
            #100;
        end
    endtask
    
    virtual task run_error_injection_phase();
        `uvm_info(get_type_name(), "Phase 3: Error Injection Coverage", UVM_MEDIUM)
        
        // UART Error Injection
        begin
            axiuart_uart_error_injection_sequence uart_err_seq;
            uart_err_seq = axiuart_uart_error_injection_sequence::type_id::create("uart_err_seq");
            uart_err_seq.start(env.uart_agt.sqr);
        end
        
        #500;
        
        // CRC Fault Injection
        begin
            axiuart_crc_fault_sequence crc_fault_seq;
            crc_fault_seq = axiuart_crc_fault_sequence::type_id::create("crc_fault_seq");
            crc_fault_seq.start(env.uart_agt.sqr);
        end
        
        #500;
        
        // FIFO Boundary Testing
        begin
            axiuart_fifo_boundary_sequence fifo_bound_seq;
            fifo_bound_seq = axiuart_fifo_boundary_sequence::type_id::create("fifo_bound_seq");
            fifo_bound_seq.start(env.uart_agt.sqr);
        end
        
        #500;
        
        // AXI Error Testing
        begin
            axiuart_axi_error_sequence axi_err_seq;
            axi_err_seq = axiuart_axi_error_sequence::type_id::create("axi_err_seq");
            axi_err_seq.start(env.uart_agt.sqr);
        end
        
        #500;
        
        // Multi-layer Error Testing
        begin
            axiuart_multi_error_sequence multi_err_seq;
            multi_err_seq = axiuart_multi_error_sequence::type_id::create("multi_err_seq");
            multi_err_seq.start(env.uart_agt.sqr);
        end
    endtask
    
    virtual task run_stress_test_phase();
        `uvm_info(get_type_name(), "Phase 4: Stress and Corner Cases", UVM_MEDIUM)
        
        // High-frequency back-to-back transactions
        repeat (15) begin
            uart_write_sequence write_seq;
            write_seq = uart_write_sequence::type_id::create("write_seq");
            if (!write_seq.randomize() with {
                length inside {[32:128]};
                delay_between_transactions == 0; // Back-to-back
            }) begin
                `uvm_error(get_type_name(), "Failed to randomize stress sequence")
            end
            write_seq.start(env.uart_agt.sqr);
            #10; // Minimal delay
        end
        
        #1000;
        
        // Maximum length frames with CRC
        repeat (5) begin
            uart_basic_sequence max_seq;
            max_seq = uart_basic_sequence::type_id::create("max_seq");
            if (!max_seq.randomize() with {
                length == 255;
                crc_enable == 1'b1;
            }) begin
                `uvm_error(get_type_name(), "Failed to randomize max length sequence")
            end
            max_seq.start(env.uart_agt.sqr);
            #200;
        end
    endtask
    
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        
        // Print comprehensive coverage summary
        `uvm_info(get_type_name(), "=== COVERAGE SUMMARY ===", UVM_LOW)
        
        // Functional coverage is reported by the coverage subscriber
        if (func_cov != null) begin
            func_cov.report_phase(phase);
        end
        
        `uvm_info(get_type_name(), "=== END COVERAGE SUMMARY ===", UVM_LOW)
    endfunction
    
endclass

// Toggle coverage focused test
class axiuart_toggle_coverage_test extends enhanced_uart_axi4_base_test;
    `uvm_component_utils(axiuart_toggle_coverage_test)
    
    function new(string name="axiuart_toggle_coverage_test", uvm_component parent=null);
        super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this, "Running toggle coverage test");
        
        `uvm_info(get_type_name(), "Starting Toggle Coverage Focused Test", UVM_LOW)
        
        // Multiple register sweeps with different patterns
        repeat (3) begin
            axiuart_register_sweep_sequence reg_sweep;
            reg_sweep = axiuart_register_sweep_sequence::type_id::create("reg_sweep");
            reg_sweep.start(env.uart_agt.sequencer);
            #200;
        end
        
        // Add some UART activity to toggle UART-related signals
        repeat (10) begin
            uart_basic_sequence basic_seq;
            basic_seq = uart_basic_sequence::type_id::create("basic_seq");
            if (!basic_seq.randomize() with {
                length inside {[1:64]};
            }) begin
                `uvm_error(get_type_name(), "Failed to randomize basic sequence")
            end
            basic_seq.start(env.uart_agt.sqr);
            #50;
        end
        
        #500;
        
        `uvm_info(get_type_name(), "Toggle Coverage Test Completed", UVM_LOW)
        
        phase.drop_objection(this, "Toggle coverage test finished");
    endtask
    
endclass

// Error injection focused test
class axiuart_error_focused_test extends enhanced_uart_axi4_base_test;
    `uvm_component_utils(axiuart_error_focused_test)
    
    function new(string name="axiuart_error_focused_test", uvm_component parent=null);
        super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this, "Running error focused test");
        
        `uvm_info(get_type_name(), "Starting Error Injection Focused Test", UVM_LOW)
        
        // Systematic error injection across all layers
        fork
            // UART layer errors
            begin
                axiuart_uart_error_injection_sequence uart_err;
                uart_err = axiuart_uart_error_injection_sequence::type_id::create("uart_err");
                uart_err.start(env.uart_agt.sqr);
            end
            
            // CRC layer errors  
            begin
                axiuart_crc_fault_sequence crc_err;
                crc_err = axiuart_crc_fault_sequence::type_id::create("crc_err");
                #1000; // Delay to interleave with UART errors
                crc_err.start(env.uart_agt.sqr);
            end
            
            // FIFO boundary errors
            begin
                axiuart_fifo_boundary_sequence fifo_err;
                fifo_err = axiuart_fifo_boundary_sequence::type_id::create("fifo_err");
                #2000; // Delay to interleave
                fifo_err.start(env.uart_agt.sqr);
            end
        join
        
        #1000;
        
        `uvm_info(get_type_name(), "Error Injection Focused Test Completed", UVM_LOW)
        
        phase.drop_objection(this, "Error focused test finished");
    endtask
    
endclass
