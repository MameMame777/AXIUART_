`timescale 1ns / 1ps

// Fast basic test - minimal verbosity, no waveforms, maximum simulation speed
// Purpose: Quick sanity check for CI/CD or rapid iteration
class uart_axi4_fast_basic_test extends uart_axi4_basic_test;

    `uvm_component_utils(uart_axi4_fast_basic_test)

    function new(string name = "uart_axi4_fast_basic_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void configure_test();
        super.configure_test();
        
        // Suppress all non-critical messages for maximum speed
        cfg.enable_driver_debug_logs = 1'b0;
        cfg.driver_debug_verbosity = UVM_NONE;
        
        `uvm_info("FAST_TEST_CONFIG",
            "Fast test mode: minimal verbosity, no waveforms, maximum simulation speed",
            UVM_LOW)
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Suppress verbose component messages
        this.set_report_verbosity_level_hier(UVM_LOW);
        this.set_report_id_verbosity_hier("UART_DRIVER*", UVM_NONE);
        this.set_report_id_verbosity_hier("UART_MONITOR*", UVM_NONE);
        this.set_report_id_verbosity_hier("AXI4_LITE_MONITOR", UVM_LOW);
        this.set_report_id_verbosity_hier("SCOREBOARD", UVM_LOW);
        this.set_report_id_verbosity_hier("BASIC_TEST*", UVM_LOW);
        
        `uvm_info("FAST_TEST_BUILD", "Fast test build complete - verbosity minimized", UVM_LOW)
    endfunction

endclass
