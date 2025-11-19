`timescale 1ns / 1ps

// Fast 115200 test - minimal verbosity for maximum speed
// Purpose: Baud rate switching test optimized for performance
class uart_axi4_fast_115200_test extends uart_axi4_basic_115200_test;

    `uvm_component_utils(uart_axi4_fast_115200_test)

    function new(string name = "uart_axi4_fast_115200_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void configure_test();
        super.configure_test();
        
        // Suppress all non-critical messages for maximum speed
        cfg.enable_driver_debug_logs = 1'b0;
        cfg.driver_debug_verbosity = UVM_NONE;
        cfg.enable_driver_runtime_logs = 1'b0;
        cfg.enable_scoreboard_runtime_logs = 1'b0;
        cfg.enable_scoreboard_metadata_logs = 1'b0;
        cfg.driver_runtime_verbosity = UVM_LOW;
        cfg.scoreboard_runtime_verbosity = UVM_LOW;
        
        `uvm_info("FAST_115200_CONFIG",
            $sformatf("Fast 115200 test: minimal verbosity mode, target_baud=%0d", TARGET_BAUD_RATE),
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
        this.set_report_id_verbosity_hier("BASIC115*", UVM_LOW);
        this.set_report_id_verbosity_hier("DEBUG_SEQ*", UVM_NONE);
        this.set_report_id_verbosity_hier("UART_DRIVER_HANDSHAKE", UVM_NONE);
        this.set_report_id_verbosity_hier("UART_DRIVER_DEBUG", UVM_NONE);
        this.set_report_id_verbosity_hier("BASIC_TEST_LOOP", UVM_NONE);
        this.set_report_id_verbosity_hier("BASIC_TEST_WAIT", UVM_NONE);
        this.set_report_id_verbosity_hier("OBJECTION_DEBUG", UVM_NONE);
        
        `uvm_info("FAST_115200_BUILD", "Fast 115200 test build complete - verbosity minimized", UVM_LOW)
    endfunction

endclass
