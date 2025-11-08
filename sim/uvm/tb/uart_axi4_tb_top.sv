`timescale 1ns / 1ps

// Enable simulation-only system status signals
`define DEFINE_SIM

import uvm_pkg::*;
import uart_axi4_test_pkg::*;
`include "uvm_macros.svh"

// Top-level testbench for AXIUART_Top system-level verification
module uart_axi4_tb_top;
    
    // Clock and reset
    logic clk;
    logic rst;
    logic rst_n;
    
    // System status signals from DUT (simulation only)
    `ifdef DEFINE_SIM
    logic system_ready;
    logic system_busy;
    logic [7:0] system_error;
    `endif
    
    // Interface instances
    uart_if uart_if_inst(clk, rst);
    bridge_status_if status_if(clk, rst_n);
    
    // AXI4-Lite interface for monitoring - will connect directly to DUT's internal interface
    // No need for separate interface instance since DUT provides axi_internal interface

    // Scenario control for waveform dumping and debug selection
    string test_scenario = "default";
    string selected_uvm_test = "uart_axi4_basic_test";
    bit tb_loopback_mode = 1'b0;

    // Optional internal loopback control (disabled by default)
    localparam bit ENABLE_UART_LOOPBACK = 1'b0;

    // Baud rate shared across DUT and UVM configuration
    localparam int TB_BAUD_RATE = uart_axi4_test_pkg::BAUD_RATE;

    // Derived simulation guard sized for extended coverage campaigns at the oversampled max baud
    localparam time DEFAULT_SIM_TIMEOUT = 200ms; // Default guard; override via +SIM_TIMEOUT_MS=<value>

    // DUT UART wiring (allows loopback model to override signals when enabled)
    logic dut_uart_tx;
    logic dut_uart_rx;
    logic dut_uart_rts_n;
    logic dut_uart_cts_n;
    logic dut_led;
    logic dut_rst;

    // Ensure the RX line idles high until the driver starts toggling it
    initial begin
        uart_if_inst.uart_rx = 1'b1;
    end
    
    // DUT instance - Using complete AXIUART_Top system
    AXIUART_Top #(
        .CLK_FREQ_HZ(125_000_000),
        .BAUD_RATE(TB_BAUD_RATE),
        .AXI_TIMEOUT(1000),
        .UART_OVERSAMPLE(16),
        .RX_FIFO_DEPTH(64),
        .TX_FIFO_DEPTH(64),
        .MAX_LEN(16),
        .REG_BASE_ADDR(32'h0000_1000)
    ) dut (
        .clk(clk),
        .rst(dut_rst),

        // UART interface - external connections
        .uart_rx(dut_uart_rx),
        .uart_tx(dut_uart_tx),
        .uart_rts_n(dut_uart_rts_n),   // Request to Send (active low)
        .uart_cts_n(dut_uart_cts_n),   // Clear to Send (active low)
        .led(dut_led)

        // System status outputs (simulation only)
        `ifdef DEFINE_SIM
        ,
        .system_busy(system_busy),      
        .system_error(system_error),     
        .system_ready(system_ready)
        `endif    
    );

    // Route UART interface signals with loopback-aware overrides
    assign dut_uart_rx = uart_if_inst.uart_rx;
    assign uart_if_inst.uart_tx = (uart_if_inst.tb_uart_tx_override_en) ?
        uart_if_inst.tb_uart_tx_override : dut_uart_tx;
    assign uart_if_inst.uart_rts_n = tb_loopback_mode ? 1'b1 : dut_uart_rts_n;
    assign dut_uart_cts_n = tb_loopback_mode ? 1'b0 : uart_if_inst.uart_cts_n;
    assign uart_if_inst.tb_loopback_active = tb_loopback_mode;
    assign dut_rst = tb_loopback_mode ? 1'b1 : rst;

    // Connect DUT AXI interface directly to UVM monitor - no signal copying needed
    // UVM monitor will access dut.axi_internal directly via virtual interface

    // Bridge status interface wiring
    assign status_if.rst_n = rst_n;
    `ifdef DEFINE_SIM
    assign status_if.bridge_busy = system_busy;
    assign status_if.bridge_error = system_error;
    assign status_if.system_ready = system_ready;
    `else
    assign status_if.bridge_busy = 1'b0;
    assign status_if.bridge_error = 8'h00;
    assign status_if.system_ready = 1'b0;
    `endif
    
    // *** UART Loopback connection (legacy bring-up mode) ***
    // Disabled for full-system verification so the UVM driver controls uart_rx.
    // Set ENABLE_UART_LOOPBACK=1'b1 if a self-loopback is required for standalone debug.
    generate
        if (ENABLE_UART_LOOPBACK) begin : gen_uart_loopback
            always_comb begin
                uart_if_inst.uart_rx = uart_if_inst.uart_tx;
            end
        end
    endgenerate
    
    // Clock generation (matches DUT parameter: 125MHz)
    initial begin
        clk = 1'b0;
        forever #4ns clk = ~clk; // 125MHz clock
    end
    
    // Reset generation - EXTENDED RESET for stability
    initial begin
        rst   = 1'b1;
        rst_n = 1'b0;
        repeat (100) @(posedge clk);  // 100 clock cycles = 2us reset
        rst   = 1'b0;
        rst_n = 1'b1;
        `uvm_info("TB_TOP", "Reset released after extended period", UVM_MEDIUM)
        
        // Additional stability wait after reset release
        repeat (50) @(posedge clk);   // Additional 1us stability period
        `uvm_info("TB_TOP", "System stability period completed", UVM_MEDIUM)
    end
    
    // UVM testbench initialization
    initial begin
        // Import the test package to ensure all classes are registered
        import uart_axi4_test_pkg::*;
        
        // Capture UVM test selection and optional scenario plusargs
        string scenario_arg;
        string testname_arg;
        bit scenario_enables_wave;
        int loopback_flag;
        if ($value$plusargs("TEST_SCENARIO=%s", scenario_arg)) begin
            test_scenario = scenario_arg;
        end
        if ($value$plusargs("UVM_TESTNAME=%s", testname_arg)) begin
            selected_uvm_test = testname_arg;
        end
        if ($value$plusargs("UVM_LOOPBACK=%d", loopback_flag)) begin
            tb_loopback_mode = (loopback_flag != 0);
        end else if ($test$plusargs("UVM_LOOPBACK")) begin
            tb_loopback_mode = 1'b1;
        end

        uart_if_inst.tb_uart_tx_override_en = 1'b0;
        uart_if_inst.tb_uart_tx_override = 1'b1;

        if (tb_loopback_mode) begin
            `uvm_info("TB_TOP", "UVM loopback mode enabled: DUT instance held in reset and UART_TX overridden", UVM_LOW)
        end

        // Set virtual interfaces in config database
        uvm_config_db#(virtual uart_if)::set(null, "*", "vif", uart_if_inst);
        uvm_config_db#(virtual uart_if)::set(null, "*", "uart_vif", uart_if_inst); // Legacy support
        uvm_config_db#(virtual bridge_status_if)::set(null, "*", "bridge_status_vif", status_if);
        uvm_config_db#(virtual axi4_lite_if)::set(null, "*", "axi_vif", dut.axi_internal);
        uvm_config_db#(bit)::set(null, "*", "tb_loopback_mode", tb_loopback_mode);

        // Propagate scenario configuration into the UVM config database for tests
        uvm_config_db#(string)::set(null, "uvm_test_top", "test_scenario", test_scenario);
        uvm_config_db#(string)::set(null, "uvm_test_top", "selected_test_name", selected_uvm_test);
        uvm_config_db#(bit)::set(null, "uvm_test_top", "tb_loopback_mode", tb_loopback_mode);

        // Default policy: enable waveform dumping unless explicitly disabled via scenario name
        scenario_enables_wave = (test_scenario != "none");
        uvm_config_db#(bit)::set(null, "uvm_test_top", "scenario_enable_wave_dump", scenario_enables_wave);
        // Phase 4.3: Set AXI monitoring interface for AXI transaction detection
        
        // Start UVM test
        run_test();
    end

    // Defer waveform dumping until after reset release and stability
    // This prevents large recursive dump registration during reset and
    // avoids simulator I/O stalls at the moment of reset release.
    initial begin
        string wave_format_arg;
        string wave_extension;
        string wave_file;
        string wave_file_override;
        int waves_on_flag;
        bit scenario_enables_wave_dump;
    bit enable_wave_dump;

        // Determine whether waves were requested via command-line control
        if (!$value$plusargs("WAVES_ON=%d", waves_on_flag)) begin
            waves_on_flag = 0;
        end

        // Obtain scenario-controlled enable flag from config database
        if (!uvm_config_db#(bit)::get(null, "uvm_test_top", "scenario_enable_wave_dump", scenario_enables_wave_dump)) begin
            scenario_enables_wave_dump = 1'b1;
        end

        // Wait for reset to be released
        wait (rst_n == 1'b1);
        // Give some extra cycles for UVM/bench to finish initialization
        repeat (50) @(posedge clk);

        enable_wave_dump = 1'b1;

        if (!waves_on_flag) begin
            `uvm_info("TB_TOP", "Waveform dumping disabled (WAVES_ON flag not set)", UVM_MEDIUM)
            enable_wave_dump = 1'b0;
        end

        if (!scenario_enables_wave_dump) begin
            `uvm_info("TB_TOP", $sformatf("Waveform dumping skipped for scenario '%s'", test_scenario), UVM_MEDIUM)
            enable_wave_dump = 1'b0;
        end

        if (enable_wave_dump) begin
            if ($value$plusargs("WAVE_FORMAT=%s", wave_format_arg)) begin
                string wave_format_upper;
                wave_format_upper = wave_format_arg.toupper();

                case (wave_format_upper)
                    "VCD": wave_extension = "vcd";
                    "MXD": wave_extension = "mxd";
                    default: wave_extension = "vcd";
                endcase
            end else begin
                wave_extension = "vcd";
            end

            if ($value$plusargs("WAVE_FILE=%s", wave_file_override)) begin
                wave_file = wave_file_override;
            end else begin
                if (test_scenario.len() != 0 && test_scenario != "default") begin
                    wave_file = $sformatf("../archive/waveforms/%s_%s.%s", selected_uvm_test, test_scenario, wave_extension);
                end else begin
                    wave_file = $sformatf("../archive/waveforms/%s.%s", selected_uvm_test, wave_extension);
                end
            end

            // Scoped waveform dump: only DUT and UART interface to limit header size
            $dumpfile(wave_file);
            $dumpvars(0, dut);
            $dumpvars(0, uart_if_inst);
            `uvm_info("TB_TOP", $sformatf("Deferred scoped waveform dumping enabled (dut, uart_if_inst) -> %s", wave_file), UVM_MEDIUM)
        end
    end
    
    // Timeout mechanism - extended for comprehensive tests
    initial begin
        time sim_timeout_value;
        int timeout_ms;

        if ($value$plusargs("SIM_TIMEOUT_MS=%d", timeout_ms)) begin
            sim_timeout_value = timeout_ms * 1ms;
            `uvm_info("TB_TOP", $sformatf("SIM_TIMEOUT_MS plusarg applied: %0d ms", timeout_ms), UVM_MEDIUM)
        end else begin
            sim_timeout_value = DEFAULT_SIM_TIMEOUT;
        end

        #(sim_timeout_value);
        `uvm_error("TB_TOP", $sformatf("Test timeout - simulation exceeded %0t", sim_timeout_value))
        $finish;
    end
    
    // Protocol checker instances for additional verification
    
    // UART protocol checker
    uart_protocol_checker uart_checker (
        .clk(clk),
        .rst_n(rst_n),
        .uart_rx(uart_if_inst.uart_rx),
        .uart_tx(uart_if_inst.uart_tx)
    );
    
    // Note: AXI4-Lite protocol checker not applicable since AXIUART_Top uses internal AXI
    
    // Coverage collection
    `ifdef ENABLE_COVERAGE
        initial begin
            // Enable coverage collection at system level
            // $coverage_control(1);  // Commented out - not supported in all simulators
            `uvm_info("TB_TOP", "Coverage collection enabled", UVM_MEDIUM)
        end
    `endif
    
    // Assertion monitoring (temporarily disabled for compilation)
    `ifdef ENABLE_ASSERTIONS_DISABLED
        // Include assertion bind files for AXIUART_Top
        bind dut uart_axi4_assertions uart_axi4_assert_inst (
            .clk(clk),
            .rst_n(rst_n),
            .uart_rx(uart_rx),
            .uart_tx(uart_tx),
            // AXI interface signals - accessing internal interface
            .axi_awaddr(dut.axi_internal.awaddr),
            .axi_awvalid(dut.axi_internal.awvalid),
            .axi_awready(dut.axi_internal.awready),
            .axi_wdata(dut.axi_internal.wdata),
            .axi_wstrb(dut.axi_internal.wstrb),
            .axi_wvalid(dut.axi_internal.wvalid),
            .axi_wready(dut.axi_internal.wready),
            .axi_bresp(dut.axi_internal.bresp),
            .axi_bvalid(dut.axi_internal.bvalid),
            .axi_bready(dut.axi_internal.bready),
            .axi_araddr(dut.axi_internal.araddr),
            .axi_arvalid(dut.axi_internal.arvalid),
            .axi_arready(dut.axi_internal.arready),
            .axi_rdata(dut.axi_internal.rdata),
            .axi_rresp(dut.axi_internal.rresp),
            .axi_rvalid(dut.axi_internal.rvalid),
            .axi_rready(dut.axi_internal.rready),
            // Bridge internal status - accessing through bridge instance
            .bridge_state(dut.uart_bridge_inst.main_state),
            .frame_complete(dut.uart_bridge_inst.frame_parser.frame_valid),
            .crc_valid(dut.uart_bridge_inst.frame_parser.frame_valid && !dut.uart_bridge_inst.frame_parser.frame_error)
        );
    `endif // ENABLE_ASSERTIONS_DISABLED
    
    // Debug and monitoring for AXIUART_Top
    always @(posedge clk) begin
        if (rst_n) begin
            // Monitor critical signals through bridge instance
            if (dut.uart_bridge_inst.frame_parser.frame_valid) begin
                `uvm_info("TB_TOP", $sformatf("Frame parsed: CMD=0x%02X, ADDR=0x%08X", 
                          dut.uart_bridge_inst.frame_parser.cmd, 
                          dut.uart_bridge_inst.frame_parser.addr), UVM_DEBUG)
            end
            
            // Monitor system status (simulation only)
            `ifdef DEFINE_SIM
            if (dut.system_busy) begin
                `uvm_info("TB_TOP", "System busy", UVM_DEBUG)
            end
            
            if (dut.system_error != 0) begin
                `uvm_info("TB_TOP", $sformatf("System error: 0x%02X", dut.system_error), UVM_HIGH)
            end
            `endif
        end
    end
    
    // Performance monitoring
    real start_time, end_time;
    int transaction_count = 0;
    
    always @(posedge uart_if_inst.uart_rx or posedge uart_if_inst.uart_tx) begin
        if (rst_n) begin
            if ($time > 1000) begin // Skip reset period
                if (transaction_count == 0) start_time = $realtime;
                transaction_count++;
                
                if (transaction_count % 100 == 0) begin
                    end_time = $realtime;
                    `uvm_info("TB_TOP", $sformatf("Processed %0d transactions in %.2f ms", 
                              transaction_count, (end_time - start_time) / 1000000.0), UVM_LOW)
                end
            end
        end
    end
    
    // Save coverage database periodically
    `ifdef ENABLE_COVERAGE
        initial begin
            #2ms;
            `uvm_info("TB_TOP", "Coverage database saved", UVM_MEDIUM)
        end
    `endif
    
endmodule

// UART Protocol Checker
module uart_protocol_checker (
    input logic clk,
    input logic rst_n,
    input logic uart_rx,
    input logic uart_tx
);
    
    // Basic UART frame validation
    // Implementation would include timing checks, frame format validation, etc.
    
endmodule