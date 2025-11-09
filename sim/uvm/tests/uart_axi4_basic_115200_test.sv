`timescale 1ns / 1ps

class uart_axi4_basic_115200_test extends uart_axi4_basic_test;

    `uvm_component_utils(uart_axi4_basic_115200_test)

    localparam int TARGET_BAUD_RATE = 115_200;
    int runtime_baud_divisor;
    int original_baud_rate;
    int original_byte_time_ns;
    int original_frame_timeout_ns;

    function new(string name = "uart_axi4_basic_115200_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void configure_test();
        super.configure_test();

        original_baud_rate = cfg.baud_rate;
        original_byte_time_ns = cfg.byte_time_ns;
        original_frame_timeout_ns = cfg.frame_timeout_ns;

        cfg.frame_timeout_ns = cfg.byte_time_ns * 128;
        cfg.enable_driver_debug_logs = 1'b1;
        cfg.driver_debug_verbosity = UVM_HIGH;

        `uvm_info("BASIC115_CONFIG",
            $sformatf("Preparing baud override: default=%0d target=%0d (pre-config frame_timeout_ns=%0d)",
                original_baud_rate, TARGET_BAUD_RATE, cfg.frame_timeout_ns),
            UVM_LOW)
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        update_uart_interface_divisor();

        `uvm_info("BASIC115_CONFIG",
            $sformatf("Baud rate override applied: %0d baud (byte_time_ns=%0d, frame_timeout_ns=%0d)",
                cfg.baud_rate, cfg.byte_time_ns, cfg.frame_timeout_ns),
            UVM_LOW)
    endfunction

    protected function void update_uart_interface_divisor();
        compute_runtime_baud_divisor();
        apply_uart_interface_divisor("BASIC115_CONFIG");
    endfunction

    protected function void compute_runtime_baud_divisor();
        int divisor;

        if (cfg == null) begin
            runtime_baud_divisor = 1;
            `uvm_warning("BASIC115_CONFIG", "Configuration handle unavailable; forcing baud divisor to 1")
            return;
        end

        divisor = (TARGET_BAUD_RATE > 0) ? (cfg.clk_freq_hz / TARGET_BAUD_RATE) : 0;
        if (divisor <= 0) begin
            divisor = 1;
        end

        if (divisor > 16'hFFFF) begin
            `uvm_warning("BASIC115_CONFIG",
                $sformatf("Computed divisor=%0d exceeds 16-bit field; clamping to 0xFFFF", divisor))
            divisor = 16'hFFFF;
        end

        runtime_baud_divisor = divisor;
        `uvm_info("BASIC115_CONFIG",
            $sformatf("Computed runtime baud divisor=%0d (clk=%0d Hz, baud=%0d)",
                runtime_baud_divisor, cfg.clk_freq_hz, cfg.baud_rate),
            UVM_MEDIUM)
    endfunction

    protected function void apply_uart_interface_divisor(string caller_id);
        if (cfg != null && cfg.uart_vif != null) begin
            cfg.uart_vif.baud_divisor = runtime_baud_divisor[15:0];
            `uvm_info(caller_id,
                $sformatf("UART interface baud_divisor programmed to %0d (0x%04h)",
                    runtime_baud_divisor, runtime_baud_divisor[15:0]),
                UVM_LOW)
        end else begin
            `uvm_warning(caller_id,
                $sformatf("UART virtual interface unavailable; pending divisor=%0d (0x%04h)",
                    runtime_baud_divisor, runtime_baud_divisor[15:0]))
        end
    endfunction

    protected task program_baud_divisor_register();
        uart_configure_baud_sequence cfg_seq;

        if (env == null || env.uart_agt == null || env.uart_agt.sequencer == null) begin
            `uvm_fatal("BASIC115_CONFIG", "Environment or UART sequencer unavailable for baud programming")
        end

        // Ensure the runtime divisor has been evaluated before programming the DUT.
        if (runtime_baud_divisor == 0) begin
            compute_runtime_baud_divisor();
        end

        cfg_seq = uart_configure_baud_sequence::type_id::create("baud_cfg_seq", this);
        if (cfg_seq == null) begin
            `uvm_fatal("BASIC115_CONFIG", "Failed to create uart_configure_baud_sequence")
        end

        if (runtime_baud_divisor == 0) begin
            `uvm_fatal("BASIC115_CONFIG",
                "runtime_baud_divisor is zero prior to CONFIG write – divisor calculation failed")
        end

        cfg_seq.divisor_value = runtime_baud_divisor;
        cfg_seq.timeout_field_value = 8'h00;

        `uvm_info("BASIC115_CONFIG",
            $sformatf("Starting CONFIG write sequence with divisor=%0d (0x%04h)",
                runtime_baud_divisor, runtime_baud_divisor[15:0]),
            UVM_MEDIUM)

        cfg_seq.start(env.uart_agt.sequencer);
    endtask

    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this, "Program runtime baud divisor");
        wait (uart_axi4_tb_top.rst_n == 1'b1);
        repeat (10) @(posedge uart_axi4_tb_top.clk);
        program_baud_divisor_register();
        repeat (10) @(posedge uart_axi4_tb_top.clk);
        finalize_runtime_baud_override();
        phase.drop_objection(this, "Program runtime baud divisor");

        super.run_phase(phase);
    endtask

    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        apply_uart_interface_divisor("BASIC115_CONFIG");
    endfunction

    protected function void finalize_runtime_baud_override();
        if (cfg == null) begin
            `uvm_warning("BASIC115_CONFIG", "Configuration handle unavailable; cannot finalize baud override")
            return;
        end

        cfg.baud_rate = TARGET_BAUD_RATE;
        cfg.bit_time_ns = (cfg.baud_rate > 0) ? (1_000_000_000 / cfg.baud_rate) : 0;
        cfg.byte_time_ns = cfg.bit_time_ns * 10;
        cfg.frame_timeout_ns = cfg.byte_time_ns * 128;
        apply_uart_interface_divisor("BASIC115_CONFIG");

        `uvm_info("BASIC115_CONFIG",
            $sformatf("Baud override applied: baud_rate=%0d byte_time_ns=%0d frame_timeout_ns=%0d divisor=%0d",
                cfg.baud_rate, cfg.byte_time_ns, cfg.frame_timeout_ns, runtime_baud_divisor),
            UVM_LOW)
    endfunction

endclass
