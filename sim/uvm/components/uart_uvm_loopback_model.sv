`timescale 1ns / 1ps

// Reactive UART loopback model that synthesizes device-to-host frames
// without engaging the RTL DUT. It consumes driver metadata and
// generates serial responses so the monitor can be validated in isolation.
class uart_uvm_loopback_model extends uvm_component;

    `uvm_component_utils(uart_uvm_loopback_model)

    // Configuration and interface handles
    uart_axi4_env_config cfg;
    virtual uart_if vif;

    // Incoming requests from the UART driver
    uvm_analysis_imp#(uart_frame_transaction, uart_uvm_loopback_model) request_export;
    mailbox #(uart_frame_transaction) request_mb;

    // Internal state
    bit initialized;
    bit driving_response;

    function new(string name = "uart_uvm_loopback_model", uvm_component parent = null);
        super.new(name, parent);
    request_export = new("request_export", this);
    request_mb = new();
    initialized = 0;
    driving_response = 0;
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        if (!uvm_config_db#(uart_axi4_env_config)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("UART_LOOPBACK", "Failed to acquire configuration object")
        end

        if (!uvm_config_db#(virtual uart_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("UART_LOOPBACK", "Failed to acquire UART virtual interface")
        end

        if (!cfg.enable_uvm_loopback_mode) begin
            `uvm_warning("UART_LOOPBACK", "Loopback model constructed while enable flag is low")
        end
    endfunction

    virtual task run_phase(uvm_phase phase);
        fork
            maintain_idle_override();
            process_requests();
        join
    endtask

    // TLM write implementation: clone transaction and queue for processing
    virtual function void write(uart_frame_transaction t);
        uart_frame_transaction copy;
        if (t == null) begin
            return;
        end
        $cast(copy, t.clone());
        if (!request_mb.try_put(copy)) begin
            `uvm_error("UART_LOOPBACK", "Failed to enqueue loopback request")
        end else begin
            `uvm_info("UART_LOOPBACK", $sformatf("Queued loopback request: cmd=0x%02X addr=0x%08X expect_error=%0b", copy.cmd, copy.addr, copy.expect_error), UVM_LOW)
        end
    endfunction

    protected task maintain_idle_override();
        forever begin
            @(posedge vif.clk);

            if (!cfg.enable_uvm_loopback_mode) begin
                if (vif.tb_uart_tx_override_en) begin
                    vif.tb_uart_tx_override_en = 1'b0;
                end
                vif.tb_uart_tx_override = 1'b1;
                initialized = 0;
                continue;
            end

            if (!vif.tb_loopback_active) begin
                if (vif.tb_uart_tx_override_en) begin
                    vif.tb_uart_tx_override_en = 1'b0;
                end
                vif.tb_uart_tx_override = 1'b1;
                initialized = 0;
                continue;
            end

            if (driving_response) begin
                continue;
            end

            if (!initialized) begin
                // Ensure the serial line starts idle but relinquish control to the driver
                vif.tb_uart_tx_override   = 1'b1;
                vif.tb_uart_tx_override_en = 1'b0;
                initialized = 1;
            end
        end
    endtask

    protected function void release_uart_line();
        vif.tb_uart_tx_override_en = 1'b0;
        vif.tb_uart_tx_override   = 1'b1;
    endfunction

    protected function int calculate_request_guard_cycles(uart_frame_transaction req);
        int request_bytes;
        int bit_cycles;

        if (req == null) begin
            return cfg.min_idle_cycles;
        end

        request_bytes = 1 + 1 + 4 + 1; // SOF + CMD + ADDR + CRC
        if (req.is_write && req.data.size() > 0) begin
            request_bytes += req.data.size();
        end

        bit_cycles = cfg.get_bit_time_cycles();
        if (bit_cycles < 1) begin
            bit_cycles = 1;
        end

        return (request_bytes * 10 * bit_cycles) + cfg.min_idle_cycles;
    endfunction

    protected task wait_for_request_completion(uart_frame_transaction req);
        int guard_cycles;

        guard_cycles = calculate_request_guard_cycles(req);
        if (guard_cycles < cfg.min_idle_cycles) begin
            guard_cycles = cfg.min_idle_cycles;
        end

        repeat (guard_cycles) @(posedge vif.clk);
    endtask

    protected task process_requests();
        uart_frame_transaction req;

        forever begin
            request_mb.get(req);

            if (!cfg.enable_uvm_loopback_mode || !vif.tb_loopback_active) begin
                `uvm_info("UART_LOOPBACK", "Loopback disabled - discarding queued request", UVM_LOW)
                release_uart_line();
                continue;
            end

            release_uart_line();
            wait_for_request_completion(req);
            drive_loopback_response(req);
        end
    endtask

    protected task drive_loopback_response(uart_frame_transaction req);
        logic [7:0] response_bytes[$];
        logic [7:0] crc_payload[];
        logic [7:0] status_byte;
        int bit_time_cycles;

        // Build minimal response frame
        status_byte = req.expect_error ? STATUS_TIMEOUT : STATUS_OK;

        response_bytes.push_back(SOF_DEVICE_TO_HOST);
        response_bytes.push_back(status_byte);
        response_bytes.push_back(req.cmd);
        response_bytes.push_back(req.addr[7:0]);
        response_bytes.push_back(req.addr[15:8]);
        response_bytes.push_back(req.addr[23:16]);
        response_bytes.push_back(req.addr[31:24]);

        if (!req.expect_error && req.cmd[7]) begin
            int beats;
            int bytes_per_beat;
            beats = int'(req.cmd[3:0]) + 1;
            case (req.cmd[5:4])
                2'b00: bytes_per_beat = 1;
                2'b01: bytes_per_beat = 2;
                default: bytes_per_beat = 4;
            endcase

            for (int i = 0; i < beats * bytes_per_beat; i++) begin
                logic [7:0] payload_byte;
                if (req.response_data.size() > i) begin
                    payload_byte = req.response_data[i];
                end else if (req.data.size() > i) begin
                    payload_byte = req.data[i];
                end else begin
                    payload_byte = 8'h00;
                end
                response_bytes.push_back(payload_byte);
            end
        end

        crc_payload = new[response_bytes.size() - 1];
        foreach (crc_payload[i]) begin
            crc_payload[i] = response_bytes[i + 1];
        end
        response_bytes.push_back(calculate_crc8(crc_payload, crc_payload.size()));

        bit_time_cycles = cfg.get_bit_time_cycles();
        if (bit_time_cycles < 1) begin
            bit_time_cycles = 1;
        end

        driving_response = 1;
        release_uart_line();

        // Guard period before asserting control of the UART line
        repeat (cfg.min_idle_cycles) @(posedge vif.clk);
        vif.tb_uart_tx_override_en = 1'b1;

        foreach (response_bytes[i]) begin
            drive_serial_byte(response_bytes[i], bit_time_cycles);
            repeat (cfg.min_idle_cycles) @(posedge vif.clk);
        end

        release_uart_line();
        driving_response = 0;

        `uvm_info("UART_LOOPBACK", $sformatf("Loopback response driven: status=0x%02X bytes=%0d", status_byte, response_bytes.size()), UVM_LOW)
    endtask

    protected task drive_serial_byte(logic [7:0] data, int bit_time_cycles);
        int local_bit_cycles;

        local_bit_cycles = (bit_time_cycles > 0) ? bit_time_cycles : 1;

        // Start bit
        vif.tb_uart_tx_override = 1'b0;
        repeat (local_bit_cycles) @(posedge vif.clk);

        // Data bits LSB-first
        for (int i = 0; i < 8; i++) begin
            vif.tb_uart_tx_override = data[i];
            repeat (local_bit_cycles) @(posedge vif.clk);
        end

        // Stop bit
        vif.tb_uart_tx_override = 1'b1;
        repeat (local_bit_cycles) @(posedge vif.clk);
    endtask

endclass
