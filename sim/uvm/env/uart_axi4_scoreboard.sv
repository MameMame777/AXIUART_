`timescale 1ns / 1ps

// Helper class to track expanded UART expectations across AXI beats
class uart_axi4_expected_transaction extends uvm_object;
    uart_frame_transaction uart_tr;
    bit is_write;
    bit auto_increment;
    logic [1:0] size;
    int beats_total;
    int bytes_per_beat;
    int next_index;
    logic [31:0] beat_addr[];
    logic [3:0] expected_wstrb[];
    logic [31:0] expected_wdata[];
    bit expect_error;

    function new(string name = "uart_axi4_expected_transaction");
        super.new(name);
        beats_total = 0;
        bytes_per_beat = 0;
        next_index = 0;
        beat_addr = new[0];
        expected_wstrb = new[0];
        expected_wdata = new[0];
        expect_error = 0;
    endfunction

    function int remaining_beats();
        return beats_total - next_index;
    endfunction
endclass

// UVM Scoreboard for UART-AXI4 Bridge
class uart_axi4_scoreboard extends uvm_scoreboard;
    
    `uvm_component_utils(uart_axi4_scoreboard)
    
    // Analysis ports for receiving transactions
    `uvm_analysis_imp_decl(_uart)
    `uvm_analysis_imp_decl(_axi)
    `uvm_analysis_imp_decl(_uart_expected)
    uvm_analysis_imp_uart #(uart_frame_transaction, uart_axi4_scoreboard) uart_analysis_imp;
    uvm_analysis_imp_axi #(axi4_lite_transaction, uart_axi4_scoreboard) axi_analysis_imp;
    uvm_analysis_imp_uart_expected #(uart_frame_transaction, uart_axi4_scoreboard) uart_expected_analysis_imp;
    
    // Configuration
    uart_axi4_env_config cfg;
    
    // Queues for matching transactions
    uart_axi4_expected_transaction uart_expectations[$];
    axi4_lite_transaction axi_queue[$];
    uart_frame_transaction uart_expected_queue[$];

    // Register map boundaries for automatic reserved-address classification
    localparam logic [31:0] REG_BASE_ADDR = 32'h0000_1000;
    localparam logic [31:0] REG_LAST_VALID_ADDR = 32'h0000_101F;
    
    // Statistics
    int uart_transactions_received = 0;
    int uart_device_responses_received = 0;
    int axi4_lite_transactions_received = 0;
    int match_count = 0;
    int mismatch_count = 0;
    int error_frame_count = 0;
    int expected_error_count = 0;
    int crc_error_count = 0;
    int timeout_count = 0;
    int protocol_error_count = 0;
    int critical_error_count = 0;
    int transaction_count = 0;
    int total_bytes_transferred = 0;
    int total_test_time = 0;
    int average_latency_ns = 0;
    int peak_latency_ns = 0;
    int uart_status_ok_count = 0;
    int uart_status_busy_count = 0;
    int uart_status_error_count = 0;
    
    // Bridge enable state monitoring for correlation analysis
    bit previous_bridge_enable = 1'b1;
    time last_bridge_enable_change_time = 0;
    int bridge_enable_transitions = 0;
    int transactions_with_bridge_disabled = 0;
    int bridge_disable_error_count = 0;
    
    // Bridge state-aware timeout and correlation parameters
    parameter time BRIDGE_DISABLE_TIMEOUT_EXTENSION = 50000ns;  // Additional timeout during bridge disable
    parameter time BRIDGE_TRANSITION_SETTLE_TIME = 10000ns;     // Time to allow bridge state to settle
    parameter int MAX_BRIDGE_DISABLE_WINDOW_BEATS = 10;         // Max beats to tolerate during disable window
    
    function new(string name = "uart_axi4_scoreboard", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        uart_analysis_imp = new("uart_analysis_imp", this);
        axi_analysis_imp = new("axi_analysis_imp", this);
        uart_expected_analysis_imp = new("uart_expected_analysis_imp", this);
        
        if (!uvm_config_db#(uart_axi4_env_config)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("SCOREBOARD", "Failed to get configuration object")
        end
    endfunction
    
    virtual function void write_uart_expected(uart_frame_transaction tr);
        uart_frame_transaction queued_tr;

        $cast(queued_tr, tr.clone());
        uart_expected_queue.push_back(queued_tr);

        `uvm_info("SCOREBOARD",
            $sformatf("Queued UART request metadata: CMD=0x%02X ADDR=0x%08X expect_error=%0b queue_depth=%0d",
                      queued_tr.cmd, queued_tr.addr, queued_tr.expect_error, uart_expected_queue.size()),
            UVM_HIGH)
    endfunction

    function bit is_addr_reserved(logic [31:0] addr);
        if (addr < REG_BASE_ADDR) begin
            return 1'b1;
        end

        if (addr > REG_LAST_VALID_ADDR) begin
            return 1'b1;
        end

        return 1'b0;
    endfunction

    function void apply_expected_metadata(ref uart_frame_transaction uart_tr);
        uart_frame_transaction queued_tr;

        if (uart_expected_queue.size() == 0) begin
            `uvm_warning("SCOREBOARD",
                $sformatf("No pre-drive metadata available for UART frame CMD=0x%02X ADDR=0x%08X",
                          uart_tr.cmd, uart_tr.addr))
            return;
        end

        queued_tr = uart_expected_queue.pop_front();

        if ((queued_tr.cmd !== uart_tr.cmd) || (queued_tr.addr !== uart_tr.addr)) begin
            `uvm_warning("SCOREBOARD",
                $sformatf("Metadata mismatch: observed CMD=0x%02X ADDR=0x%08X, queued CMD=0x%02X ADDR=0x%08X",
                          uart_tr.cmd, uart_tr.addr, queued_tr.cmd, queued_tr.addr))
        end

        uart_tr.expect_error = queued_tr.expect_error;
        uart_tr.is_write = queued_tr.is_write;
        uart_tr.auto_increment = queued_tr.auto_increment;
        uart_tr.size = queued_tr.size;
        uart_tr.length = queued_tr.length;
    endfunction

    // Receive UART transactions
    virtual function void write_uart(uart_frame_transaction tr);
        uart_frame_transaction uart_tr;
        uart_axi4_expected_transaction expectation;

        if (tr.direction == UART_TX) begin
            handle_uart_response(tr);
            return;
        end

        $cast(uart_tr, tr.clone());

        if (uart_tr.direction != UART_RX) begin
            `uvm_info("SCOREBOARD",
                $sformatf("Ignoring UART frame CMD=0x%02X (direction=%s)",
                          uart_tr.cmd, uart_tr.direction.name()),
                UVM_HIGH)
            return;
        end

        uart_transactions_received++;

        apply_expected_metadata(uart_tr);

        if (uart_tr.error_inject || uart_tr.force_crc_error || uart_tr.force_timeout ||
            uart_tr.corrupt_frame_format || uart_tr.truncate_frame || uart_tr.wrong_sof) begin
            error_frame_count++;
            `uvm_info("SCOREBOARD",
                $sformatf("Ignoring expected error-injected UART frame CMD=0x%02X ADDR=0x%08X (inject flags active)",
                          uart_tr.cmd, uart_tr.addr),
                UVM_MEDIUM)
            return;
        end

        expectation = build_expected_transaction(uart_tr);

        if (expectation == null) begin
            `uvm_error("SCOREBOARD",
                $sformatf("Failed to build expectation for UART frame CMD=0x%02X ADDR=0x%08X", uart_tr.cmd, uart_tr.addr))
            return;
        end

        uart_expectations.push_back(expectation);

        `uvm_info("SCOREBOARD",
            $sformatf("Received UART transaction: CMD=0x%02X, ADDR=0x%08X, beats=%0d",
                      uart_tr.cmd, uart_tr.addr, expectation.beats_total), UVM_DEBUG)

        // Check for matching AXI transaction
        check_for_matches();
    endfunction
    
    // Receive AXI transactions
    virtual function void write_axi(axi4_lite_transaction tr);
        axi4_lite_transaction axi_tr;
        
        $cast(axi_tr, tr.clone());
        axi_queue.push_back(axi_tr);
        axi4_lite_transactions_received++;
        
        `uvm_info("SCOREBOARD", $sformatf("Received AXI transaction: ADDR=0x%08X, WDATA=0x%08X, WSTRB=0x%X", 
                  axi_tr.addr, axi_tr.wdata, axi_tr.wstrb), UVM_DEBUG)
        
        // Check for matching UART transaction
        check_for_matches();
    endfunction
    
    // Check for transaction matches
    virtual function void check_for_matches();
        uart_axi4_expected_transaction expectation;
        axi4_lite_transaction axi_tr;

        int exp_idx;
        int axi_idx;
        int beat_index;
        int match_result;
        logic [31:0] expected_addr;
        bit progress;

        do begin
            progress = 0;

            for (exp_idx = 0; exp_idx < uart_expectations.size(); exp_idx++) begin
                expectation = uart_expectations[exp_idx];

                if (expectation.next_index >= expectation.beats_total) begin
                    continue;
                end

                beat_index = expectation.next_index;
                expected_addr = expectation.beat_addr[beat_index];

                for (axi_idx = 0; axi_idx < axi_queue.size(); axi_idx++) begin
                    axi_tr = axi_queue[axi_idx];

                    if (axi_tr.addr != expected_addr) begin
                        continue;
                    end

                    if (axi_tr.is_write != expectation.is_write) begin
                        continue;
                    end

                    if (expectation.is_write &&
                        (axi_tr.wstrb !== expectation.expected_wstrb[beat_index])) begin
                        continue;
                    end

                    match_result = verify_transaction_match(expectation, beat_index, axi_tr);
                    
                    if (match_result == 1) begin
                        // Successful match
                        match_count++;
                        `uvm_info("SCOREBOARD",
                            $sformatf("Matched beat %0d/%0d for CMD=0x%02X ADDR=0x%08X",
                                      beat_index + 1, expectation.beats_total,
                                      expectation.uart_tr.cmd, expected_addr),
                            UVM_MEDIUM)

                        axi_queue.delete(axi_idx);
                        expectation.next_index++;

                        if (expectation.next_index == expectation.beats_total) begin
                            `uvm_info("SCOREBOARD",
                                $sformatf("Completed UART command CMD=0x%02X ADDR=0x%08X",
                                          expectation.uart_tr.cmd, expectation.uart_tr.addr),
                                UVM_LOW)
                            uart_expectations.delete(exp_idx);
                        end

                        progress = 1;
                    end else if (match_result == -1) begin
                        // Transaction deferred due to bridge state - continue checking other transactions
                        `uvm_info("SCOREBOARD_BRIDGE_STATE",
                            $sformatf("Transaction deferred: CMD=0x%02X ADDR=0x%08X beat=%0d",
                                      expectation.uart_tr.cmd, expected_addr, beat_index + 1),
                            UVM_HIGH)
                        continue; // Don't delete anything, just defer this transaction
                    end else begin
                        // Actual mismatch (match_result == 0)
                        mismatch_count++;
                        `uvm_error("SCOREBOARD",
                            $sformatf("Transaction mismatch at beat %0d for CMD=0x%02X ADDR=0x%08X",
                                      beat_index + 1, expectation.uart_tr.cmd, expected_addr))

                        uart_expectations.delete(exp_idx);
                        axi_queue.delete(axi_idx);
                        progress = 1;
                    end

                    break;
                end

                if (progress) begin
                    break;
                end
            end
        end while (progress);
    endfunction
    
    // Verify that UART and AXI transactions match
    // Returns: 1 = match, 0 = mismatch, -1 = deferred (bridge state)
    virtual function int verify_transaction_match(uart_axi4_expected_transaction expectation,
                                                  int beat_index,
                                                  axi4_lite_transaction axi_tr);
        bit is_write;
        logic [3:0] wstrb_expected;
        bit expect_error;
        bit bridge_enabled;
        bit allow_error;
        bit require_error;
        bit reserved_addr;

        // Enhanced debug logging for scoreboard repair
        `uvm_info("SCOREBOARD_VERIFY",
            $sformatf("Verifying match: ADDR=0x%08X beat=%0d CMD=0x%02X AXI_%s vs UART_expect_error=%0b",
                      axi_tr.addr, beat_index + 1, expectation.uart_tr.cmd,
                      axi_tr.is_write ? "WRITE" : "READ", expectation.expect_error),
            UVM_HIGH)

        is_write = expectation.is_write;
        if (expectation.is_write) begin
            wstrb_expected = expectation.expected_wstrb[beat_index];
        end else begin
            wstrb_expected = 4'b0000;
        end
        expect_error = expectation.expect_error;
        bridge_enabled = 1'b1;
        reserved_addr = is_addr_reserved(expectation.beat_addr[beat_index]);

        if (cfg.bridge_status_vif != null) begin
            bridge_enabled = cfg.bridge_status_vif.bridge_enable;
            
            // Monitor bridge_enable state transitions for correlation analysis
            if (bridge_enabled != previous_bridge_enable) begin
                bridge_enable_transitions++;
                last_bridge_enable_change_time = $time;
                `uvm_info("SCOREBOARD_BRIDGE_STATE",
                    $sformatf("Bridge enable state changed: %0b -> %0b at time %0t (transition #%0d)",
                              previous_bridge_enable, bridge_enabled, $time, bridge_enable_transitions),
                    UVM_MEDIUM)
                previous_bridge_enable = bridge_enabled;
            end
            
            // Track transactions when bridge is disabled
            if (!bridge_enabled) begin
                transactions_with_bridge_disabled++;
                `uvm_info("SCOREBOARD_BRIDGE_STATE",
                    $sformatf("Transaction with bridge DISABLED: ADDR=0x%08X CMD=0x%02X (count=%0d)",
                              axi_tr.addr, expectation.uart_tr.cmd, transactions_with_bridge_disabled),
                    UVM_MEDIUM)
            end
        end

        if (!expect_error && reserved_addr) begin
            expect_error = 1'b1;
            expectation.expect_error = 1'b1;
            `uvm_info("SCOREBOARD",
                $sformatf("Auto-classifying reserved address 0x%08X as expected error",
                          expectation.beat_addr[beat_index]),
                UVM_MEDIUM)
        end

        allow_error = expect_error || !bridge_enabled;
        require_error = expect_error || !bridge_enabled;

        // Bridge state-aware transaction validation
        if (!is_bridge_state_valid_for_transaction(expectation, beat_index)) begin
            `uvm_info("SCOREBOARD_BRIDGE_STATE",
                $sformatf("Deferring transaction due to bridge state: ADDR=0x%08X CMD=0x%02X bridge_enable=%0b time_since_transition=%0t",
                          axi_tr.addr, expectation.uart_tr.cmd, bridge_enabled, 
                          $time - last_bridge_enable_change_time),
                UVM_MEDIUM)
            return -1; // Special return code for deferred transactions
        end

        // Enhanced logging for error expectation logic
        `uvm_info("SCOREBOARD_VERIFY",
            $sformatf("Error logic: bridge_enabled=%0b reserved_addr=%0b expect_error=%0b allow_error=%0b require_error=%0b",
                      bridge_enabled, reserved_addr, expect_error, allow_error, require_error),
            UVM_HIGH)

        if (axi_tr.is_write != is_write) begin
            `uvm_error("SCOREBOARD", "Transaction type mismatch (read/write)")
            return 0;
        end

        // Check transaction type matches
        if (is_write) begin
            logic [1:0] bresp = axi_tr.bresp;

            if (bresp != 2'b00) begin
                if (!allow_error) begin
                    `uvm_error("SCOREBOARD",
                        $sformatf("Unexpected AXI write response 0x%0X at ADDR=0x%08X", bresp, axi_tr.addr))
                    return 0;
                end

                expected_error_count++;
                `uvm_info("SCOREBOARD",
                    $sformatf("Expected error write observed: ADDR=0x%08X BRESP=0x%0X (bridge_enable=%0b expect_error=%0b)",
                              axi_tr.addr, bresp, bridge_enabled, expect_error),
                    UVM_MEDIUM)
                return 1;
            end

            if (require_error) begin
                // Track bridge disable related errors specifically
                if (!bridge_enabled && !expect_error) begin
                    bridge_disable_error_count++;
                    `uvm_error("SCOREBOARD",
                        $sformatf("BRIDGE_DISABLE_ERROR: Expected AXI error on write at ADDR=0x%08X but BRESP=0 (bridge_enable=%0b expect_error=%0b) [bridge_disable_error #%0d]",
                                  axi_tr.addr, bridge_enabled, expect_error, bridge_disable_error_count))
                end else begin
                    `uvm_error("SCOREBOARD",
                        $sformatf("Expected AXI error on write at ADDR=0x%08X but BRESP=0 (bridge_enable=%0b expect_error=%0b)",
                                  axi_tr.addr, bridge_enabled, expect_error))
                end
                return 0;
            end

            if (axi_tr.wstrb != wstrb_expected) begin
                `uvm_error("SCOREBOARD", $sformatf("WSTRB mismatch: expected 0x%X, got 0x%X",
                          wstrb_expected, axi_tr.wstrb))
                return 0;
            end

            if (!verify_write_data(expectation, beat_index, axi_tr)) begin
                return 0;
            end
        end else begin
            logic [1:0] rresp = axi_tr.rresp;

            if (rresp != 2'b00) begin
                if (!allow_error) begin
                    `uvm_error("SCOREBOARD",
                        $sformatf("Unexpected AXI read response 0x%0X at ADDR=0x%08X", rresp, axi_tr.addr))
                    return 0;
                end

                expected_error_count++;
                `uvm_info("SCOREBOARD",
                    $sformatf("Expected error read observed: ADDR=0x%08X RRESP=0x%0X (bridge_enable=%0b expect_error=%0b)",
                              axi_tr.addr, rresp, bridge_enabled, expect_error),
                    UVM_MEDIUM)
                return 1;
            end

            if (require_error) begin
                // Track bridge disable related read errors specifically
                if (!bridge_enabled && !expect_error) begin
                    bridge_disable_error_count++;
                    `uvm_error("SCOREBOARD",
                        $sformatf("BRIDGE_DISABLE_ERROR: Expected AXI error on read at ADDR=0x%08X but RRESP=0 (bridge_enable=%0b expect_error=%0b) [bridge_disable_error #%0d]",
                                  axi_tr.addr, bridge_enabled, expect_error, bridge_disable_error_count))
                end else begin
                    `uvm_error("SCOREBOARD",
                        $sformatf("Expected AXI error on read at ADDR=0x%08X but RRESP=0 (bridge_enable=%0b expect_error=%0b)",
                                  axi_tr.addr, bridge_enabled, expect_error))
                end
                return 0;
            end
        end

        return 1;
    endfunction
    
    // Calculate expected WSTRB based on address and size
    virtual function logic [3:0] calculate_expected_wstrb(logic [31:0] addr, logic [1:0] size);
        case (size)
            2'b00: return 4'b0001 << addr[1:0];        // 8-bit
            2'b01: return addr[1] ? 4'b1100 : 4'b0011; // 16-bit
            2'b10: return 4'b1111;                     // 32-bit
            default: return 4'b0000;                   // Invalid
        endcase
    endfunction
    
    // Verify write data matches between UART and AXI
    virtual function bit verify_write_data(uart_axi4_expected_transaction expectation,
                                           int beat_index,
                                           axi4_lite_transaction axi_tr);
        logic [31:0] expected_wdata;
        logic [31:0] wstrb_mask;

        expected_wdata = expectation.expected_wdata[beat_index];
        wstrb_mask = expand_wstrb_mask(axi_tr.wstrb);

        if ( (axi_tr.wdata & wstrb_mask) != (expected_wdata & wstrb_mask) ) begin
            `uvm_error("SCOREBOARD",
                $sformatf("Write data mismatch at beat %0d: expected 0x%08X, got 0x%08X (mask 0x%08X)",
                          beat_index + 1, expected_wdata, axi_tr.wdata, wstrb_mask))
            return 0;
        end

        return 1;
    endfunction

    virtual function logic [31:0] expand_wstrb_mask(logic [3:0] wstrb);
        logic [31:0] mask;
        int i;

        mask = 32'h0;
        for (i = 0; i < 4; i++) begin
            if (wstrb[i]) begin
                mask[(i * 8) +: 8] = 8'hFF;
            end
        end

        return mask;
    endfunction

    virtual function int bytes_per_beat_from_size(logic [1:0] size);
        case (size)
            2'b00: return 1;
            2'b01: return 2;
            2'b10: return 4;
            default: return 0;
        endcase
    endfunction

    virtual function logic [31:0] build_expected_wdata(uart_frame_transaction uart_tr,
                                                       int beat_index,
                                                       int bytes_per_beat,
                                                       logic [31:0] beat_addr);
        logic [31:0] data_word;
        int data_base;

        data_word = 32'h0;
        data_base = beat_index * bytes_per_beat;

        case (bytes_per_beat)
            1: begin
                if (data_base < uart_tr.data.size()) begin
                    int lane;
                    lane = beat_addr[1:0];
                    data_word[(lane * 8) +: 8] = uart_tr.data[data_base];
                end
            end
            2: begin
                logic [7:0] byte0;
                logic [7:0] byte1;
                byte0 = (data_base < uart_tr.data.size()) ? uart_tr.data[data_base] : 8'h00;
                byte1 = (data_base + 1 < uart_tr.data.size()) ? uart_tr.data[data_base + 1] : 8'h00;

                if (beat_addr[1] == 1'b0) begin
                    data_word[7:0]   = byte0;
                    data_word[15:8]  = byte1;
                end else begin
                    data_word[23:16] = byte0;
                    data_word[31:24] = byte1;
                end
            end
            4: begin
                int byte_idx;
                for (byte_idx = 0; byte_idx < 4; byte_idx++) begin
                    if (data_base + byte_idx < uart_tr.data.size()) begin
                        data_word[(byte_idx * 8) +: 8] = uart_tr.data[data_base + byte_idx];
                    end
                end
            end
            default: begin
                // Unsupported sizes are handled earlier.
            end
        endcase

        return data_word;
    endfunction
    
    // Bridge state-aware transaction validation
    virtual function bit is_bridge_state_valid_for_transaction(uart_axi4_expected_transaction expectation, int beat_index);
        time time_since_transition;
        bit bridge_enabled;
        
        // Get current bridge state
        if (cfg.bridge_status_vif != null) begin
            bridge_enabled = cfg.bridge_status_vif.bridge_enable;
        end else begin
            bridge_enabled = 1'b1; // Default to enabled if no interface
        end
        
        time_since_transition = $time - last_bridge_enable_change_time;
        
        // If bridge is disabled, allow limited transactions but with extended tolerance
        if (!bridge_enabled) begin
            if (beat_index >= MAX_BRIDGE_DISABLE_WINDOW_BEATS) begin
                `uvm_info("SCOREBOARD_BRIDGE_STATE",
                    $sformatf("Bridge disable window exceeded for ADDR=0x%08X beat=%0d (max=%0d)",
                              expectation.beat_addr[beat_index], beat_index, MAX_BRIDGE_DISABLE_WINDOW_BEATS),
                    UVM_MEDIUM)
                return 0; // Too many beats during disable window
            end
            return 1; // Allow transaction during disable window
        end
        
        // If bridge was recently re-enabled, allow settle time
        if (time_since_transition < BRIDGE_TRANSITION_SETTLE_TIME) begin
            `uvm_info("SCOREBOARD_BRIDGE_STATE",
                $sformatf("Bridge transition settle time: %0t < %0t for ADDR=0x%08X",
                          time_since_transition, BRIDGE_TRANSITION_SETTLE_TIME, expectation.beat_addr[beat_index]),
                UVM_HIGH)
            return 0; // Wait for bridge to settle
        end
        
        return 1; // Normal operation - bridge enabled and settled
    endfunction
    
    // Calculate effective timeout considering bridge state
    virtual function time get_effective_timeout(uart_axi4_expected_transaction expectation, time base_timeout);
        bit bridge_enabled;
        time effective_timeout;
        time time_since_transition;
        
        // Get current bridge state
        if (cfg.bridge_status_vif != null) begin
            bridge_enabled = cfg.bridge_status_vif.bridge_enable;
        end else begin
            bridge_enabled = 1'b1;
        end
        
        effective_timeout = base_timeout;
        time_since_transition = $time - last_bridge_enable_change_time;
        
        // Extend timeout during bridge disable windows
        if (!bridge_enabled) begin
            effective_timeout += BRIDGE_DISABLE_TIMEOUT_EXTENSION;
            `uvm_info("SCOREBOARD_BRIDGE_STATE",
                $sformatf("Extended timeout for bridge disable: %0t + %0t = %0t for CMD=0x%02X",
                          base_timeout, BRIDGE_DISABLE_TIMEOUT_EXTENSION, effective_timeout, expectation.uart_tr.cmd),
                UVM_HIGH)
        end
        
        // Extend timeout immediately after bridge re-enable
        if (bridge_enabled && time_since_transition < BRIDGE_TRANSITION_SETTLE_TIME * 2) begin
            effective_timeout += BRIDGE_TRANSITION_SETTLE_TIME;
            `uvm_info("SCOREBOARD_BRIDGE_STATE",
                $sformatf("Extended timeout for bridge recovery: %0t + %0t = %0t for CMD=0x%02X",
                          base_timeout, BRIDGE_TRANSITION_SETTLE_TIME, effective_timeout, expectation.uart_tr.cmd),
                UVM_HIGH)
        end
        
        return effective_timeout;
    endfunction

    virtual function uart_axi4_expected_transaction build_expected_transaction(uart_frame_transaction uart_tr);
        uart_axi4_expected_transaction expectation;
        int bytes_per_beat;
        int beats_total;
        int beat;

        expectation = new();
        expectation.uart_tr = uart_tr;
        expectation.is_write = !uart_tr.cmd[7];
        expectation.auto_increment = uart_tr.cmd[6];
        expectation.size = uart_tr.cmd[5:4];
        expectation.expect_error = uart_tr.expect_error;

        bytes_per_beat = bytes_per_beat_from_size(expectation.size);
        if (bytes_per_beat == 0) begin
            `uvm_error("SCOREBOARD",
                $sformatf("Unsupported transfer size in UART command CMD=0x%02X", uart_tr.cmd))
            return null;
        end

        beats_total = int'(uart_tr.cmd[3:0]) + 1;
        expectation.bytes_per_beat = bytes_per_beat;
        expectation.beats_total = beats_total;
        expectation.next_index = 0;
        expectation.beat_addr = new[beats_total];
        expectation.expected_wstrb = new[beats_total];
        expectation.expected_wdata = new[beats_total];

        for (beat = 0; beat < beats_total; beat++) begin
            logic [31:0] beat_addr;
            beat_addr = uart_tr.addr;
            if (expectation.auto_increment) begin
                logic [31:0] beat_offset;
                beat_offset = beat * bytes_per_beat;
                beat_addr = uart_tr.addr + beat_offset;
            end

            expectation.beat_addr[beat] = beat_addr;

            if (expectation.is_write) begin
                expectation.expected_wstrb[beat] = calculate_expected_wstrb(beat_addr, expectation.size);
                expectation.expected_wdata[beat] = build_expected_wdata(uart_tr, beat, bytes_per_beat, beat_addr);
            end else begin
                expectation.expected_wstrb[beat] = 4'b0000;
                expectation.expected_wdata[beat] = 32'h0;
            end
        end

        return expectation;
    endfunction

    virtual function void handle_uart_response(uart_frame_transaction tr);
        if (tr.parse_error_kind != PARSE_ERROR_NONE) begin
            `uvm_warning("SCOREBOARD",
                $sformatf("Skipping UART_TX frame due to monitor parse error: %s", tr.parse_error_kind.name()))
            return;
        end

        uart_device_responses_received++;

        if (!tr.response_received) begin
            uart_status_error_count++;
            `uvm_warning("SCOREBOARD", "UART response without status payload detected")
            return;
        end

        case (tr.response_status)
            STATUS_OK: begin
                uart_status_ok_count++;
                `uvm_info("SCOREBOARD",
                    $sformatf("UART response OK for CMD=0x%02X", tr.cmd),
                    UVM_MEDIUM)
            end
            STATUS_BUSY: begin
                uart_status_busy_count++;
                `uvm_info("SCOREBOARD",
                    $sformatf("UART response BUSY for CMD=0x%02X", tr.cmd),
                    UVM_MEDIUM)
            end
            default: begin
                uart_status_error_count++;
                `uvm_warning("SCOREBOARD",
                    $sformatf("UART response error status=0x%02X for CMD=0x%02X", tr.response_status, tr.cmd))
            end
        endcase

        if (!tr.crc_valid) begin
            `uvm_warning("SCOREBOARD",
                $sformatf("UART response CRC invalid for CMD=0x%02X", tr.cmd))
        end
    endfunction
    
    // Final phase - report statistics
    virtual function void final_phase(uvm_phase phase);
        int pending_uart_commands;
        int pending_uart_beats;
        int idx;

        pending_uart_commands = uart_expectations.size();
        pending_uart_beats = 0;

        for (idx = 0; idx < uart_expectations.size(); idx++) begin
            pending_uart_beats += uart_expectations[idx].remaining_beats();
        end

        `uvm_info("SCOREBOARD", "=== SCOREBOARD FINAL REPORT ===", UVM_LOW)
        `uvm_info("SCOREBOARD", $sformatf("UART transactions received: %0d", uart_transactions_received), UVM_LOW)
        `uvm_info("SCOREBOARD", $sformatf("UART device responses received: %0d (OK=%0d, BUSY=%0d, Error=%0d)",
                  uart_device_responses_received, uart_status_ok_count, uart_status_busy_count, uart_status_error_count), UVM_LOW)
        `uvm_info("SCOREBOARD", $sformatf("AXI transactions received: %0d", axi4_lite_transactions_received), UVM_LOW)
        `uvm_info("SCOREBOARD", $sformatf("Error-injected UART frames ignored: %0d", error_frame_count), UVM_LOW)
        `uvm_info("SCOREBOARD", $sformatf("Expected error transactions observed: %0d", expected_error_count), UVM_LOW)
        `uvm_info("SCOREBOARD", $sformatf("Matches found: %0d", match_count), UVM_LOW)
        `uvm_info("SCOREBOARD", $sformatf("Mismatches found: %0d", mismatch_count), UVM_LOW)
        
        // Bridge enable state correlation statistics  
        `uvm_info("SCOREBOARD", "=== BRIDGE STATE CORRELATION REPORT ===", UVM_LOW)
        `uvm_info("SCOREBOARD", $sformatf("Bridge enable state transitions: %0d", bridge_enable_transitions), UVM_LOW)
        `uvm_info("SCOREBOARD", $sformatf("Transactions with bridge disabled: %0d", transactions_with_bridge_disabled), UVM_LOW)
        `uvm_info("SCOREBOARD", $sformatf("Bridge disable related errors: %0d", bridge_disable_error_count), UVM_LOW)
        if (last_bridge_enable_change_time > 0) begin
            `uvm_info("SCOREBOARD", $sformatf("Last bridge state change at time: %0t", last_bridge_enable_change_time), UVM_LOW)
        end
        
        // Bridge state-aware validation statistics
        if (bridge_enable_transitions > 0) begin
            real bridge_error_rate = real'(bridge_disable_error_count) / real'(transactions_with_bridge_disabled + 1) * 100.0;
            `uvm_info("SCOREBOARD", $sformatf("Bridge disable error rate: %0.1f%% (%0d errors / %0d transactions)",
                      bridge_error_rate, bridge_disable_error_count, transactions_with_bridge_disabled), UVM_LOW)
        end
        
        // Current bridge state
        if (cfg.bridge_status_vif != null) begin
            `uvm_info("SCOREBOARD", $sformatf("Final bridge enable state: %0b", cfg.bridge_status_vif.bridge_enable), UVM_LOW)
        end
        
        `uvm_info("SCOREBOARD", $sformatf("Pending UART commands: %0d (remaining beats=%0d)", pending_uart_commands, pending_uart_beats), UVM_LOW)
        `uvm_info("SCOREBOARD", $sformatf("Unmatched AXI transactions: %0d", axi_queue.size()), UVM_LOW)
        
        if (mismatch_count > 0) begin
            `uvm_error("SCOREBOARD", "Test failed due to transaction mismatches")
        end
        
        if (pending_uart_beats > 0) begin
            `uvm_warning("SCOREBOARD", $sformatf("Unmatched UART command beats remaining: %0d", pending_uart_beats))
        end

        if (axi_queue.size() > 0) begin
            `uvm_warning("SCOREBOARD", "Unmatched AXI transactions remain in queue")
        end
    endfunction

endclass
