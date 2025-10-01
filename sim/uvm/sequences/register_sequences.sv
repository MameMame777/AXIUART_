`timescale 1ns / 1ps

`include "uvm_macros.svh"
import uvm_pkg::*;
import uart_axi4_test_pkg::*;

// Register address definitions
localparam bit [31:0] REG_BASE_ADDR = 32'h0000_1000;
localparam bit [31:0] REG_CONTROL   = REG_BASE_ADDR + 32'h000;
localparam bit [31:0] REG_STATUS    = REG_BASE_ADDR + 32'h004;
localparam bit [31:0] REG_CONFIG    = REG_BASE_ADDR + 32'h008;
localparam bit [31:0] REG_DEBUG     = REG_BASE_ADDR + 32'h00C;
localparam bit [31:0] REG_TX_COUNT  = REG_BASE_ADDR + 32'h010;
localparam bit [31:0] REG_RX_COUNT  = REG_BASE_ADDR + 32'h014;
localparam bit [31:0] REG_FIFO_STAT = REG_BASE_ADDR + 32'h018;
localparam bit [31:0] REG_VERSION   = REG_BASE_ADDR + 32'h01C;

// Base class providing shared helpers for UART-driven register sequences
virtual class register_uart_sequence_base extends uvm_sequence #(uart_frame_transaction);

    // CONTROL register timing constants shared across disable/enable flows
    protected static const time CONTROL_POST_CMD_DELAY_NS        = 120ns;
    protected static const time CONTROL_DISABLE_WINDOW_NS       = 600ns;
    protected static const time CONTROL_DISABLE_HOLD_NS         = 1200ns;
    protected static const time CONTROL_READBACK_DELAY_NS       = 80ns;
    protected static const time CONTROL_READBACK_RETRY_DELAY_NS = 600ns;
    protected static const int  CONTROL_READBACK_MAX_ATTEMPTS   = 3;
    protected static const int  CONTROL_PARTIAL_RETRY_EXTENSION = 2;
    protected static const int  CONTROL_PARTIAL_BACKOFF_MULTIPLIER = 4;
    protected static const time CONTROL_PARTIAL_BACKOFF_NS = CONTROL_DISABLE_HOLD_NS +
        (CONTROL_READBACK_RETRY_DELAY_NS * CONTROL_PARTIAL_BACKOFF_MULTIPLIER);

    function new(string name = "register_uart_sequence_base");
        super.new(name);
    endfunction

    protected task automatic drive_write_core(string txn_label,
                                              bit [31:0] addr,
                                              bit [31:0] value,
                                              int unsigned byte_count,
                                              bit expect_error = 0,
                                              output uart_frame_transaction req);
        req = uart_frame_transaction::type_id::create(txn_label);
        start_item(req);

        req.is_write = 1;
        req.auto_increment = 0;
        req.size = infer_size(byte_count);
        req.length = 4'h0; // Single beat
        req.addr = addr;
        req.sof = SOF_HOST_TO_DEVICE;
        req.direction = UART_RX;
        req.error_inject = 0;
        req.expect_error = expect_error;
        assign_data(req, value, byte_count);
        req.build_cmd();
        req.calculate_crc();

        finish_item(req);
    endtask

    protected task automatic drive_read_core(string txn_label,
                                             bit [31:0] addr,
                                             int unsigned byte_count,
                                             bit expect_error,
                                             output uart_frame_transaction req);
        req = uart_frame_transaction::type_id::create(txn_label);
        start_item(req);

        req.is_write = 0;
        req.auto_increment = 0;
        req.size = infer_size(byte_count);
        req.length = 4'h0;
        req.addr = addr;
        req.sof = SOF_HOST_TO_DEVICE;
        req.direction = UART_RX;
        req.error_inject = 0;
        req.expect_error = expect_error;
        req.data = new[0];
        req.build_cmd();
        req.calculate_crc();

        finish_item(req);

        if (expect_error) begin
            `uvm_info(get_type_name(),
                $sformatf("Issued expected-error read from 0x%08X", addr), UVM_MEDIUM)
        end else begin
            `uvm_info(get_type_name(),
                $sformatf("Read request (%0d bytes) from 0x%08X", byte_count, addr),
                UVM_MEDIUM)
        end
    endtask

    protected task automatic drive_control_write_with_trace(string stage_label,
                                                             bit [31:0] value,
                                                             int unsigned byte_count,
                                                             bit perform_readback,
                                                             bit expected_enable_bit,
                                                             bit allow_busy = 1'b0);
        uart_frame_transaction ctrl_req;
        time issue_time_ns;

    drive_write_core({stage_label, "_control_write"}, REG_CONTROL, value, byte_count,
             /*expect_error=*/0, ctrl_req);
        issue_time_ns = $time / 1ns;

        `uvm_info("CONTROL_TRACE",
            $sformatf("[%s] CONTROL write value=0x%08X CMD=0x%02X (%0d bytes) at %0t ns",
                      stage_label, value, ctrl_req.cmd, byte_count, issue_time_ns),
            UVM_MEDIUM);

        if (perform_readback) begin
            #(CONTROL_READBACK_DELAY_NS);
            verify_control_readback(stage_label, byte_count, expected_enable_bit, allow_busy);
        end
    endtask

    protected task automatic verify_control_readback(string stage_label,
                                                      int unsigned byte_count,
                                                      bit expected_enable_bit,
                                                      bit allow_busy);
        uart_frame_transaction rd_req;
        bit [31:0] observed_value;
        int limit_bytes;
        time read_time_ns;
        int unsigned resp_size;
        bit short_read;
        bit empty_read;
        int partial_retry_budget;

        partial_retry_budget = CONTROL_PARTIAL_RETRY_EXTENSION;

        for (int attempt = 0; attempt < CONTROL_READBACK_MAX_ATTEMPTS; attempt++) begin
            string attempt_label;

            attempt_label = $sformatf("%s_control_read_attempt%0d", stage_label, attempt);
            drive_read_core(attempt_label, REG_CONTROL, byte_count, /*expect_error=*/0, rd_req);
            read_time_ns = $time / 1ns;

            `uvm_info("CONTROL_TRACE",
                $sformatf("[%s] CONTROL read attempt %0d issued CMD=0x%02X at %0t ns",
                          stage_label, attempt, rd_req.cmd, read_time_ns),
                UVM_MEDIUM);

            if (!rd_req.response_received) begin
                `uvm_error("CONTROL_TRACE",
                    $sformatf("[%s] CONTROL read attempt %0d did not receive a response",
                              stage_label, attempt));
                return;
            end

            if (rd_req.response_status == STATUS_BUSY) begin
                `uvm_info("CONTROL_TRACE",
                    $sformatf("[%s] CONTROL read reported STATUS_BUSY (0x%02X) on attempt %0d",
                              stage_label, rd_req.response_status, attempt),
                    UVM_MEDIUM);

                if (allow_busy) begin
                    return;
                end

                if (attempt == CONTROL_READBACK_MAX_ATTEMPTS - 1) begin
                    `uvm_error("CONTROL_TRACE",
                        $sformatf("[%s] CONTROL remained busy after %0d attempts",
                                  stage_label, CONTROL_READBACK_MAX_ATTEMPTS));
                    return;
                end

                hold_bridge_disabled({stage_label, "_busy_retry_hold"}, CONTROL_READBACK_RETRY_DELAY_NS);
                continue;
            end

            if (rd_req.response_status != STATUS_OK) begin
                `uvm_error("CONTROL_TRACE",
                    $sformatf("[%s] CONTROL read returned status 0x%02X on attempt %0d",
                              stage_label, rd_req.response_status, attempt));
                return;
            end

            resp_size = rd_req.response_data.size();
            short_read = (resp_size < byte_count);
            empty_read = (resp_size == 0);

            if (short_read) begin
                `uvm_warning("CONTROL_TRACE",
                    $sformatf("[%s] CONTROL read returned %0d byte(s); expected %0d",
                              stage_label, resp_size, byte_count));

                if (allow_busy) begin
                    `uvm_info("CONTROL_TRACE",
                        $sformatf("[%s] Allowing short CONTROL read because allow_busy=1", stage_label),
                        UVM_MEDIUM);
                    return;
                end

                if (empty_read) begin
                    if (attempt == CONTROL_READBACK_MAX_ATTEMPTS - 1) begin
                        `uvm_error("CONTROL_TRACE",
                            $sformatf("[%s] CONTROL read never produced data after %0d attempts",
                                      stage_label, CONTROL_READBACK_MAX_ATTEMPTS));
                        return;
                    end

                    wait_for_bridge_recovery({stage_label, "_short_read_retry"}, CONTROL_READBACK_RETRY_DELAY_NS);
                    continue;
                end
            end

            observed_value = '0;
            limit_bytes = (resp_size < byte_count) ? resp_size : byte_count;
            for (int i = 0; i < limit_bytes; i++) begin
                observed_value[8*i +: 8] = rd_req.response_data[i];
            end

            `uvm_info("CONTROL_TRACE",
                $sformatf("[%s] CONTROL read observed_value=0x%08X", stage_label, observed_value),
                UVM_MEDIUM);

            if (short_read && !allow_busy && !empty_read) begin
                if (observed_value[0] === expected_enable_bit) begin
                    `uvm_warning("CONTROL_TRACE",
                        $sformatf("[%s] CONTROL read confirmed enable bit with truncated payload (%0d byte(s))",
                                  stage_label, resp_size));
                    `uvm_info("CONTROL_TRACE",
                        $sformatf("[%s] CONTROL bridge_enable confirmed as %0b", stage_label, observed_value[0]),
                        UVM_MEDIUM);
                    return;
                end

                if (attempt < CONTROL_READBACK_MAX_ATTEMPTS - 1) begin
                    `uvm_info("CONTROL_TRACE",
                        $sformatf("[%s] CONTROL read truncated payload (%0d byte(s)) — retrying after %0t ns",
                                  stage_label, resp_size, CONTROL_READBACK_RETRY_DELAY_NS / 1ns),
                        UVM_MEDIUM);
                    wait_for_bridge_recovery({stage_label, "_short_read_retry"}, CONTROL_READBACK_RETRY_DELAY_NS);
                    continue;
                end

                if (partial_retry_budget > 0) begin
                    partial_retry_budget--;
                    `uvm_warning("CONTROL_TRACE",
                        $sformatf("[%s] CONTROL read truncated payload with mismatched enable bit — extending backoff (%0d byte(s))",
                                  stage_label, resp_size));
                    `uvm_info("CONTROL_TRACE",
                        $sformatf("[%s] Applying extended CONTROL quiet time of %0t ns before retry (remaining partial retries: %0d)",
                                  stage_label, CONTROL_PARTIAL_BACKOFF_NS / 1ns, partial_retry_budget),
                        UVM_MEDIUM);
                    wait_for_bridge_recovery({stage_label, "_partial_retry_backoff"}, CONTROL_PARTIAL_BACKOFF_NS);
                    attempt--;
                    continue;
                end

                `uvm_warning("CONTROL_TRACE",
                    $sformatf("[%s] CONTROL bridge_enable could not be confirmed due to persistent truncated payload (observed=%0b expected=%0b)",
                              stage_label, observed_value[0], expected_enable_bit));
                `uvm_info("CONTROL_TRACE",
                    $sformatf("[%s] Deferring CONTROL enable verification to bridge_status_monitor after exhausting retries", stage_label),
                    UVM_LOW);
                return;
            end

            if (!short_read && observed_value[31:1] !== '0) begin
                `uvm_error("CONTROL_TRACE",
                    $sformatf("[%s] CONTROL read observed reserved bits set: 0x%08X", stage_label, observed_value));
                return;
            end

            if (observed_value[0] !== expected_enable_bit) begin
                if (attempt == CONTROL_READBACK_MAX_ATTEMPTS - 1) begin
                    `uvm_error("CONTROL_TRACE",
                        $sformatf("[%s] CONTROL bridge_enable mismatch: observed=%0b expected=%0b", stage_label,
                                  observed_value[0], expected_enable_bit));
                    return;
                end

                `uvm_info("CONTROL_TRACE",
                    $sformatf("[%s] CONTROL bridge_enable observed=%0b expected=%0b — retrying",
                              stage_label, observed_value[0], expected_enable_bit),
                    UVM_MEDIUM);
                wait_for_bridge_recovery({stage_label, "_enable_retry"}, CONTROL_READBACK_RETRY_DELAY_NS);
                continue;
            end

            `uvm_info("CONTROL_TRACE",
                $sformatf("[%s] CONTROL bridge_enable confirmed as %0b", stage_label, observed_value[0]),
                UVM_MEDIUM);

            return;
        end
    endtask

    protected task automatic hold_bridge_disabled(string label, time hold_duration_ns);
        time hold_start_ns;

        hold_start_ns = $time / 1ns;
        `uvm_info("CONTROL_TRACE",
            $sformatf("[%s] Holding bridge_enable low for %0t ns starting at %0t ns",
                      label, hold_duration_ns / 1ns, hold_start_ns),
            UVM_MEDIUM);
        #(hold_duration_ns);
    endtask

    protected task automatic wait_for_bridge_recovery(string label, time wait_duration_ns);
        time wait_start_ns;

        wait_start_ns = $time / 1ns;
        `uvm_info("CONTROL_TRACE",
            $sformatf("[%s] Waiting for bridge recovery for %0t ns starting at %0t ns",
                      label, wait_duration_ns / 1ns, wait_start_ns),
            UVM_MEDIUM);
        #(wait_duration_ns);
    endtask

    protected task automatic drive_write(bit [31:0] addr, bit [31:0] value, int unsigned byte_count,
                                         bit expect_error = 0);
        uart_frame_transaction req;
        drive_write_core("reg_write", addr, value, byte_count, expect_error, req);

        if (expect_error) begin
            `uvm_info(get_type_name(),
                $sformatf("Issued expected-error write to 0x%08X", addr), UVM_MEDIUM)
        end else begin
            `uvm_info(get_type_name(),
                $sformatf("Write 0x%08X (%0d bytes) to 0x%08X (CMD=0x%02X)",
                          value, byte_count, addr, req.cmd),
                UVM_MEDIUM)
        end
    endtask

    protected task automatic drive_read(bit [31:0] addr, int unsigned byte_count,
                                        bit expect_error = 0);
        uart_frame_transaction req;
        drive_read_core("reg_read", addr, byte_count, expect_error, req);
    endtask

    protected task automatic drive_burst(bit [31:0] base_addr, int unsigned byte_count,
                                         int unsigned beats, bit auto_increment);
        uart_frame_transaction req;
        int unsigned total_bytes = byte_count * beats;

        req = uart_frame_transaction::type_id::create("reg_burst");
        start_item(req);

        req.is_write = 1;
        req.auto_increment = auto_increment;
        req.size = infer_size(byte_count);
        req.length = beats - 1;
        req.addr = base_addr;
        req.sof = SOF_HOST_TO_DEVICE;
        req.direction = UART_RX;
        req.error_inject = 0;
        req.expect_error = 0;
        req.data = new[total_bytes];
        for (int i = 0; i < total_bytes; i++) begin
            req.data[i] = $urandom_range(0, 255);
        end
        req.build_cmd();
        req.calculate_crc();

        finish_item(req);

        `uvm_info(get_type_name(),
            $sformatf("Burst write: %0d beats (%0d bytes) starting at 0x%08X (auto_inc=%0d)",
                      beats, total_bytes, base_addr, auto_increment),
            UVM_MEDIUM)
    endtask

    protected task automatic assign_data(ref uart_frame_transaction req,
                                         bit [31:0] value,
                                         int unsigned byte_count);
        req.data = new[byte_count];
        for (int i = 0; i < byte_count; i++) begin
            req.data[i] = value[8*i +: 8];
        end
    endtask

    protected function automatic logic [1:0] infer_size(int unsigned byte_count);
        case (byte_count)
            1: return 2'b00;
            2: return 2'b01;
            default: return 2'b10;
        endcase
    endfunction
endclass

// Basic register read/write sequence
class register_basic_rw_sequence extends uvm_sequence #(axi4_lite_transaction);
    `uvm_object_utils(register_basic_rw_sequence)

    function new(string name = "register_basic_rw_sequence");
        super.new(name);
    endfunction

    rand bit [31:0] test_addr;
    rand bit [31:0] test_data;

    constraint c_addr_valid { 
        test_addr inside {REG_CONTROL, REG_CONFIG, REG_DEBUG}; 
    }
    
    constraint c_data_valid {
        test_data[31:16] == 16'h0000; // Upper bits should be 0 for most registers
    }

    virtual task body();
        axi4_lite_transaction write_trans, read_trans;
        bit [31:0] read_data;
        
        `uvm_info("REG_SEQ", $sformatf("Starting register R/W test at addr=0x%08X, data=0x%08X", test_addr, test_data), UVM_MEDIUM)
        
        // Write to register
        `uvm_do_with(write_trans, {
            write_trans.addr == test_addr;
            write_trans.data == test_data;
            write_trans.trans_type == AXI_WRITE;
            write_trans.strb == 4'hF;
            write_trans.resp == 2'b00;
        })
        
        // Read back from register
        `uvm_do_with(read_trans, {
            read_trans.addr == test_addr;
            read_trans.trans_type == AXI_READ;
            read_trans.resp == 2'b00;
        })
        
        read_data = read_trans.data;
        
        // Check write/read consistency for writable registers
        case (test_addr)
            REG_CONTROL: begin
                // Only bit 0 is writable, bit 1 is W1C (always reads 0)
                if (read_data[0] !== test_data[0] || read_data[31:1] !== 31'b0) begin
                    `uvm_error("REG_SEQ", $sformatf("CONTROL register mismatch: W=0x%08X, R=0x%08X", test_data, read_data))
                end else begin
                    `uvm_info("REG_SEQ", $sformatf("CONTROL register OK: R=0x%08X", read_data), UVM_MEDIUM)
                end
            end
            
            REG_CONFIG: begin
                // Bits 15:0 are writable
                bit [15:0] expected_config = test_data[15:0];
                if (read_data[15:0] !== expected_config || read_data[31:16] !== 16'b0) begin
                    `uvm_error("REG_SEQ", $sformatf("CONFIG register mismatch: W=0x%08X, R=0x%08X", test_data, read_data))
                end else begin
                    `uvm_info("REG_SEQ", $sformatf("CONFIG register OK: R=0x%08X", read_data), UVM_MEDIUM)
                end
            end
            
            REG_DEBUG: begin
                // Bits 3:0 are writable
                bit [3:0] expected_debug = test_data[3:0];
                if (read_data[3:0] !== expected_debug || read_data[31:4] !== 28'b0) begin
                    `uvm_error("REG_SEQ", $sformatf("DEBUG register mismatch: W=0x%08X, R=0x%08X", test_data, read_data))
                end else begin
                    `uvm_info("REG_SEQ", $sformatf("DEBUG register OK: R=0x%08X", read_data), UVM_MEDIUM)
                end
            end
            
            default: begin
                `uvm_warning("REG_SEQ", $sformatf("Unexpected register address: 0x%08X", test_addr))
            end
        endcase
    endtask
endclass

// Register reset test sequence
class register_reset_sequence extends uvm_sequence #(axi4_lite_transaction);
    `uvm_object_utils(register_reset_sequence)

    function new(string name = "register_reset_sequence");
        super.new(name);
    endfunction

    virtual task body();
        axi4_lite_transaction read_trans;
        
        `uvm_info("REG_SEQ", "Starting register reset value test", UVM_MEDIUM)
        
        // Check reset values of all registers
        check_register_reset_value(REG_CONTROL, 32'h0000_0000, "CONTROL");
        check_register_reset_value(REG_STATUS, 32'h0000_0000, "STATUS");
        check_register_reset_value(REG_CONFIG, 32'h0000_0000, "CONFIG");
        check_register_reset_value(REG_DEBUG, 32'h0000_0000, "DEBUG");
        check_register_reset_value(REG_TX_COUNT, 32'h0000_0000, "TX_COUNT");
        check_register_reset_value(REG_RX_COUNT, 32'h0000_0000, "RX_COUNT");
        check_register_reset_value(REG_FIFO_STAT, 32'h0000_0000, "FIFO_STAT");
        check_register_reset_value(REG_VERSION, 32'h0001_0000, "VERSION");
    endtask
    
    task check_register_reset_value(bit [31:0] addr, bit [31:0] expected, string name);
        axi4_lite_transaction read_trans;
        
        `uvm_do_with(read_trans, {
            read_trans.addr == addr;
            read_trans.trans_type == AXI_READ;
            read_trans.resp == 2'b00;
        })
        
        if (read_trans.data !== expected) begin
            `uvm_error("REG_SEQ", $sformatf("%s reset value mismatch: Expected=0x%08X, Actual=0x%08X", 
                       name, expected, read_trans.data))
        end else begin
            `uvm_info("REG_SEQ", $sformatf("%s reset value OK: 0x%08X", name, read_trans.data), UVM_MEDIUM)
        end
    endtask
endclass

// Register access protection test sequence
class register_access_test_sequence extends uvm_sequence #(axi4_lite_transaction);
    `uvm_object_utils(register_access_test_sequence)

    function new(string name = "register_access_test_sequence");
        super.new(name);
    endfunction

    virtual task body();
        `uvm_info("REG_SEQ", "Starting register access protection test", UVM_MEDIUM)
        
        // Test read-only registers (writes should be ignored)
        test_read_only_register(REG_STATUS, "STATUS");
        test_read_only_register(REG_TX_COUNT, "TX_COUNT");
        test_read_only_register(REG_RX_COUNT, "RX_COUNT");
        test_read_only_register(REG_FIFO_STAT, "FIFO_STAT");
        test_read_only_register(REG_VERSION, "VERSION");
        
        // Test invalid addresses (should return SLVERR)
        test_invalid_address(REG_BASE_ADDR + 32'h020);
        test_invalid_address(REG_BASE_ADDR + 32'hFFC);
        test_invalid_address(REG_BASE_ADDR + 32'h1000);
        
        // Test unaligned addresses (should return SLVERR)
        test_unaligned_address(REG_CONTROL + 1);
        test_unaligned_address(REG_CONFIG + 2);
        test_unaligned_address(REG_DEBUG + 3);
    endtask
    
    task test_read_only_register(bit [31:0] addr, string name);
        axi4_lite_transaction write_trans, read_trans;
        bit [31:0] original_value, test_value, final_value;
        
        // Read original value
        `uvm_do_with(read_trans, {
            read_trans.addr == addr;
            read_trans.trans_type == AXI_READ;
            read_trans.resp == 2'b00;
        })
        original_value = read_trans.data;
        
        // Try to write different value
        test_value = ~original_value;
        `uvm_do_with(write_trans, {
            write_trans.addr == addr;
            write_trans.data == test_value;
            write_trans.trans_type == AXI_WRITE;
            write_trans.strb == 4'hF;
            write_trans.resp == 2'b00;
        })
        
        // Read final value
        `uvm_do_with(read_trans, {
            read_trans.addr == addr;
            read_trans.trans_type == AXI_READ;
            read_trans.resp == 2'b00;
        })
        final_value = read_trans.data;
        
        if (final_value !== original_value) begin
            `uvm_error("REG_SEQ", $sformatf("%s register is not read-only: Original=0x%08X, Final=0x%08X", 
                       name, original_value, final_value))
        end else begin
            `uvm_info("REG_SEQ", $sformatf("%s register correctly read-only", name), UVM_MEDIUM)
        end
    endtask
    
    task test_invalid_address(bit [31:0] addr);
        axi4_lite_transaction read_trans, write_trans;
        
        // Test invalid read
        `uvm_do_with(read_trans, {
            read_trans.addr == addr;
            read_trans.trans_type == AXI_READ;
            read_trans.resp == 2'b10;
        })
        
        if (read_trans.resp !== 2'b10) begin // SLVERR expected
            `uvm_error("REG_SEQ", $sformatf("Invalid read address 0x%08X should return SLVERR, got 0x%02X", 
                       addr, read_trans.resp))
        end else begin
            `uvm_info("REG_SEQ", $sformatf("Invalid read address 0x%08X correctly returned SLVERR", addr), UVM_MEDIUM)
        end
        
        // Test invalid write
        `uvm_do_with(write_trans, {
            write_trans.addr == addr;
            write_trans.data == 32'hDEADBEEF;
            write_trans.trans_type == AXI_WRITE;
            write_trans.strb == 4'hF;
            write_trans.resp == 2'b10;
        })
        
        if (write_trans.resp !== 2'b10) begin // SLVERR expected
            `uvm_error("REG_SEQ", $sformatf("Invalid write address 0x%08X should return SLVERR, got 0x%02X", 
                       addr, write_trans.resp))
        end else begin
            `uvm_info("REG_SEQ", $sformatf("Invalid write address 0x%08X correctly returned SLVERR", addr), UVM_MEDIUM)
        end
    endtask
    
    task test_unaligned_address(bit [31:0] addr);
        axi4_lite_transaction read_trans;
        
        `uvm_do_with(read_trans, {
            read_trans.addr == addr;
            read_trans.trans_type == AXI_READ;
            read_trans.resp == 2'b10;
        })
        
        if (read_trans.resp !== 2'b10) begin // SLVERR expected
            `uvm_error("REG_SEQ", $sformatf("Unaligned address 0x%08X should return SLVERR, got 0x%02X", 
                       addr, read_trans.resp))
        end else begin
            `uvm_info("REG_SEQ", $sformatf("Unaligned address 0x%08X correctly returned SLVERR", addr), UVM_MEDIUM)
        end
    endtask
endclass

// Comprehensive UART-driven register access sequence (Day 1 primary sequence)
class register_comprehensive_access_sequence extends register_uart_sequence_base;
    `uvm_object_utils(register_comprehensive_access_sequence)

    function new(string name = "register_comprehensive_access_sequence");
        super.new(name);
    endfunction

    virtual task body();
        `uvm_info(get_type_name(), "Starting comprehensive register access sequence", UVM_MEDIUM)

        sweep_register_map();
        exercise_reserved_regions();
        exercise_bitfield_patterns();
        exercise_timing_profiles();

        `uvm_info(get_type_name(), "Comprehensive register access sequence completed", UVM_MEDIUM)
    endtask

    // Sweep all defined registers with read/write activity
    task automatic sweep_register_map();
        int REG_COUNT = 8;
        bit [31:0] reg_addrs [8] = '{
            REG_CONTROL, REG_STATUS, REG_CONFIG, REG_DEBUG,
            REG_TX_COUNT, REG_RX_COUNT, REG_FIFO_STAT, REG_VERSION
        };
        bit reg_writable [8] = '{1, 0, 1, 1, 0, 0, 0, 0};
        bit [31:0] reg_write_values [8] = '{
            32'h0000_0001, // CONTROL: enable bridge
            32'h0000_0000,
            32'h0000_3301, // CONFIG: baud_div + timeout_cfg
            32'h0000_0003, // DEBUG: enter mode 3
            32'h0000_0000,
            32'h0000_0000,
            32'h0000_0000,
            32'h0000_0000
        };
        string reg_names [8] = '{
            "CONTROL", "STATUS", "CONFIG", "DEBUG",
            "TX_COUNT", "RX_COUNT", "FIFO_STAT", "VERSION"
        };

        for (int i = 0; i < REG_COUNT; i++) begin
            if (reg_writable[i]) begin
                drive_write(reg_addrs[i], reg_write_values[i], 4);
                #(200ns);
            end

            drive_read(reg_addrs[i], 4);
            `uvm_info(get_type_name(),
                $sformatf("Register sweep completed for %s (0x%08X)", reg_names[i], reg_addrs[i]),
                UVM_HIGH)
        end
    endtask

    // Exercise reserved and boundary addresses for error handling
    task automatic exercise_reserved_regions();
        int RESERVED_COUNT = 5;
        bit [31:0] reserved_addrs [5] = '{
            REG_BASE_ADDR + 32'h020,
            REG_BASE_ADDR + 32'h024,
            REG_BASE_ADDR + 32'h0FC,
            REG_BASE_ADDR + 32'h200,
            32'h0000_1FFC
        };

        for (int i = 0; i < RESERVED_COUNT; i++) begin
            drive_read(reserved_addrs[i], 4, /*expect_error=*/1);
            #(100ns);
            drive_write(reserved_addrs[i], 32'hDEAD_BEEF, 4, /*expect_error=*/1);
            #(150ns);
        end

        // Misaligned accesses
        for (int offset = 1; offset < 4; offset++) begin
            drive_read(REG_CONTROL + offset, 4, /*expect_error=*/1);
            #(80ns);
        end
    endtask

    // Toggle individual bitfields to improve toggle coverage
    task automatic exercise_bitfield_patterns();
        int CONFIG_SWEEPS = 4;
        int unsigned baud_values [4] = '{434, 217, 108, 54};
        int unsigned timeout_values [4] = '{500, 1000, 2000, 4000};

        // CONTROL register: drive explicit enable/disable transitions and reset pulses
        toggle_control_states();

        // CONFIG register: sweep baud and timeout fields
        for (int i = 0; i < CONFIG_SWEEPS; i++) begin
            bit [31:0] cfg_value;
            cfg_value[7:0] = baud_values[i][7:0];
            cfg_value[15:8] = timeout_values[i][7:0];
            cfg_value[31:16] = '0;
            drive_write(REG_CONFIG, cfg_value, 2);
            #(120ns);
            drive_read(REG_CONFIG, 2);
        end

        // DEBUG register nibble sweep
        for (int dbg = 0; dbg < 16; dbg++) begin
            drive_write(REG_DEBUG, dbg, 1);
            #(40ns);
        end
    endtask

    // Force CONTROL register through disable/enable states to trigger toggle coverage
    task automatic toggle_control_states();
        // Ensure bridge starts enabled, then drive to a disabled state
        drive_control_write_with_trace("initial_enable", 32'h0000_0001, 4, /*perform_readback=*/0, /*expected_enable_bit=*/1'b1);
        #(CONTROL_POST_CMD_DELAY_NS);
        drive_control_write_with_trace("disable_window_entry", 32'h0000_0000, 4, /*perform_readback=*/1, /*expected_enable_bit=*/1'b0, /*allow_busy=*/1'b1);
        hold_bridge_disabled("disable_window_entry_hold", CONTROL_DISABLE_WINDOW_NS);

        // While disabled, sample status and issue a reset pulse without enable asserted
        drive_read(REG_STATUS, 4, /*expect_error=*/0);
        #(100ns);
        drive_control_write_with_trace("stats_reset_pulse", 32'h0000_0002, 4, /*perform_readback=*/0, /*expected_enable_bit=*/1'b0);
        #(CONTROL_POST_CMD_DELAY_NS);

        // Re-enable, apply enable+reset, then add a second disable window for coverage margin
        drive_control_write_with_trace("re_enable_primary", 32'h0000_0001, 4, /*perform_readback=*/0, /*expected_enable_bit=*/1'b1);
        #(CONTROL_POST_CMD_DELAY_NS);
        drive_control_write_with_trace("enable_with_reset", 32'h0000_0003, 4, /*perform_readback=*/0, /*expected_enable_bit=*/1'b1);
        #(150ns);
        drive_control_write_with_trace("disable_window_reprobe", 32'h0000_0000, 4, /*perform_readback=*/1, /*expected_enable_bit=*/1'b0, /*allow_busy=*/1'b1);
        hold_bridge_disabled("disable_window_reprobe_hold", CONTROL_DISABLE_WINDOW_NS);
        drive_control_write_with_trace("disable_window_confirm_issue", 32'h0000_0000, 4, /*perform_readback=*/0, /*expected_enable_bit=*/1'b0, /*allow_busy=*/1'b1);
        hold_bridge_disabled("disable_window_confirm_hold", CONTROL_DISABLE_HOLD_NS);
        verify_control_readback("disable_window_confirm", 4, /*expected_enable_bit=*/1'b0, /*allow_busy=*/1'b1);
        drive_control_write_with_trace("final_enable", 32'h0000_0001, 4, /*perform_readback=*/0, /*expected_enable_bit=*/1'b1);
        wait_for_bridge_recovery("final_enable_settle", CONTROL_DISABLE_HOLD_NS);
        verify_control_readback("final_enable_confirm", 4, /*expected_enable_bit=*/1'b1, /*allow_busy=*/1'b0);
        #(CONTROL_POST_CMD_DELAY_NS);
    endtask

    task automatic hold_bridge_disabled(string label, time hold_duration_ns);
        time hold_start_ns;

        hold_start_ns = $time / 1ns;
        `uvm_info("CONTROL_TRACE",
            $sformatf("[%s] Holding bridge_enable low for %0t ns starting at %0t ns",
                      label, hold_duration_ns / 1ns, hold_start_ns),
            UVM_MEDIUM);
        #(hold_duration_ns);
    endtask

    task automatic wait_for_bridge_recovery(string label, time wait_duration_ns);
        time wait_start_ns;

        wait_start_ns = $time / 1ns;
        `uvm_info("CONTROL_TRACE",
            $sformatf("[%s] Waiting for bridge recovery for %0t ns starting at %0t ns",
                      label, wait_duration_ns / 1ns, wait_start_ns),
            UVM_MEDIUM);
        #(wait_duration_ns);
    endtask

    // Apply different timing gaps and burst patterns to stress FIFOs
    task automatic exercise_timing_profiles();
        // Back-to-back writes
        for (int i = 0; i < 8; i++) begin
            drive_write(REG_CONFIG, 32'h0000_1000 | i, 4);
        end

        // Randomized idle gaps with reads
        for (int j = 0; j < 6; j++) begin
            drive_read(REG_STATUS, 4);
            #(50ns + (j * 30ns));
        end

        // Auto-increment burst covering RX/TX counter addresses
        drive_burst(REG_TX_COUNT, 4, 4, /*auto_increment=*/1);
        #(250ns);
    endtask

    task automatic drive_write_core(string txn_label,
                                    bit [31:0] addr,
                                    bit [31:0] value,
                                    int unsigned byte_count,
                                    bit expect_error = 0,
                                    output uart_frame_transaction req);
        req = uart_frame_transaction::type_id::create(txn_label);
        start_item(req);

        req.is_write = 1;
        req.auto_increment = 0;
        req.size = infer_size(byte_count);
        req.length = 4'h0; // Single beat
        req.addr = addr;
        req.sof = SOF_HOST_TO_DEVICE;
        req.direction = UART_RX;
        req.error_inject = 0;
        req.expect_error = expect_error;
        assign_data(req, value, byte_count);
        req.build_cmd();
        req.calculate_crc();

        finish_item(req);
    endtask

    task automatic drive_read_core(string txn_label,
                                   bit [31:0] addr,
                                   int unsigned byte_count,
                                   bit expect_error,
                                   output uart_frame_transaction req);
        req = uart_frame_transaction::type_id::create(txn_label);
        start_item(req);

        req.is_write = 0;
        req.auto_increment = 0;
        req.size = infer_size(byte_count);
        req.length = 4'h0;
        req.addr = addr;
        req.sof = SOF_HOST_TO_DEVICE;
        req.direction = UART_RX;
        req.error_inject = 0;
        req.expect_error = expect_error;
        req.data = new[0];
        req.build_cmd();
        req.calculate_crc();

        finish_item(req);

        if (expect_error) begin
            `uvm_info(get_type_name(),
                $sformatf("Issued expected-error read from 0x%08X", addr), UVM_MEDIUM)
        end else begin
            `uvm_info(get_type_name(),
                $sformatf("Read request (%0d bytes) from 0x%08X", byte_count, addr),
                UVM_MEDIUM)
        end
    endtask

    task automatic drive_control_write_with_trace(string stage_label,
                                                   bit [31:0] value,
                                                   int unsigned byte_count,
                                                   bit perform_readback,
                                                   bit expected_enable_bit,
                                                   bit allow_busy = 1'b0);
        uart_frame_transaction ctrl_req;
        time issue_time_ns;

    drive_write_core({stage_label, "_control_write"}, REG_CONTROL, value, byte_count,
             /*expect_error=*/0, ctrl_req);
        issue_time_ns = $time / 1ns;

        `uvm_info("CONTROL_TRACE",
            $sformatf("[%s] CONTROL write value=0x%08X CMD=0x%02X (%0d bytes) at %0t ns",
                      stage_label, value, ctrl_req.cmd, byte_count, issue_time_ns),
            UVM_MEDIUM);

        if (perform_readback) begin
            #(CONTROL_READBACK_DELAY_NS);
            verify_control_readback(stage_label, byte_count, expected_enable_bit, allow_busy);
        end
    endtask

    task automatic verify_control_readback(string stage_label,
                                            int unsigned byte_count,
                                            bit expected_enable_bit,
                                            bit allow_busy);
        uart_frame_transaction rd_req;
        bit [31:0] observed_value;
        int limit_bytes;
        time read_time_ns;
        int unsigned resp_size;
        bit short_read;
        bit empty_read;
        int partial_retry_budget;

        partial_retry_budget = CONTROL_PARTIAL_RETRY_EXTENSION;

        for (int attempt = 0; attempt < CONTROL_READBACK_MAX_ATTEMPTS; attempt++) begin
            string attempt_label;

            attempt_label = $sformatf("%s_control_read_attempt%0d", stage_label, attempt);
            drive_read_core(attempt_label, REG_CONTROL, byte_count, /*expect_error=*/0, rd_req);
            read_time_ns = $time / 1ns;

            `uvm_info("CONTROL_TRACE",
                $sformatf("[%s] CONTROL read attempt %0d issued CMD=0x%02X at %0t ns",
                          stage_label, attempt, rd_req.cmd, read_time_ns),
                UVM_MEDIUM);

            if (!rd_req.response_received) begin
                `uvm_error("CONTROL_TRACE",
                    $sformatf("[%s] CONTROL read attempt %0d did not receive a response",
                              stage_label, attempt));
                return;
            end

            if (rd_req.response_status == STATUS_BUSY) begin
                `uvm_info("CONTROL_TRACE",
                    $sformatf("[%s] CONTROL read reported STATUS_BUSY (0x%02X) on attempt %0d",
                              stage_label, rd_req.response_status, attempt),
                    UVM_MEDIUM);

                if (allow_busy) begin
                    return;
                end

                if (attempt == CONTROL_READBACK_MAX_ATTEMPTS - 1) begin
                    `uvm_error("CONTROL_TRACE",
                        $sformatf("[%s] CONTROL remained busy after %0d attempts",
                                  stage_label, CONTROL_READBACK_MAX_ATTEMPTS));
                    return;
                end

                hold_bridge_disabled({stage_label, "_busy_retry_hold"}, CONTROL_READBACK_RETRY_DELAY_NS);
                continue;
            end

            if (rd_req.response_status != STATUS_OK) begin
                `uvm_error("CONTROL_TRACE",
                    $sformatf("[%s] CONTROL read returned status 0x%02X on attempt %0d",
                              stage_label, rd_req.response_status, attempt));
                return;
            end

            resp_size = rd_req.response_data.size();
            short_read = (resp_size < byte_count);
            empty_read = (resp_size == 0);

            if (short_read) begin
                `uvm_warning("CONTROL_TRACE",
                    $sformatf("[%s] CONTROL read returned %0d byte(s); expected %0d",
                              stage_label, resp_size, byte_count));

                if (allow_busy) begin
                    `uvm_info("CONTROL_TRACE",
                        $sformatf("[%s] Allowing short CONTROL read because allow_busy=1", stage_label),
                        UVM_MEDIUM);
                    return;
                end

                if (empty_read) begin
                    if (attempt == CONTROL_READBACK_MAX_ATTEMPTS - 1) begin
                        `uvm_error("CONTROL_TRACE",
                            $sformatf("[%s] CONTROL read never produced data after %0d attempts",
                                      stage_label, CONTROL_READBACK_MAX_ATTEMPTS));
                        return;
                    end

                    wait_for_bridge_recovery({stage_label, "_short_read_retry"}, CONTROL_READBACK_RETRY_DELAY_NS);
                    continue;
                end
            end

            observed_value = '0;
            limit_bytes = (resp_size < byte_count) ? resp_size : byte_count;
            for (int i = 0; i < limit_bytes; i++) begin
                observed_value[8*i +: 8] = rd_req.response_data[i];
            end

            `uvm_info("CONTROL_TRACE",
                $sformatf("[%s] CONTROL read observed_value=0x%08X", stage_label, observed_value),
                UVM_MEDIUM);

            if (short_read && !allow_busy && !empty_read) begin
                if (observed_value[0] === expected_enable_bit) begin
                    `uvm_warning("CONTROL_TRACE",
                        $sformatf("[%s] CONTROL read confirmed enable bit with truncated payload (%0d byte(s))",
                                  stage_label, resp_size));
                    `uvm_info("CONTROL_TRACE",
                        $sformatf("[%s] CONTROL bridge_enable confirmed as %0b", stage_label, observed_value[0]),
                        UVM_MEDIUM);
                    return;
                end

                if (attempt < CONTROL_READBACK_MAX_ATTEMPTS - 1) begin
                    `uvm_info("CONTROL_TRACE",
                        $sformatf("[%s] CONTROL read truncated payload (%0d byte(s)) — retrying after %0t ns",
                                  stage_label, resp_size, CONTROL_READBACK_RETRY_DELAY_NS / 1ns),
                        UVM_MEDIUM);
                    wait_for_bridge_recovery({stage_label, "_short_read_retry"}, CONTROL_READBACK_RETRY_DELAY_NS);
                    continue;
                end

                if (partial_retry_budget > 0) begin
                    partial_retry_budget--;
                    `uvm_warning("CONTROL_TRACE",
                        $sformatf("[%s] CONTROL read truncated payload with mismatched enable bit — extending backoff (%0d byte(s))",
                                  stage_label, resp_size));
                    `uvm_info("CONTROL_TRACE",
                        $sformatf("[%s] Applying extended CONTROL quiet time of %0t ns before retry (remaining partial retries: %0d)",
                                  stage_label, CONTROL_PARTIAL_BACKOFF_NS / 1ns, partial_retry_budget),
                        UVM_MEDIUM);
                    wait_for_bridge_recovery({stage_label, "_partial_retry_backoff"}, CONTROL_PARTIAL_BACKOFF_NS);
                    attempt--;
                    continue;
                end

                `uvm_warning("CONTROL_TRACE",
                    $sformatf("[%s] CONTROL bridge_enable could not be confirmed due to persistent truncated payload (observed=%0b expected=%0b)",
                              stage_label, observed_value[0], expected_enable_bit));
                `uvm_info("CONTROL_TRACE",
                    $sformatf("[%s] Deferring CONTROL enable verification to bridge_status_monitor after exhausting retries", stage_label),
                    UVM_LOW);
                return;
            end

            if (!short_read && observed_value[31:1] !== '0) begin
                `uvm_error("CONTROL_TRACE",
                    $sformatf("[%s] CONTROL read observed reserved bits set: 0x%08X", stage_label, observed_value));
                return;
            end

            if (observed_value[0] !== expected_enable_bit) begin
                if (attempt == CONTROL_READBACK_MAX_ATTEMPTS - 1) begin
                    `uvm_error("CONTROL_TRACE",
                        $sformatf("[%s] CONTROL bridge_enable mismatch: observed=%0b expected=%0b", stage_label,
                                  observed_value[0], expected_enable_bit));
                    return;
                end

                `uvm_info("CONTROL_TRACE",
                    $sformatf("[%s] CONTROL bridge_enable observed=%0b expected=%0b — retrying",
                              stage_label, observed_value[0], expected_enable_bit),
                    UVM_MEDIUM);
                wait_for_bridge_recovery({stage_label, "_enable_retry"}, CONTROL_READBACK_RETRY_DELAY_NS);
                continue;
            end

            `uvm_info("CONTROL_TRACE",
                $sformatf("[%s] CONTROL bridge_enable confirmed as %0b", stage_label, observed_value[0]),
                UVM_MEDIUM);

            return;
        end
    endtask

    // Issue a single-beat write of byte_count bytes
    task automatic drive_write(bit [31:0] addr, bit [31:0] value, int unsigned byte_count,
                               bit expect_error = 0);
        uart_frame_transaction req;
        drive_write_core("reg_write", addr, value, byte_count, expect_error, req);

        if (expect_error) begin
            `uvm_info(get_type_name(),
                $sformatf("Issued expected-error write to 0x%08X", addr), UVM_MEDIUM)
        end else begin
            `uvm_info(get_type_name(),
                $sformatf("Write 0x%08X (%0d bytes) to 0x%08X (CMD=0x%02X)",
                          value, byte_count, addr, req.cmd),
                UVM_MEDIUM)
        end
    endtask

    // Issue a single-beat read of byte_count bytes
    task automatic drive_read(bit [31:0] addr, int unsigned byte_count,
                              bit expect_error = 0);
        uart_frame_transaction req;
        drive_read_core("reg_read", addr, byte_count, expect_error, req);
    endtask

    // Drive burst transaction with optional auto-increment
    task automatic drive_burst(bit [31:0] base_addr, int unsigned byte_count,
                               int unsigned beats, bit auto_increment);
        uart_frame_transaction req;
        int unsigned total_bytes = byte_count * beats;

        req = uart_frame_transaction::type_id::create("reg_burst");
        start_item(req);

        req.is_write = 1;
        req.auto_increment = auto_increment;
        req.size = infer_size(byte_count);
        req.length = beats - 1;
        req.addr = base_addr;
        req.sof = SOF_HOST_TO_DEVICE;
        req.direction = UART_RX;
        req.error_inject = 0;
        req.expect_error = 0;
        req.data = new[total_bytes];
        for (int i = 0; i < total_bytes; i++) begin
            req.data[i] = $urandom_range(0, 255);
        end
        req.build_cmd();
        req.calculate_crc();

        finish_item(req);

        `uvm_info(get_type_name(),
            $sformatf("Burst write: %0d beats (%0d bytes) starting at 0x%08X (auto_inc=%0d)",
                      beats, total_bytes, base_addr, auto_increment),
            UVM_MEDIUM)
    endtask

    // Assign byte array for write transactions
    task automatic assign_data(ref uart_frame_transaction req,
                               bit [31:0] value,
                               int unsigned byte_count);
        req.data = new[byte_count];
        for (int i = 0; i < byte_count; i++) begin
            req.data[i] = value[8*i +: 8];
        end
    endtask

    // Map byte count to size encoding (00=1B, 01=2B, 10=4B)
    function automatic logic [1:0] infer_size(int unsigned byte_count);
        case (byte_count)
            1: return 2'b00;
            2: return 2'b01;
            default: return 2'b10;
        endcase
    endfunction
endclass

// Alignment-focused UART register sequence targeting alignment and WSTRB coverage gaps
class register_alignment_sequence extends register_uart_sequence_base;
    `uvm_object_utils(register_alignment_sequence)

    function new(string name = "register_alignment_sequence");
        super.new(name);
    endfunction

    virtual task body();
        `uvm_info(get_type_name(), "Starting register alignment coverage sequence", UVM_MEDIUM)

        drive_byte_lane_coverage();
        drive_halfword_lane_coverage();
        drive_misaligned_error_campaign();
        drive_burst_matrix();

        `uvm_info(get_type_name(), "Register alignment coverage sequence completed", UVM_MEDIUM)
    endtask

    task automatic drive_byte_lane_coverage();
        bit [31:0] base_addr;

        base_addr = REG_DEBUG;
        // Lane 0 receives aligned single-byte traffic from the comprehensive access sequence.
        // Focus on upper lanes to exercise partial WSTRB error paths without perturbing
        // the scoreboard's aligned data predictions.
        for (int lane = 1; lane < 4; lane++) begin
            bit [31:0] value;

            value = 32'h0;
            value[7:0] = 8'hA0 + lane;
            drive_write(base_addr + lane, value, 1, /*expect_error=*/1);
            #(60ns);
        end
    endtask

    task automatic drive_halfword_lane_coverage();
        drive_write(REG_CONFIG, 32'h0000_55AA, 2, /*expect_error=*/0);
        #(80ns);
        drive_write(REG_CONFIG + 32'h2, 32'h0000_AA55, 2, /*expect_error=*/0);
        #(80ns);
    endtask

    task automatic drive_misaligned_error_campaign();
        drive_write(REG_CONFIG + 32'h1, 32'h0000_00F1, 2, /*expect_error=*/1);
        #(70ns);
        drive_write(REG_CONFIG + 32'h3, 32'h0000_0F0F, 2, /*expect_error=*/1);
        #(70ns);
        drive_write(REG_CONTROL + 32'h1, 32'hDEAD_BEEF, 4, /*expect_error=*/1);
        #(90ns);
    endtask

    task automatic drive_burst_matrix();
    drive_alignment_burst("burst_inc_8bit", REG_DEBUG, 1, 4, /*auto_increment=*/1'b1, /*expect_error=*/1);
        drive_alignment_burst("burst_fixed_16bit", REG_CONFIG, 2, 2, /*auto_increment=*/1'b0, /*expect_error=*/0);
        drive_alignment_burst("burst_inc_16bit_misaligned", REG_CONFIG + 32'h1, 2, 3, /*auto_increment=*/1'b1, /*expect_error=*/1);
        drive_alignment_burst("burst_inc_32bit_misaligned", REG_CONTROL + 32'h1, 4, 2, /*auto_increment=*/1'b1, /*expect_error=*/1);
    endtask

    task automatic drive_alignment_burst(string label,
                                         bit [31:0] base_addr,
                                         int unsigned byte_count,
                                         int unsigned beats,
                                         bit auto_increment,
                                         bit expect_error);
        uart_frame_transaction req;
        int unsigned total_bytes;

        if (beats == 0) begin
            beats = 1;
        end

        total_bytes = byte_count * beats;
        req = uart_frame_transaction::type_id::create({label, "_txn"});
        start_item(req);

        req.is_write = 1;
        req.auto_increment = auto_increment;
        req.size = infer_size(byte_count);
        req.length = beats - 1;
        req.addr = base_addr;
        req.sof = SOF_HOST_TO_DEVICE;
        req.direction = UART_RX;
        req.error_inject = 0;
        req.expect_error = expect_error;
        req.data = new[total_bytes];
        for (int i = 0; i < total_bytes; i++) begin
            req.data[i] = (8'h40 + i[7:0]);
        end
        req.build_cmd();
        req.calculate_crc();

        finish_item(req);

        `uvm_info(get_type_name(),
            $sformatf("[%s] Burst write base=0x%08X size=%0d beats=%0d auto_inc=%0d expect_error=%0d",
                      label, base_addr, byte_count, beats, auto_increment, expect_error),
            UVM_MEDIUM)

        #(110ns);
    endtask
endclass

// Disable window campaign sequence introducing randomized idle and error scenarios
class register_disable_window_campaign_sequence extends register_uart_sequence_base;
    `uvm_object_utils(register_disable_window_campaign_sequence)

    function new(string name = "register_disable_window_campaign_sequence");
        super.new(name);
    endfunction

    virtual task body();
        int unsigned iteration_count;

        `uvm_info(get_type_name(), "Starting disable window campaign sequence", UVM_MEDIUM)

        // Ensure bridge begins enabled and confirmed
        drive_control_write_with_trace("campaign_preroll_enable", 32'h0000_0001, 4,
                                       /*perform_readback=*/1, /*expected_enable_bit=*/1'b1,
                                       /*allow_busy=*/1'b0);
        wait_for_bridge_recovery("campaign_preroll_settle", CONTROL_DISABLE_HOLD_NS);

        if (!std::randomize(iteration_count) with { iteration_count inside {[3:6]}; }) begin
            iteration_count = 3;
        end

        for (int iter = 0; iter < iteration_count; iter++) begin
            execute_disable_iteration(iter);
        end

        // Restore enabled state before exiting
        drive_control_write_with_trace("campaign_final_enable", 32'h0000_0001, 4,
                                       /*perform_readback=*/1, /*expected_enable_bit=*/1'b1,
                                       /*allow_busy=*/1'b0);
        wait_for_bridge_recovery("campaign_final_settle", CONTROL_DISABLE_HOLD_NS);

        `uvm_info(get_type_name(), "Disable window campaign sequence completed", UVM_MEDIUM)
    endtask

    protected task automatic execute_disable_iteration(int iter_index);
        int unsigned pre_ops;
        int unsigned mid_ops;
        int unsigned post_ops;
        int unsigned disable_hold_ns;
        int unsigned recovery_ns;
    bit include_reset_pulse;
    bit issue_busy_probe;
    bit include_crc_fault;
    bit extend_quiet_period;
    bit [31:0] enable_value;
        string iter_label;

        if (!std::randomize(pre_ops, mid_ops, post_ops, disable_hold_ns, recovery_ns,
                             include_reset_pulse, issue_busy_probe, include_crc_fault,
                             extend_quiet_period) with {
                pre_ops inside {[2:5]};
                mid_ops inside {[1:4]};
                post_ops inside {[3:6]};
                disable_hold_ns inside {[400:1600]};
                recovery_ns inside {[300:1400]};
            }) begin
            pre_ops = 3;
            mid_ops = 2;
            post_ops = 4;
            disable_hold_ns = 800;
            recovery_ns = 900;
            include_reset_pulse = 0;
            issue_busy_probe = 1;
            include_crc_fault = 0;
            extend_quiet_period = 0;
        end

        iter_label = $sformatf("disable_campaign_iter%0d", iter_index);

        apply_pre_disable_traffic(iter_label, pre_ops);

        drive_control_write_with_trace({iter_label, "_disable_entry"}, 32'h0000_0000, 4,
                                       /*perform_readback=*/1, /*expected_enable_bit=*/1'b0,
                                       /*allow_busy=*/1'b1);
        hold_bridge_disabled({iter_label, "_disable_hold"}, time'(disable_hold_ns) * 1ns);

        if (issue_busy_probe) begin
            verify_control_readback({iter_label, "_busy_probe"}, 4,
                                    /*expected_enable_bit=*/1'b0, /*allow_busy=*/1'b1);
        end

        issue_disabled_access(iter_label, mid_ops);

        if (extend_quiet_period) begin
            wait_for_bridge_recovery({iter_label, "_extended_quiet"}, CONTROL_PARTIAL_BACKOFF_NS);
        end

        enable_value = include_reset_pulse ? 32'h0000_0003 : 32'h0000_0001;
        drive_control_write_with_trace({iter_label, "_enable_issue"}, enable_value, 4,
                                       /*perform_readback=*/0, /*expected_enable_bit=*/1'b1,
                                       /*allow_busy=*/1'b0);
        wait_for_bridge_recovery({iter_label, "_enable_recover"}, time'(recovery_ns) * 1ns);
        verify_control_readback({iter_label, "_enable_confirm"}, 4,
                                /*expected_enable_bit=*/1'b1, /*allow_busy=*/1'b0);

        apply_post_disable_traffic(iter_label, post_ops);

        if (include_crc_fault) begin
            inject_crc_fault_frame({iter_label, "_crc_fault"});
        end
    endtask

    protected task automatic apply_pre_disable_traffic(string base_label, int unsigned count);
        for (int idx = 0; idx < count; idx++) begin
            issue_pre_disable_access($sformatf("%s_pre_op%0d", base_label, idx));
            #(CONTROL_POST_CMD_DELAY_NS + time'($urandom_range(40, 140)) * 1ns);
        end
    endtask

    protected task automatic issue_pre_disable_access(string label);
        bit do_write;
        bit target_debug;

        if (!std::randomize(do_write, target_debug)) begin
            do_write = 1'b0;
            target_debug = 1'b0;
        end

        if (do_write) begin
            bit [31:0] payload;
            void'(std::randomize(payload));
            if (target_debug) begin
                drive_write(REG_DEBUG, payload, 1);
            end else begin
                drive_write(REG_CONFIG, payload, 4);
            end
        end else begin
            case ($urandom_range(0, 3))
                0: drive_read(REG_STATUS, 4);
                1: drive_read(REG_VERSION, 4);
                2: drive_read(REG_FIFO_STAT, 4);
                default: drive_read(REG_CONFIG, 2);
            endcase
        end

        `uvm_info(get_type_name(), $sformatf("[%s] Completed pre-disable access", label), UVM_HIGH)
    endtask

    protected task automatic issue_disabled_access(string base_label, int unsigned count);
        string op_label;
        for (int idx = 0; idx < count; idx++) begin
            op_label = $sformatf("%s_disabled_op%0d", base_label, idx);

            case ($urandom_range(0, 4))
                0: drive_read(REG_STATUS, 4, /*expect_error=*/1);
                1: drive_read((idx % 2) ? REG_TX_COUNT : REG_RX_COUNT, 4, /*expect_error=*/1);
                2: drive_read(REG_FIFO_STAT, 4, /*expect_error=*/1);
                3: drive_write(REG_DEBUG, $urandom_range(0, 15), 1, /*expect_error=*/1);
                default: drive_read(REG_CONTROL, 4, /*expect_error=*/1);
            endcase

            `uvm_info(get_type_name(), $sformatf("[%s] Disabled window stimulus issued", op_label), UVM_HIGH)
            #(CONTROL_POST_CMD_DELAY_NS + time'($urandom_range(60, 160)) * 1ns);
        end
    endtask

    protected task automatic apply_post_disable_traffic(string base_label, int unsigned count);
        string op_label;
        for (int idx = 0; idx < count; idx++) begin
            op_label = $sformatf("%s_post_op%0d", base_label, idx);

            case ($urandom_range(0, 3))
                0: drive_burst(REG_CONFIG, 4, 2, /*auto_increment=*/1);
                1: drive_write(REG_CONFIG, $urandom(), 4);
                default: drive_read(REG_STATUS, 4);
            endcase

            `uvm_info(get_type_name(), $sformatf("[%s] Post-disable activity executed", op_label), UVM_HIGH)
            #(CONTROL_POST_CMD_DELAY_NS + time'($urandom_range(80, 200)) * 1ns);
        end
    endtask

    protected task automatic inject_crc_fault_frame(string label);
        uart_frame_transaction fault_req;

        fault_req = uart_frame_transaction::type_id::create(label);
        start_item(fault_req);

        fault_req.is_write = 1;
        fault_req.auto_increment = 0;
        fault_req.size = 2'b10;
        fault_req.length = 4'h0;
        fault_req.addr = REG_CONFIG;
        fault_req.sof = SOF_HOST_TO_DEVICE;
        fault_req.direction = UART_RX;
        fault_req.error_inject = 1;
        fault_req.force_crc_error = 1;
        fault_req.data = new[4];
        for (int i = 0; i < 4; i++) begin
            fault_req.data[i] = $urandom_range(0, 255);
        end
        fault_req.build_cmd();
        fault_req.calculate_crc();
        fault_req.crc ^= 8'hFF; // Intentionally corrupt CRC to trigger DUT error handling

        finish_item(fault_req);

        `uvm_warning("CONTROL_TRACE",
            $sformatf("[%s] Injected CONTROL CRC fault frame (addr=0x%08X)", label, fault_req.addr))
    endtask
endclass

// Sequence focusing on read/write pattern combinations (Day 1 afternoon)
class register_rw_pattern_sequence extends register_uart_sequence_base;
    `uvm_object_utils(register_rw_pattern_sequence)

    function new(string name = "register_rw_pattern_sequence");
        super.new(name);
    endfunction

    virtual task body();
        `uvm_info(get_type_name(), "Starting register read/write pattern sequence", UVM_MEDIUM)

        exercise_data_widths();
        exercise_auto_increment_patterns();
        exercise_misaligned_scenarios();
        exercise_back_to_back_transactions();

        `uvm_info(get_type_name(), "Register read/write pattern sequence completed", UVM_MEDIUM)
    endtask

    // Cover byte, halfword, and word accesses with validation reads
    task automatic exercise_data_widths();
        int WIDTH_VARIANTS = 3;
        int unsigned byte_counts [3] = '{1, 2, 4};
        bit [31:0] target_regs [3] = '{REG_CONTROL, REG_CONFIG, REG_DEBUG};

        for (int i = 0; i < 3; i++) begin
            for (int j = 0; j < WIDTH_VARIANTS; j++) begin
                bit [31:0] pattern = {24'h0, (i * 8'h11) ^ byte_counts[j][7:0]};
                drive_write(target_regs[i], pattern, byte_counts[j]);
                #(60ns);
                drive_read(target_regs[i], byte_counts[j]);
            end
        end
    endtask

    // Auto-increment sequences across register space
    task automatic exercise_auto_increment_patterns();
        // 32-bit auto-increment burst covering CONTROL -> DEBUG
        drive_burst(REG_CONTROL, 4, 4, /*auto_increment=*/1);
        #(120ns);

        // 16-bit alternating pattern across TX/RX counters
        drive_burst(REG_TX_COUNT, 2, 4, /*auto_increment=*/1);
        #(160ns);
    endtask

    // Misaligned and boundary conditions to validate error responses
    task automatic exercise_misaligned_scenarios();
        for (int offset = 1; offset < 4; offset++) begin
            drive_write(REG_CONFIG + offset, 32'hFFFF_FFFF, 4, /*expect_error=*/1);
            #(90ns);
            drive_read(REG_CONFIG + offset, 4, /*expect_error=*/1);
        end

        // Boundary at end of defined register space
        drive_write(REG_BASE_ADDR + 32'h020, 32'hCAFE_F00D, 4, /*expect_error=*/1);
        #(90ns);
    endtask

    // Stress back-to-back transactions with minimal idle time
    task automatic exercise_back_to_back_transactions();
        for (int iter = 0; iter < 6; iter++) begin
            bit [31:0] addr = REG_CONTROL;
            bit [31:0] data = 32'h0000_0001 ^ iter;
            drive_write(addr, data, 1);
        end

        for (int iter = 0; iter < 6; iter++) begin
            drive_read(REG_STATUS, 4);
        end
    endtask

endclass