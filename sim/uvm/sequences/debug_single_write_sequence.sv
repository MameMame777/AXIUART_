`timescale 1ns / 1ps

// Simple Write-Only debug test sequence
class simple_debug_write_sequence_20250923 extends uvm_sequence #(uart_frame_transaction);
    
    `uvm_object_utils(simple_debug_write_sequence_20250923)
    
    function new(string name = "simple_debug_write_sequence_20250923");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction req_local;

        uvm_sequencer_base seq_handle;
    bit verbose_mode;
    string verbose_arg_matches[$];
    verbose_mode = (uvm_cmdline_processor::get_inst().get_arg_matches("+UART_BASIC_VERBOSE", verbose_arg_matches) > 0);

        if (verbose_mode) begin
            `uvm_info("DEBUG_SEQ", "Sequence body() started", UVM_LOW)
        end

        seq_handle = get_sequencer();
        if (seq_handle == null) begin
            `uvm_fatal("DEBUG_SEQ", "get_sequencer() returned NULL during body()")
        end

        // Create transaction explicitly so we can instrument the handshake path
        req_local = uart_frame_transaction::type_id::create("req_local");
        if (req_local == null) begin
            `uvm_fatal("DEBUG_SEQ", "Failed to allocate uart_frame_transaction")
        end
        req_local.set_item_context(this, seq_handle);
        if (verbose_mode) begin
            `uvm_info("DEBUG_SEQ", $sformatf("Transaction object allocated at time=%0t", $time), UVM_LOW)
        end

        if (verbose_mode) begin
            `uvm_info("DEBUG_SEQ_HANDSHAKE",
                $sformatf("Sequencer state dump for %s at time=%0t", seq_handle.get_full_name(), $time),
                UVM_LOW)
            seq_handle.print();
        end

        // Engage sequencer-driver handshake explicitly for visibility
        if (verbose_mode) begin
            `uvm_info("DEBUG_SEQ_HANDSHAKE",
                $sformatf("start_item() begin for %s at time=%0t", seq_handle.get_full_name(), $time),
                UVM_LOW)
        end
        start_item(req_local);
        if (verbose_mode) begin
            `uvm_info("DEBUG_SEQ_HANDSHAKE",
                $sformatf("start_item() returned for %s at time=%0t", seq_handle.get_full_name(), $time),
                UVM_LOW)
        end

        // Set transaction fields directly (avoids DSIM constraint solver limitations)
        req_local.is_write       = 1'b1;
        req_local.auto_increment = 1'b0;
        req_local.size           = 2'b00;
        req_local.length         = 4'h0;
        req_local.expect_error   = 1'b0;
        req_local.addr           = 32'h0000_1000;

        // Allocate and initialize data array
        req_local.data = new[1];
        req_local.data[0] = 8'h42;

        if (req_local.data.size() != 1) begin
            `uvm_fatal("DEBUG_SEQ_DATA",
                $sformatf("Unexpected data payload size=%0d for debug write sequence", req_local.data.size()))
        end

        // Rebuild protocol fields to match the configured payload
        req_local.build_cmd();
        req_local.calculate_crc();

        if (verbose_mode) begin
            `uvm_info("DEBUG_SEQ_HANDSHAKE",
                $sformatf("finish_item() begin for %s at time=%0t", seq_handle.get_full_name(), $time),
                UVM_LOW)
        end
        finish_item(req_local);
        if (verbose_mode) begin
            `uvm_info("DEBUG_SEQ_HANDSHAKE",
                $sformatf("finish_item() returned for %s at time=%0t", seq_handle.get_full_name(), $time),
                UVM_LOW)
        end

        if (!req_local.expect_error && (!req_local.response_received || req_local.response_status == STATUS_TIMEOUT)) begin
            `uvm_fatal("DEBUG_SEQ_TIMEOUT",
                $sformatf("DUT response missing or timed out: status=0x%02X timeout_flag=%0b",
                          req_local.response_status, req_local.timeout_error))
        end
    endtask
    
endclass