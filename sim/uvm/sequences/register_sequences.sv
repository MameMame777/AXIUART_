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
class register_comprehensive_access_sequence extends uvm_sequence #(uart_frame_transaction);
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

        // CONTROL register: enable and status reset pulse
        drive_write(REG_CONTROL, 32'h0000_0001, 1);
        #(100ns);
        drive_write(REG_CONTROL, 32'h0000_0003, 1);
        #(100ns);

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

    // Issue a single-beat write of byte_count bytes
    task automatic drive_write(bit [31:0] addr, bit [31:0] value, int unsigned byte_count,
                               bit expect_error = 0);
        uart_frame_transaction req;
        req = uart_frame_transaction::type_id::create("reg_write");
        start_item(req);

        req.is_write = 1;
        req.auto_increment = 0;
        req.size = infer_size(byte_count);
        req.length = 4'h0; // Single beat
        req.addr = addr;
        req.sof = SOF_HOST_TO_DEVICE;
        req.direction = UART_RX;
        req.error_inject = 0;
        assign_data(req, value, byte_count);
        req.build_cmd();
        req.calculate_crc();

        finish_item(req);

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
        req = uart_frame_transaction::type_id::create("reg_read");
        start_item(req);

        req.is_write = 0;
        req.auto_increment = 0;
        req.size = infer_size(byte_count);
        req.length = 4'h0;
        req.addr = addr;
        req.sof = SOF_HOST_TO_DEVICE;
        req.direction = UART_RX;
        req.error_inject = 0;
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

// Sequence focusing on read/write pattern combinations (Day 1 afternoon)
class register_rw_pattern_sequence extends uvm_sequence #(uart_frame_transaction);
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

    // Helper: single-beat write with optional error expectation
    task automatic drive_write(bit [31:0] addr, bit [31:0] value, int unsigned byte_count,
                               bit expect_error = 0);
        uart_frame_transaction req;
        req = uart_frame_transaction::type_id::create("pattern_write");
        start_item(req);

        req.is_write = 1;
        req.auto_increment = 0;
        req.size = infer_size(byte_count);
        req.length = 4'h0;
        req.addr = addr;
        req.sof = SOF_HOST_TO_DEVICE;
        req.direction = UART_RX;
        req.error_inject = 0;
        assign_data(req, value, byte_count);
        req.build_cmd();
        req.calculate_crc();

        finish_item(req);

        `uvm_info(get_type_name(),
            $sformatf("Pattern write (%0d bytes) addr=0x%08X data=0x%08X expect_error=%0d (CMD=0x%02X)",
                      byte_count, addr, value, expect_error, req.cmd),
            UVM_HIGH)
    endtask

    // Helper: single-beat read with optional error expectation
    task automatic drive_read(bit [31:0] addr, int unsigned byte_count,
                              bit expect_error = 0);
        uart_frame_transaction req;
        req = uart_frame_transaction::type_id::create("pattern_read");
        start_item(req);

        req.is_write = 0;
        req.auto_increment = 0;
        req.size = infer_size(byte_count);
        req.length = 4'h0;
        req.addr = addr;
        req.sof = SOF_HOST_TO_DEVICE;
        req.direction = UART_RX;
        req.error_inject = 0;
        req.data = new[0];
        req.build_cmd();
        req.calculate_crc();

        finish_item(req);

        `uvm_info(get_type_name(),
            $sformatf("Pattern read (%0d bytes) addr=0x%08X expect_error=%0d",
                      byte_count, addr, expect_error),
            UVM_HIGH)
    endtask

    task automatic drive_burst(bit [31:0] base_addr, int unsigned byte_count,
                               int unsigned beats, bit auto_increment);
        uart_frame_transaction req;
        int unsigned total_bytes = byte_count * beats;

        req = uart_frame_transaction::type_id::create("pattern_burst");
        start_item(req);

        req.is_write = 1;
        req.auto_increment = auto_increment;
        req.size = infer_size(byte_count);
        req.length = beats - 1;
        req.addr = base_addr;
        req.sof = SOF_HOST_TO_DEVICE;
        req.direction = UART_RX;
        req.error_inject = 0;
        req.data = new[total_bytes];
        for (int i = 0; i < total_bytes; i++) begin
            req.data[i] = $urandom_range(0, 255);
        end
        req.build_cmd();
        req.calculate_crc();

        finish_item(req);

        `uvm_info(get_type_name(),
            $sformatf("Pattern burst (%0d beats) base=0x%08X auto_inc=%0d", beats, base_addr, auto_increment),
            UVM_MEDIUM)
    endtask

    task automatic assign_data(ref uart_frame_transaction req,
                               bit [31:0] value,
                               int unsigned byte_count);
        req.data = new[byte_count];
        for (int i = 0; i < byte_count; i++) begin
            req.data[i] = value[8*i +: 8];
        end
    endtask

    function automatic logic [1:0] infer_size(int unsigned byte_count);
        case (byte_count)
            1: return 2'b00;
            2: return 2'b01;
            default: return 2'b10;
        endcase
    endfunction
endclass