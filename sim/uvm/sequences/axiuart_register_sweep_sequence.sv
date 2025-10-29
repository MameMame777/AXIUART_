`timescale 1ns / 1ps

// Register sweep sequence for toggle coverage improvement
// Systematically access all register space to achieve >90% toggle coverage

// This file should be included within uart_axi4_test_pkg.sv, not imported directly

class axiuart_register_sweep_sequence extends uvm_sequence#(uart_frame_transaction);
    `uvm_object_utils(axiuart_register_sweep_sequence)
    
    // Register addresses from register_map.md
    localparam bit [31:0] REG_BASE_ADDR = 32'h0000_1000;
    localparam bit [31:0] REG_CONTROL   = REG_BASE_ADDR + 32'h000;
    localparam bit [31:0] REG_STATUS    = REG_BASE_ADDR + 32'h004;
    localparam bit [31:0] REG_CONFIG    = REG_BASE_ADDR + 32'h008;
    localparam bit [31:0] REG_DEBUG     = REG_BASE_ADDR + 32'h00C;
    localparam bit [31:0] REG_TX_COUNT  = REG_BASE_ADDR + 32'h010;
    localparam bit [31:0] REG_RX_COUNT  = REG_BASE_ADDR + 32'h014;
    localparam bit [31:0] REG_FIFO_STAT = REG_BASE_ADDR + 32'h018;
    localparam bit [31:0] REG_VERSION   = REG_BASE_ADDR + 32'h01C;
    localparam bit [7:0]  MAX_BAUD_DIV = UART_OVERSAMPLE[7:0];
    localparam bit [7:0]  DEFAULT_TIMEOUT_CFG = 8'h5A;
    
    function new(string name = "axiuart_register_sweep_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_frame_transaction req;
        
        `uvm_info(get_type_name(), "Starting UART-based register sweep sequence for toggle coverage", UVM_MEDIUM)
        
        // Phase 1: Read all registers to initialize toggle states
        perform_uart_register_read_sweep();
        
        // Phase 2: Write all writable registers with test patterns  
        perform_register_write_patterns();
        
        // Phase 3: Exercise special register behaviors
        perform_special_register_tests();
        
        // Phase 4: Boundary and error condition tests
        perform_address_boundary_tests();
        
        `uvm_info(get_type_name(), "UART register sweep sequence completed", UVM_MEDIUM)
    endtask
    
    // Read all mapped registers sequentially via UART
    virtual task perform_uart_register_read_sweep();
        bit [31:0] register_list[$] = {
            REG_CONTROL, REG_STATUS, REG_CONFIG, REG_DEBUG,
            REG_TX_COUNT, REG_RX_COUNT, REG_FIFO_STAT, REG_VERSION
        };
        
        `uvm_info(get_type_name(), "Phase 1: Reading all mapped registers via UART", UVM_MEDIUM)
        
        foreach (register_list[i]) begin
            uart_frame_transaction req;
            req = uart_frame_transaction::type_id::create("req");
            start_item(req);
            
            // UART Read Command: SOF + CMD(0x80) + ADDR_H + ADDR_L + LEN(0x04) + CRC
            req.frame_data = new[6];
            req.frame_data[0] = 8'h5A;  // SOF
            req.frame_data[1] = 8'h80;  // READ_CMD
            req.frame_data[2] = register_list[i][15:8];   // ADDR_H
            req.frame_data[3] = register_list[i][7:0];    // ADDR_L
            req.frame_data[4] = 8'h04;  // LENGTH (4 bytes)
            req.frame_data[5] = calculate_simple_crc(req.frame_data[1:4]); // CRC
            req.frame_length = 6;
            req.error_inject = 0;
            req.data_randomization = 0;
            finish_item(req);
            
            #1000; // Wait between register accesses
        end
    endtask
    
    // Simple CRC calculation for UART frames
    function bit [7:0] calculate_simple_crc(bit [7:0] data[]);
        bit [7:0] crc = 8'h00;
        foreach (data[i]) begin
            crc = crc ^ data[i];
        end
        return crc;
    endfunction
    
    // UART-based register write helper
    virtual task write_uart_register(bit [31:0] addr, bit [31:0] data);
        uart_frame_transaction req;
        req = uart_frame_transaction::type_id::create("uart_write_req");
        start_item(req);
        
        // UART Write Command: SOF + CMD(0x81) + ADDR_H + ADDR_L + DATA3 + DATA2 + DATA1 + DATA0 + CRC
        req.frame_data = new[9];
        req.frame_data[0] = 8'h5A;  // SOF
        req.frame_data[1] = 8'h81;  // WRITE_CMD
        req.frame_data[2] = addr[15:8];     // ADDR_H
        req.frame_data[3] = addr[7:0];      // ADDR_L
        req.frame_data[4] = data[31:24];    // DATA3 (MSB)
        req.frame_data[5] = data[23:16];    // DATA2
        req.frame_data[6] = data[15:8];     // DATA1
        req.frame_data[7] = data[7:0];      // DATA0 (LSB)
        req.frame_data[8] = calculate_simple_crc(req.frame_data[1:7]); // CRC
        req.frame_length = 9;
        req.error_inject = 0;
        req.data_randomization = 0;
        finish_item(req);
        
        `uvm_info(get_type_name(), $sformatf("UART Write: addr=0x%08x, data=0x%08x", addr, data), UVM_HIGH)
        #1000; // Wait between register accesses
    endtask
    
    // UART-based register read helper
    virtual task read_uart_register(bit [31:0] addr);
        uart_frame_transaction req;
        req = uart_frame_transaction::type_id::create("uart_read_req");
        start_item(req);
        
        // UART Read Command: SOF + CMD(0x80) + ADDR_H + ADDR_L + LEN(0x04) + CRC
        req.frame_data = new[6];
        req.frame_data[0] = 8'h5A;  // SOF
        req.frame_data[1] = 8'h80;  // READ_CMD
        req.frame_data[2] = addr[15:8];     // ADDR_H
        req.frame_data[3] = addr[7:0];      // ADDR_L
        req.frame_data[4] = 8'h04;          // LENGTH (4 bytes)
        req.frame_data[5] = calculate_simple_crc(req.frame_data[1:4]); // CRC
        req.frame_length = 6;
        req.error_inject = 0;
        req.data_randomization = 0;
        finish_item(req);
        
        `uvm_info(get_type_name(), $sformatf("UART Read: addr=0x%08x", addr), UVM_HIGH)
        #1000; // Wait between register accesses
    endtask
    
    // Write test patterns to all writable registers
    virtual task perform_register_write_patterns();
        `uvm_info(get_type_name(), "Phase 2: Writing test patterns to writable registers", UVM_MEDIUM)
        
        // Test CONTROL register - enable/disable patterns
        test_control_register();
        
        // Test CONFIG register - baud rate and timeout variations
        test_config_register();
        
        // Test DEBUG register - all debug modes
        test_debug_register();
    endtask
    
    virtual task test_control_register();
        bit [31:0] control_patterns[$] = {
            32'h0000_0000,  // Reset state
            32'h0000_0001,  // Enable bridge
            32'h0000_0002,  // Reset stats (self-clearing)
            32'h0000_0003   // Enable + reset (combination)
        };
        
        foreach (control_patterns[i]) begin
            write_uart_register(REG_CONTROL, control_patterns[i]);
            #100; // Allow time for side effects
            read_uart_register(REG_CONTROL); // Read back for toggle
        end
    endtask
    
    virtual task test_config_register();
        bit [31:0] nominal_baud_pattern = {24'h000000, 8'h00, MAX_BAUD_DIV};
        bit [31:0] nominal_timeout_pattern = {24'h000000, DEFAULT_TIMEOUT_CFG, 8'h00};
        bit [31:0] config_patterns[$] = {
            32'h0000_0000,              // Reset state  
            nominal_baud_pattern,       // Baud divisor only (maximum speed)
            nominal_timeout_pattern,    // Timeout only
            nominal_timeout_pattern | nominal_baud_pattern, // Both configured
            32'hFFFF_FFFF               // Maximum values (test reserved bits = 0)
        };
        
        foreach (config_patterns[i]) begin
            write_uart_register(REG_CONFIG, config_patterns[i]);
            read_uart_register(REG_CONFIG); // Verify reserved bits return 0
        end
    endtask
    
    virtual task test_debug_register();
        // Test all debug modes 0x0 through 0xF
        for (int debug_mode = 0; debug_mode < 16; debug_mode++) begin
            bit [31:0] debug_value = debug_mode & 32'h0000_000F;
            write_uart_register(REG_DEBUG, debug_value);
            read_uart_register(REG_DEBUG);
            #50; // Allow debug mode to take effect
        end
    endtask
    
    // Exercise special register behaviors
    virtual task perform_special_register_tests();
        `uvm_info(get_type_name(), "Phase 3: Special register behavior tests", UVM_MEDIUM)
        
        // Test W1C behavior on CONTROL[1] (reset_stats)
        test_w1c_behavior();
        
        // Test read-only register write attempts (should be ignored)
        test_readonly_writes();
        
        // Monitor counter increments if possible
        test_counter_monitoring();
    endtask
    
    virtual task test_w1c_behavior();
        // Write 1 to reset_stats bit multiple times
        write_uart_register(REG_CONTROL, 32'h0000_0002);
        read_uart_register(REG_CONTROL); // Should read bit[1] = 0 (self-clearing)
        
        write_uart_register(REG_CONTROL, 32'h0000_0003); // Enable + reset
        read_uart_register(REG_CONTROL); // Should read 0x0000_0001 (enable remains)
    endtask
    
    virtual task test_readonly_writes();
        bit [31:0] readonly_registers[$] = {
            REG_STATUS, REG_TX_COUNT, REG_RX_COUNT, REG_FIFO_STAT, REG_VERSION
        };
        
        // Attempt writes to read-only registers (should be ignored)
        foreach (readonly_registers[i]) begin
            write_uart_register(readonly_registers[i], 32'hFFFF_FFFF);
            read_uart_register(readonly_registers[i]); // Toggle read signals
        end
    endtask
    
    virtual task test_counter_monitoring();
        // Read counters multiple times to toggle all bits
        repeat (10) begin
            read_uart_register(REG_TX_COUNT);
            read_uart_register(REG_RX_COUNT);
            read_uart_register(REG_FIFO_STAT);
            #20;
        end
    endtask
    
    // Test address boundary conditions and error responses
    virtual task perform_address_boundary_tests();
        `uvm_info(get_type_name(), "Phase 4: Address boundary and error tests", UVM_MEDIUM)
        
        // Test unmapped address spaces (should return SLVERR)
        test_unmapped_addresses();
        
        // Test misaligned addresses (should return SLVERR)
        test_misaligned_addresses();
        
        // Test boundary addresses
        test_boundary_addresses();
    endtask
    
    virtual task test_unmapped_addresses();
        bit [31:0] unmapped_addrs[$] = {
            REG_BASE_ADDR + 32'h020,  // First unmapped
            REG_BASE_ADDR + 32'h100,  // Mid-range unmapped
            REG_BASE_ADDR + 32'hFFE   // Last unmapped (before 4KB boundary)
        };
        
        foreach (unmapped_addrs[i]) begin
            // These should generate error responses - important for error path toggle
            read_uart_register(unmapped_addrs[i]);
            write_uart_register(unmapped_addrs[i], 32'hDEAD_BEEF);
        end
    endtask
    
    virtual task test_misaligned_addresses();
        bit [31:0] misaligned_addrs[$] = {
            REG_CONTROL + 32'h001,  // +1 byte
            REG_STATUS + 32'h002,   // +2 bytes
            REG_CONFIG + 32'h003    // +3 bytes
        };
        
        foreach (misaligned_addrs[i]) begin
            read_uart_register(misaligned_addrs[i]);
            write_uart_register(misaligned_addrs[i], 32'h1234_5678);
        end
    endtask
    
    virtual task test_boundary_addresses();
        // Test exactly at register space boundaries
        read_uart_register(REG_BASE_ADDR);           // First valid address
        read_uart_register(REG_VERSION);             // Last valid address
        read_uart_register(REG_BASE_ADDR - 4); // Just before valid space
        read_uart_register(REG_BASE_ADDR + 32'h1000); // Just after valid space
    endtask
    
endclass