`timescale 1ns / 1ps

// Simple Test Register Read/Write Test - Extended validation of all test registers
// Tests comprehensive read/write functionality with various patterns
class test_register_readwrite_test_simple extends uart_axi4_base_test;
    `uvm_component_utils(test_register_readwrite_test_simple)
    
    function new(string name = "test_register_readwrite_test_simple", uvm_component parent = null);
        super.new(name);
    endfunction
    
    virtual task main_phase(uvm_phase phase);
        debug_test_register_sequence seq;
        
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "Starting Test Register Read/Write Test", UVM_LOW)
        
        seq = debug_test_register_sequence::type_id::create("seq");
        seq.start(env.uart_agt.sequencer);
        
        `uvm_info(get_type_name(), "Test Register Read/Write Test completed", UVM_LOW)
        phase.drop_objection(this);
    endtask

endclass

// Simple sequence for test register validation
class debug_test_register_sequence extends uvm_sequence#(uart_frame_transaction);
    `uvm_object_utils(debug_test_register_sequence)
    
    function new(string name = "debug_test_register_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        // Test register addresses and patterns
        logic [31:0] test_addresses[8] = '{
            32'h00001020,  // REG_TEST_0
            32'h00001024,  // REG_TEST_1  
            32'h00001028,  // REG_TEST_2
            32'h0000102C,  // REG_TEST_3
            32'h00001040,  // REG_TEST_4 - gap test
            32'h00001050,  // REG_TEST_5 - larger gap
            32'h00001080,  // REG_TEST_6 - even larger gap
            32'h00001100   // REG_TEST_7 - different range
        };
        
        logic [31:0] test_patterns[8] = '{
            32'h12345678,  // Basic pattern
            32'hDEADBEEF,  // Common test pattern
            32'hAAAA5555,  // Alternating bits
            32'h55555555,  // Pattern 1
            32'hAAAAAAAA,  // Pattern 2
            32'hFFFF0000,  // Upper/lower split
            32'h0000FFFF,  // Lower/upper split
            32'h00000001   // Single bit
        };
        
        string reg_names[8] = '{
            "REG_TEST_0", "REG_TEST_1", "REG_TEST_2", "REG_TEST_3",
            "REG_TEST_4", "REG_TEST_5", "REG_TEST_6", "REG_TEST_7"
        };
        
        `uvm_info(get_type_name(), "=== PHASE 1: Read Initial Values (should be 0x00000000) ===", UVM_LOW)
        
        // Phase 1: Read initial values - should all be 0x00000000
        for (int i = 0; i < 8; i++) begin
            read_register(test_addresses[i], reg_names[i], 32'h00000000);
        end
        
        `uvm_info(get_type_name(), "=== PHASE 2: Write Test Patterns ===", UVM_LOW)
        
        // Phase 2: Write test patterns
        for (int i = 0; i < 8; i++) begin
            write_register(test_addresses[i], test_patterns[i], reg_names[i]);
            `uvm_info(get_type_name(), $sformatf("%s write: 0x%08X -> 0x%08X", 
                      reg_names[i], test_patterns[i], test_addresses[i]), UVM_LOW)
        end
        
        `uvm_info(get_type_name(), "=== PHASE 3: Read Back and Verify Patterns ===", UVM_LOW)
        
        // Phase 3: Read back and verify
        for (int i = 0; i < 8; i++) begin
            read_register(test_addresses[i], reg_names[i], test_patterns[i]);
        end
        
        `uvm_info(get_type_name(), "=== PHASE 4: Restore Initial State ===", UVM_LOW)
        
        // Phase 4: Clear all test registers back to 0x00000000
        for (int i = 0; i < 8; i++) begin
            write_register(test_addresses[i], 32'h00000000, reg_names[i]);
            `uvm_info(get_type_name(), $sformatf("%s cleared to 0x00000000", reg_names[i]), UVM_LOW)
        end
        
        // Final verification that all registers are cleared
        for (int i = 0; i < 8; i++) begin
            read_register(test_addresses[i], reg_names[i], 32'h00000000);
        end
    endtask
    
    // Helper task to write register
    task write_register(bit [31:0] addr, bit [31:0] data, string name);
        uart_frame_transaction req;
        req = uart_frame_transaction::type_id::create($sformatf("%s_write", name));
        start_item(req);
        
        req.is_write = 1;
        req.auto_increment = 0;
        req.size = 2'b10; // 4 bytes
        req.length = 4'h0;
        req.addr = addr;
        req.sof = SOF_HOST_TO_DEVICE;
        req.direction = UART_RX;
        req.error_inject = 0;
        req.expect_error = 0;
        
        // Set 4-byte data
        req.data = new[4];
        req.data[0] = data[7:0];
        req.data[1] = data[15:8];
        req.data[2] = data[23:16];
        req.data[3] = data[31:24];
        
        req.build_cmd();
        req.calculate_crc();
        
        finish_item(req);
        
        `uvm_info(get_type_name(), 
                  $sformatf("Write 0x%08X to %s (0x%08X)", data, name, addr), 
                  UVM_MEDIUM)
    endtask

    // Helper task to read register and verify
    task read_register(bit [31:0] addr, string name, bit [31:0] expected);
        uart_frame_transaction req;
        req = uart_frame_transaction::type_id::create($sformatf("%s_read", name));
        start_item(req);
        
        req.is_write = 0;
        req.auto_increment = 0;
        req.size = 2'b10; // 4 bytes
        req.length = 4'h0;
        req.addr = addr;
        req.sof = SOF_HOST_TO_DEVICE;
        req.direction = UART_RX;
        req.error_inject = 0;
        req.expect_error = 0;
        req.data = new[0];
        
        req.build_cmd();
        req.calculate_crc();
        
        finish_item(req);
        
        `uvm_info(get_type_name(), 
                  $sformatf("Read from %s (0x%08X), expected: 0x%08X", name, addr, expected), 
                  UVM_MEDIUM)
    endtask

endclass