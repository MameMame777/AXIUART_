`timescale 1ns / 1ps

// Test Register Read/Write Test - Extended validation of all test registers
// Tests comprehensive read/write functionality with various patterns
class test_register_readwrite_test extends uart_axi4_base_test;
    `uvm_component_utils(test_register_readwrite_test)
    
    function new(string name = "test_register_readwrite_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual task main_phase(uvm_phase phase);
        register_comprehensive_access_sequence seq;
        
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "Starting Test Register Read/Write Test", UVM_LOW)
        
        seq = register_comprehensive_access_sequence::type_id::create("seq");
        
        // Test all 8 test registers with comprehensive patterns
        test_all_registers(seq);
        
        seq.start(env.uart_agt.sequencer);
        
        `uvm_info(get_type_name(), "Test Register Read/Write Test completed", UVM_LOW)
        phase.drop_objection(this);
    endtask
    
    // Comprehensive test of all test registers
    task test_all_registers(register_comprehensive_access_sequence seq);
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
        
        logic [31:0] read_data;
        
        `uvm_info(get_type_name(), "=== PHASE 1: Read Initial Values (should be 0x00000000) ===", UVM_LOW)
        
        // Phase 1: Read initial values - should all be 0x00000000
        for (int i = 0; i < 8; i++) begin
            seq.axi_read(test_addresses[i], read_data);
            if (read_data == 32'h00000000) begin
                `uvm_info(get_type_name(), $sformatf("%s initial read PASS: 0x%08X", reg_names[i], read_data), UVM_LOW)
            end else begin
                `uvm_error(get_type_name(), $sformatf("%s initial read FAIL: Expected=0x00000000, Got=0x%08X", reg_names[i], read_data))
            end
        end
        
        `uvm_info(get_type_name(), "=== PHASE 2: Write Test Patterns ===", UVM_LOW)
        
        // Phase 2: Write test patterns
        for (int i = 0; i < 8; i++) begin
            seq.axi_write(test_addresses[i], test_patterns[i]);
            `uvm_info(get_type_name(), $sformatf("%s write: 0x%08X -> 0x%08X", reg_names[i], test_patterns[i], test_addresses[i]), UVM_LOW)
        end
        
        `uvm_info(get_type_name(), "=== PHASE 3: Read Back and Verify Patterns ===", UVM_LOW)
        
        // Phase 3: Read back and verify
        for (int i = 0; i < 8; i++) begin
            seq.axi_read(test_addresses[i], read_data);
            if (read_data == test_patterns[i]) begin
                `uvm_info(get_type_name(), $sformatf("%s readback PASS: 0x%08X", reg_names[i], read_data), UVM_LOW)
            end else begin
                `uvm_error(get_type_name(), $sformatf("%s readback FAIL: Expected=0x%08X, Got=0x%08X", reg_names[i], test_patterns[i], read_data))
            end
        end
        
        `uvm_info(get_type_name(), "=== PHASE 4: Test Partial Writes (WSTRB patterns) ===", UVM_LOW)
        
        // Phase 4: Test partial writes with different WSTRB patterns
        test_partial_writes(seq, test_addresses[0], reg_names[0]); // Use REG_TEST_0 for partial write tests
        
        `uvm_info(get_type_name(), "=== PHASE 5: Test Address Boundary Conditions ===", UVM_LOW)
        
        // Phase 5: Test boundary conditions
        test_boundary_conditions(seq);
        
        `uvm_info(get_type_name(), "=== PHASE 6: Restore Initial State ===", UVM_LOW)
        
        // Phase 6: Clear all test registers back to 0x00000000
        for (int i = 0; i < 8; i++) begin
            seq.axi_write(test_addresses[i], 32'h00000000);
            `uvm_info(get_type_name(), $sformatf("%s cleared to 0x00000000", reg_names[i]), UVM_LOW)
        end
        
        // Final verification that all registers are cleared
        for (int i = 0; i < 8; i++) begin
            seq.axi_read(test_addresses[i], read_data);
            if (read_data == 32'h00000000) begin
                `uvm_info(get_type_name(), $sformatf("%s final clear PASS: 0x%08X", reg_names[i], read_data), UVM_LOW)
            end else begin
                `uvm_error(get_type_name(), $sformatf("%s final clear FAIL: Expected=0x00000000, Got=0x%08X", reg_names[i], read_data))
            end
        end
    endtask
    
    // Test partial writes with different WSTRB patterns
    task test_partial_writes(uart_axi4_sequence seq, logic [31:0] test_addr, string reg_name);
        logic [31:0] read_data;
        logic [31:0] original_value = 32'hDEADBEEF;
        
        // Set up initial value
        seq.axi_write(test_addr, original_value);
        
        // Test byte write (WSTRB = 4'b0001) - write to byte 0
        seq.axi_write_with_strb(test_addr, 32'h000000AA, 4'b0001);
        seq.axi_read(test_addr, read_data);
        if (read_data == 32'hDEADBEAA) begin
            `uvm_info(get_type_name(), $sformatf("%s byte write PASS: 0x%08X", reg_name, read_data), UVM_LOW)
        end else begin
            `uvm_error(get_type_name(), $sformatf("%s byte write FAIL: Expected=0xDEADBEAA, Got=0x%08X", reg_name, read_data))
        end
        
        // Test halfword write (WSTRB = 4'b0011) - write to lower halfword
        seq.axi_write_with_strb(test_addr, 32'h00005555, 4'b0011);
        seq.axi_read(test_addr, read_data);
        if (read_data == 32'hDEAD5555) begin
            `uvm_info(get_type_name(), $sformatf("%s halfword write PASS: 0x%08X", reg_name, read_data), UVM_LOW)
        end else begin
            `uvm_error(get_type_name(), $sformatf("%s halfword write FAIL: Expected=0xDEAD5555, Got=0x%08X", reg_name, read_data))
        end
        
        // Test upper halfword write (WSTRB = 4'b1100) - write to upper halfword  
        seq.axi_write_with_strb(test_addr + 2, 32'h12340000, 4'b1100);
        seq.axi_read(test_addr, read_data);
        if (read_data == 32'h12345555) begin
            `uvm_info(get_type_name(), $sformatf("%s upper halfword write PASS: 0x%08X", reg_name, read_data), UVM_LOW)
        end else begin
            `uvm_error(get_type_name(), $sformatf("%s upper halfword write FAIL: Expected=0x12345555, Got=0x%08X", reg_name, read_data))
        end
    endtask
    
    // Test address boundary conditions
    task test_boundary_conditions(uart_axi4_sequence seq);
        logic [31:0] read_data;
        logic [1:0] resp;
        
        // Test invalid addresses (should return SLVERR)
        logic [31:0] invalid_addresses[4] = '{
            32'h00001018,  // Gap between REG_FIFO_STAT and REG_TEST_0
            32'h00001030,  // Gap between REG_TEST_3 and REG_TEST_4
            32'h00001200,  // Beyond REG_TEST_7
            32'h00000FFF   // Below base address
        };
        
        for (int i = 0; i < 4; i++) begin
            // Test read to invalid address
            seq.axi_read_with_resp(invalid_addresses[i], read_data, resp);
            if (resp == 2'b10) begin // SLVERR
                `uvm_info(get_type_name(), $sformatf("Invalid address read PASS: 0x%08X -> SLVERR", invalid_addresses[i]), UVM_LOW)
            end else begin
                `uvm_error(get_type_name(), $sformatf("Invalid address read FAIL: 0x%08X -> resp=%0d (expected SLVERR)", invalid_addresses[i], resp))
            end
            
            // Test write to invalid address
            seq.axi_write_with_resp(invalid_addresses[i], 32'hDEADBEEF, resp);
            if (resp == 2'b10) begin // SLVERR
                `uvm_info(get_type_name(), $sformatf("Invalid address write PASS: 0x%08X -> SLVERR", invalid_addresses[i]), UVM_LOW)
            end else begin
                `uvm_error(get_type_name(), $sformatf("Invalid address write FAIL: 0x%08X -> resp=%0d (expected SLVERR)", invalid_addresses[i], resp))
            end
        end
    endtask
    
endclass