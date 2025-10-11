`timescale 1ns / 1ps

// Comprehensive RTL-based Error Injection Test
// Based on Frame_Parser.sv error handling specifications
class uart_axi4_comprehensive_error_injection_test extends uart_axi4_base_test;
    
    `uvm_component_utils(uart_axi4_comprehensive_error_injection_test)
    
    // Error injection sequences for each RTL error condition
    uart_axi4_crc_error_sequence       crc_error_seq;
    uart_axi4_cmd_invalid_sequence     cmd_invalid_seq; 
    uart_axi4_addr_align_sequence      addr_align_seq;
    uart_axi4_timeout_sequence         timeout_seq;
    uart_axi4_len_range_sequence       len_range_seq;
    uart_axi4_protocol_violation_sequence protocol_violation_seq;
    
    function new(string name = "uart_axi4_comprehensive_error_injection_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Create error injection sequences
        crc_error_seq = uart_axi4_crc_error_sequence::type_id::create("crc_error_seq");
        cmd_invalid_seq = uart_axi4_cmd_invalid_sequence::type_id::create("cmd_invalid_seq");
        addr_align_seq = uart_axi4_addr_align_sequence::type_id::create("addr_align_seq");
        timeout_seq = uart_axi4_timeout_sequence::type_id::create("timeout_seq");
        len_range_seq = uart_axi4_len_range_sequence::type_id::create("len_range_seq");
        protocol_violation_seq = uart_axi4_protocol_violation_sequence::type_id::create("protocol_violation_seq");
        
        `uvm_info(get_type_name(), "Comprehensive Error Injection Test Build Phase Complete", UVM_MEDIUM)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Starting Comprehensive Error Injection Test", UVM_LOW)
        
        // Test 1: CRC Error Injection (STATUS_CRC_ERR = 0x01)
        `uvm_info(get_type_name(), "=== Testing CRC Error Injection ===", UVM_LOW)
        crc_error_seq.start(m_env.m_uart_agent.m_sequencer);
        #1000ns;
        
        // Test 2: Command Invalid Error (STATUS_CMD_INV = 0x02)
        `uvm_info(get_type_name(), "=== Testing Command Invalid Error ===", UVM_LOW)
        cmd_invalid_seq.start(m_env.m_uart_agent.m_sequencer);
        #1000ns;
        
        // Test 3: Address Alignment Error (STATUS_ADDR_ALIGN = 0x03)
        `uvm_info(get_type_name(), "=== Testing Address Alignment Error ===", UVM_LOW)
        addr_align_seq.start(m_env.m_uart_agent.m_sequencer);
        #1000ns;
        
        // Test 4: Timeout Error (STATUS_TIMEOUT = 0x04)
        `uvm_info(get_type_name(), "=== Testing Timeout Error ===", UVM_LOW)
        timeout_seq.start(m_env.m_uart_agent.m_sequencer);
        #1000ns;
        
        // Test 5: Length Range Error (STATUS_LEN_RANGE = 0x07)
        `uvm_info(get_type_name(), "=== Testing Length Range Error ===", UVM_LOW)
        len_range_seq.start(m_env.m_uart_agent.m_sequencer);
        #1000ns;
        
        // Test 6: Protocol Violation (Multiple error conditions)
        `uvm_info(get_type_name(), "=== Testing Protocol Violations ===", UVM_LOW)
        protocol_violation_seq.start(m_env.m_uart_agent.m_sequencer);
        #1000ns;
        
        `uvm_info(get_type_name(), "Comprehensive Error Injection Test Complete", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass

// CRC Error Injection Sequence - Based on CRC8 polynomial 0x07
class uart_axi4_crc_error_sequence extends uart_axi4_base_sequence;
    
    `uvm_object_utils(uart_axi4_crc_error_sequence)
    
    function new(string name = "uart_axi4_crc_error_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_axi4_transaction trans;
        
        // Create valid frame with deliberately corrupted CRC
        trans = uart_axi4_transaction::type_id::create("trans");
        start_item(trans);
        
        // Valid frame structure
        trans.sof = 8'hA5;  // Correct SOF
        trans.cmd = 8'h80;  // Read command, 1 byte
        trans.addr = 32'h00001000;  // Valid aligned address
        trans.data = new[1];
        trans.data[0] = 8'h55;
        
        // Calculate correct CRC then corrupt it
        trans.crc = calculate_crc8(trans) ^ 8'hFF;  // Deliberate corruption
        trans.inject_crc_error = 1'b1;
        trans.expected_status = 8'h01;  // STATUS_CRC_ERR
        
        finish_item(trans);
        
        `uvm_info(get_type_name(), $sformatf("CRC Error Injection: Original CRC would be 0x%02X, sending corrupted 0x%02X", 
                  calculate_crc8(trans) ^ 8'hFF, trans.crc), UVM_MEDIUM)
    endtask
    
    // CRC8 calculation function matching RTL polynomial 0x07
    function bit [7:0] calculate_crc8(uart_axi4_transaction trans);
        bit [7:0] crc = 8'h00;
        bit [7:0] data_bytes[];
        int byte_count = 0;
        
        // Serialize frame data for CRC calculation
        data_bytes = new[6 + trans.data.size()];
        data_bytes[0] = trans.sof;
        data_bytes[1] = trans.cmd;
        data_bytes[2] = trans.addr[31:24];
        data_bytes[3] = trans.addr[23:16];
        data_bytes[4] = trans.addr[15:8];
        data_bytes[5] = trans.addr[7:0];
        
        for (int i = 0; i < trans.data.size(); i++) begin
            data_bytes[6 + i] = trans.data[i];
        end
        
        // CRC8 calculation with polynomial 0x07
        for (int i = 0; i < data_bytes.size(); i++) begin
            crc = crc ^ data_bytes[i];
            for (int j = 0; j < 8; j++) begin
                if (crc & 8'h80) begin
                    crc = (crc << 1) ^ 8'h07;
                end else begin
                    crc = crc << 1;
                end
            end
        end
        
        return crc;
    endfunction
    
endclass

// Command Invalid Error Sequence - Based on size_field validation
class uart_axi4_cmd_invalid_sequence extends uart_axi4_base_sequence;
    
    `uvm_object_utils(uart_axi4_cmd_invalid_sequence)
    
    function new(string name = "uart_axi4_cmd_invalid_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_axi4_transaction trans;
        
        // Test invalid size field (2'b11 - reserved)
        trans = uart_axi4_transaction::type_id::create("trans");
        start_item(trans);
        
        trans.sof = 8'hA5;
        trans.cmd = 8'hB0;  // size_field = 2'b11 (invalid), len_field = 0
        trans.addr = 32'h00001000;
        trans.data = new[0];  // No data for invalid command
        trans.crc = calculate_crc8(trans);
        trans.inject_cmd_error = 1'b1;
        trans.expected_status = 8'h02;  // STATUS_CMD_INV
        
        finish_item(trans);
        
        `uvm_info(get_type_name(), $sformatf("Command Invalid: size_field=2'b11 (reserved), cmd=0x%02X", trans.cmd), UVM_MEDIUM)
    endtask
    
    function bit [7:0] calculate_crc8(uart_axi4_transaction trans);
        // Same CRC calculation as above
        bit [7:0] crc = 8'h00;
        bit [7:0] data_bytes[] = '{trans.sof, trans.cmd, trans.addr[31:24], trans.addr[23:16], trans.addr[15:8], trans.addr[7:0]};
        
        for (int i = 0; i < data_bytes.size(); i++) begin
            crc = crc ^ data_bytes[i];
            for (int j = 0; j < 8; j++) begin
                if (crc & 8'h80) crc = (crc << 1) ^ 8'h07;
                else crc = crc << 1;
            end
        end
        return crc;
    endfunction
    
endclass

// Address Alignment Error Sequence
class uart_axi4_addr_align_sequence extends uart_axi4_base_sequence;
    
    `uvm_object_utils(uart_axi4_addr_align_sequence)
    
    function new(string name = "uart_axi4_addr_align_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_axi4_transaction trans;
        
        // Test misaligned address for 4-byte access
        trans = uart_axi4_transaction::type_id::create("trans");
        start_item(trans);
        
        trans.sof = 8'hA5;
        trans.cmd = 8'hA1;  // 4-byte access, len=1
        trans.addr = 32'h00001003;  // Misaligned for 4-byte access
        trans.data = new[4];
        for (int i = 0; i < 4; i++) trans.data[i] = 8'h55 + i;
        trans.crc = calculate_crc8(trans);
        trans.inject_addr_error = 1'b1;
        trans.expected_status = 8'h03;  // STATUS_ADDR_ALIGN
        
        finish_item(trans);
        
        `uvm_info(get_type_name(), $sformatf("Address Alignment Error: 4-byte access at misaligned addr=0x%08X", trans.addr), UVM_MEDIUM)
    endtask
    
    function bit [7:0] calculate_crc8(uart_axi4_transaction trans);
        bit [7:0] crc = 8'h00;
        bit [7:0] data_bytes[];
        data_bytes = new[6 + trans.data.size()];
        data_bytes[0] = trans.sof;
        data_bytes[1] = trans.cmd;
        data_bytes[2] = trans.addr[31:24];
        data_bytes[3] = trans.addr[23:16];
        data_bytes[4] = trans.addr[15:8];
        data_bytes[5] = trans.addr[7:0];
        for (int i = 0; i < trans.data.size(); i++) data_bytes[6 + i] = trans.data[i];
        
        for (int i = 0; i < data_bytes.size(); i++) begin
            crc = crc ^ data_bytes[i];
            for (int j = 0; j < 8; j++) begin
                if (crc & 8'h80) crc = (crc << 1) ^ 8'h07;
                else crc = crc << 1;
            end
        end
        return crc;
    endfunction
    
endclass

// Timeout Error Sequence
class uart_axi4_timeout_sequence extends uart_axi4_base_sequence;
    
    `uvm_object_utils(uart_axi4_timeout_sequence)
    
    function new(string name = "uart_axi4_timeout_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_axi4_transaction trans;
        
        // Create transaction that will cause AXI timeout
        trans = uart_axi4_transaction::type_id::create("trans");
        start_item(trans);
        
        trans.sof = 8'hA5;
        trans.cmd = 8'h81;  // Read command
        trans.addr = 32'hFFFFFFFF;  // Address that might cause timeout
        trans.data = new[1];
        trans.data[0] = 8'h00;
        trans.crc = calculate_crc8(trans);
        trans.inject_timeout_error = 1'b1;
        trans.expected_status = 8'h04;  // STATUS_TIMEOUT
        
        finish_item(trans);
        
        `uvm_info(get_type_name(), "Timeout Error: Transaction to invalid address", UVM_MEDIUM)
    endtask
    
    function bit [7:0] calculate_crc8(uart_axi4_transaction trans);
        bit [7:0] crc = 8'h00;
        bit [7:0] data_bytes[] = '{trans.sof, trans.cmd, trans.addr[31:24], trans.addr[23:16], trans.addr[15:8], trans.addr[7:0], trans.data[0]};
        
        for (int i = 0; i < data_bytes.size(); i++) begin
            crc = crc ^ data_bytes[i];
            for (int j = 0; j < 8; j++) begin
                if (crc & 8'h80) crc = (crc << 1) ^ 8'h07;
                else crc = crc << 1;
            end
        end
        return crc;
    endfunction
    
endclass

// Length Range Error Sequence
class uart_axi4_len_range_sequence extends uart_axi4_base_sequence;
    
    `uvm_object_utils(uart_axi4_len_range_sequence)
    
    function new(string name = "uart_axi4_len_range_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_axi4_transaction trans;
        
        // Test length field that exceeds maximum (len_field > maximum for size)
        trans = uart_axi4_transaction::type_id::create("trans");
        start_item(trans);
        
        trans.sof = 8'hA5;
        trans.cmd = 8'h8F;  // 1-byte access with len_field = 15 (excessive)
        trans.addr = 32'h00001000;
        trans.data = new[16];  // 16 bytes for 1-byte access type
        for (int i = 0; i < 16; i++) trans.data[i] = 8'h10 + i;
        trans.crc = calculate_crc8(trans);
        trans.inject_len_error = 1'b1;
        trans.expected_status = 8'h07;  // STATUS_LEN_RANGE
        
        finish_item(trans);
        
        `uvm_info(get_type_name(), "Length Range Error: len_field=15 for 1-byte access", UVM_MEDIUM)
    endtask
    
    function bit [7:0] calculate_crc8(uart_axi4_transaction trans);
        bit [7:0] crc = 8'h00;
        bit [7:0] data_bytes[];
        data_bytes = new[6 + trans.data.size()];
        data_bytes[0] = trans.sof;
        data_bytes[1] = trans.cmd;
        data_bytes[2] = trans.addr[31:24];
        data_bytes[3] = trans.addr[23:16];
        data_bytes[4] = trans.addr[15:8];
        data_bytes[5] = trans.addr[7:0];
        for (int i = 0; i < trans.data.size(); i++) data_bytes[6 + i] = trans.data[i];
        
        for (int i = 0; i < data_bytes.size(); i++) begin
            crc = crc ^ data_bytes[i];
            for (int j = 0; j < 8; j++) begin
                if (crc & 8'h80) crc = (crc << 1) ^ 8'h07;
                else crc = crc << 1;
            end
        end
        return crc;
    endfunction
    
endclass

// Protocol Violation Sequence - Multiple errors
class uart_axi4_protocol_violation_sequence extends uart_axi4_base_sequence;
    
    `uvm_object_utils(uart_axi4_protocol_violation_sequence)
    
    function new(string name = "uart_axi4_protocol_violation_sequence");
        super.new(name);
    endfunction
    
    virtual task body();
        uart_axi4_transaction trans;
        
        // Test 1: Invalid SOF
        trans = uart_axi4_transaction::type_id::create("trans");
        start_item(trans);
        trans.sof = 8'h00;  // Invalid SOF (should be 0xA5)
        trans.cmd = 8'h80;
        trans.addr = 32'h00001000;
        trans.data = new[1];
        trans.data[0] = 8'h55;
        trans.crc = 8'h00;  // Don't care for invalid SOF
        trans.inject_protocol_error = 1'b1;
        finish_item(trans);
        
        #500ns;
        
        // Test 2: Truncated frame
        trans = uart_axi4_transaction::type_id::create("trans");
        start_item(trans);
        trans.sof = 8'hA5;
        trans.cmd = 8'h81;  // Expect 1 byte but send truncated
        trans.addr = 32'h00001000;
        trans.data = new[0];  // No data (truncated)
        trans.inject_truncation_error = 1'b1;
        finish_item(trans);
        
        `uvm_info(get_type_name(), "Protocol Violations: Invalid SOF and Truncated Frame", UVM_MEDIUM)
    endtask
    
endclass