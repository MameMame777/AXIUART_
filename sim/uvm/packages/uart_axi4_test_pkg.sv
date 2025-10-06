`timescale 1ns / 1ps

// UVM Test Package for UART-AXI4 Bridge
// Contains all UVM components, sequences, tests, and utilities
package uart_axi4_test_pkg;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // Configuration class first (must be before anything that uses it)
    `include "../env/uart_axi4_env_config.sv"
    
    // Transaction direction constants
    typedef enum { UART_RX, UART_TX } uart_direction_t;
    typedef enum { AXI_WRITE, AXI_READ } axi_trans_type_t;
    
    // Protocol constants
    parameter int CLK_FREQ_HZ = 125_000_000;
    parameter int BAUD_RATE = 115200;
    parameter int BIT_TIME_NS = 1_000_000_000 / BAUD_RATE;
    parameter int BYTE_TIME_NS = BIT_TIME_NS * 10; // 8 data + 1 start + 1 stop
    
    // Frame constants from protocol specification
    parameter logic [7:0] SOF_HOST_TO_DEVICE = 8'hA5;  // Host to device SOF (corrected to match RTL)
    parameter logic [7:0] SOF_DEVICE_TO_HOST = 8'h5A;  // Device to host SOF (matches RTL Frame_Builder)
    
    // Command constants
    parameter logic [7:0] READ_CMD  = 8'h80;  // Read command (bit 7 = 1)
    parameter logic [7:0] WRITE_CMD = 8'h00;  // Write command (bit 7 = 0)
    
    // Register addresses for testing
    parameter logic [31:0] TEST_REG_ADDR        = 32'h0000_1000;
    parameter logic [31:0] STATUS_REG_ADDR      = 32'h0000_1004;
    parameter logic [31:0] FIFO_STATUS_REG_ADDR = 32'h0000_1008;
    
    // Status codes
    parameter logic [7:0] STATUS_OK         = 8'h00;
    parameter logic [7:0] STATUS_CRC_ERR    = 8'h01;
    parameter logic [7:0] STATUS_CMD_INV    = 8'h02;
    parameter logic [7:0] STATUS_ADDR_ALIGN = 8'h03;
    parameter logic [7:0] STATUS_TIMEOUT    = 8'h04;
    parameter logic [7:0] STATUS_AXI_SLVERR = 8'h05;
    parameter logic [7:0] STATUS_BUSY       = 8'h06;
    parameter logic [7:0] STATUS_LEN_RANGE  = 8'h07;
    parameter logic [7:0] STATUS_MONITOR_PARSE_FAIL = 8'hF0;

    typedef enum logic [2:0] {
        PARSE_ERROR_NONE,
        PARSE_ERROR_SOF_MISMATCH,
        PARSE_ERROR_LENGTH,
        PARSE_ERROR_STOP_BIT,
        PARSE_ERROR_CRC,
        PARSE_ERROR_PAYLOAD
    } uart_monitor_parse_error_e;
    
    // CRC8 calculation function (polynomial 0x07)
    function automatic logic [7:0] calculate_crc8(input logic [7:0] data[], input int length);
        logic [7:0] crc = 8'h00;
        logic [7:0] temp;
        
        for (int i = 0; i < length; i++) begin
            temp = crc ^ data[i];
            for (int j = 0; j < 8; j++) begin
                if (temp[7]) begin
                    temp = (temp << 1) ^ 8'h07;
                end else begin
                    temp = temp << 1;
                end
            end
            crc = temp;
        end
        return crc;
    endfunction
    
    // UART frame transaction class
    class uart_frame_transaction extends uvm_sequence_item;
        
        // Frame fields - standardized naming
        rand logic [7:0]  sof;      // Start of Frame byte
        rand logic [7:0]  cmd;
        logic [31:0] addr;          // CRITICAL: Remove rand to prevent randomization override
        rand logic [7:0]  len;      // Length byte
        logic [7:0]  data[];        // CRITICAL: Remove rand to prevent randomization override
        logic [7:0]       crc;
        
        // Standardized frame fields for compatibility
        rand logic [7:0]  frame_data[];  // Complete frame data including SOF, CMD, ADDR, DATA, CRC
        rand int          frame_length;  // Total frame length in bytes
        
        // Transaction type
        rand bit is_write;
        rand bit auto_increment;
        rand logic [1:0] size;  // 00=8bit, 01=16bit, 10=32bit, 11=reserved
        rand logic [3:0] length; // 0-15 (actual length is length+1)
        
        // Transaction direction and timing
        uart_direction_t direction;
        realtime timestamp;
        bit crc_valid;
        
        // Error injection fields - standardized
        bit force_crc_error = 0;
        bit force_timeout = 0;
        bit corrupt_frame_format = 0;
        bit truncate_frame = 0;
        bit wrong_sof = 0;
        bit error_inject = 0;        // General error injection flag
    bit expect_error = 0;         // Expect an error response from DUT
        bit data_randomization = 0;  // Data randomization control
        
        // Response fields
        logic [7:0] response_status;
        logic [7:0] response_data[];
        bit response_received;
        
        // Coverage support fields (for axiuart_cov_pkg)
        logic [31:0] target_addr;    // Alias for addr
        bit [6:0]    rx_fifo_level;  // FIFO monitoring
        bit [6:0]    tx_fifo_level;  // FIFO monitoring
        bit          parity_error;   // Error flags
        bit          framing_error;
        bit          timeout_error;
        bit [2:0]    parser_state;   // FSM states
        bit [2:0]    axi_state;
    bit [2:0]    frame_type;     // Derived field
    bit [7:0]    crc_result;     // CRC calculation result
    uart_monitor_parse_error_e parse_error_kind;
    bit          monitor_recovered;
        
        // Constraints
        constraint c_valid_size { size inside {2'b00, 2'b01, 2'b10}; }
        constraint c_valid_length { length <= 15; } // Max 16 beats
        // Note: data size constraint removed as data is now non-rand and managed explicitly
        
        `uvm_object_utils_begin(uart_frame_transaction)
            `uvm_field_int(sof, UVM_ALL_ON)
            `uvm_field_int(cmd, UVM_ALL_ON)
            `uvm_field_int(addr, UVM_ALL_ON)
            `uvm_field_int(len, UVM_ALL_ON)
            `uvm_field_array_int(data, UVM_ALL_ON)
            `uvm_field_int(crc, UVM_ALL_ON)
            `uvm_field_array_int(frame_data, UVM_ALL_ON)
            `uvm_field_int(frame_length, UVM_ALL_ON)
            `uvm_field_int(is_write, UVM_ALL_ON)
            `uvm_field_int(auto_increment, UVM_ALL_ON)
            `uvm_field_int(size, UVM_ALL_ON)
            `uvm_field_int(length, UVM_ALL_ON)
            `uvm_field_enum(uart_direction_t, direction, UVM_ALL_ON)
            `uvm_field_real(timestamp, UVM_ALL_ON)
            `uvm_field_int(crc_valid, UVM_ALL_ON)
            `uvm_field_int(error_inject, UVM_ALL_ON)
            `uvm_field_int(data_randomization, UVM_ALL_ON)
            `uvm_field_int(expect_error, UVM_ALL_ON)
            `uvm_field_int(response_status, UVM_ALL_ON)
            `uvm_field_array_int(response_data, UVM_ALL_ON)
            `uvm_field_int(response_received, UVM_ALL_ON)
            `uvm_field_enum(uart_monitor_parse_error_e, parse_error_kind, UVM_ALL_ON)
            `uvm_field_int(monitor_recovered, UVM_ALL_ON)
        `uvm_object_utils_end
        
        function new(string name = "uart_frame_transaction");
            super.new(name);
            data = new[1];
            response_data = new[1];
            parse_error_kind = PARSE_ERROR_NONE;
            monitor_recovered = 0;
        endfunction
        
        // Build command byte
        function void build_cmd();
            cmd = {is_write ? 1'b0 : 1'b1, auto_increment, size, length};
        endfunction
        
        // Calculate and set CRC
        function void calculate_crc();
            logic [7:0] frame_bytes[];
            int byte_count;
            
            // Count bytes for CRC calculation
            byte_count = 1 + 4; // CMD + ADDR
            if (is_write) byte_count += data.size();
            
            frame_bytes = new[byte_count];
            frame_bytes[0] = cmd;
            frame_bytes[1] = addr[7:0];
            frame_bytes[2] = addr[15:8];
            frame_bytes[3] = addr[23:16];
            frame_bytes[4] = addr[31:24];
            
            if (is_write) begin
                for (int i = 0; i < data.size(); i++) begin
                    frame_bytes[5 + i] = data[i];
                end
            end
            
            crc = calculate_crc8(frame_bytes, byte_count);
        endfunction
        
        function void post_randomize();
            build_cmd();
            calculate_crc();
            
            // Synchronize frame_data with data array
            if (data.size() > 0) begin
                frame_data = new[data.size()];
                for (int i = 0; i < data.size(); i++) begin
                    frame_data[i] = data[i];
                end
                frame_length = data.size();
            end else begin
                frame_data = new[1];
                frame_data[0] = 8'h00;
                frame_length = 0;
            end
            
            // Initialize coverage support fields
            target_addr = addr;
            crc_result = crc;
            frame_type = cmd[7:5]; // Extract frame type from command
            
            // Error flags initialized to no error
            parity_error = 1'b0;
            framing_error = 1'b0; 
            timeout_error = 1'b0;
            
            // FIFO levels initialized to empty
            rx_fifo_level = 7'h00;
            tx_fifo_level = 7'h00;
            
            // FSM states initialized  
            parser_state = 3'h0;
            axi_state = 3'h0;
        endfunction
        
    endclass
    
    // AXI transaction item for monitoring
    class axi4_lite_transaction extends uvm_sequence_item;
        logic [31:0] addr;
        logic [31:0] wdata;
        logic [3:0]  wstrb;
        logic [31:0] rdata;
        logic [1:0]  bresp;
        logic [1:0]  rresp;
        bit is_write;
        axi_trans_type_t trans_type;
        
        // Additional fields needed by sequences and coverage
        logic [1:0]  size;           // AXI size field: 00=8bit, 01=16bit, 10=32bit
        bit          expect_error;   // For error injection testing
        
        // Additional fields needed by agents
        realtime timestamp;
        bit completed;
        
        // Aliases for driver/monitor compatibility
        logic [31:0] data;
        logic [1:0] resp;
        logic [3:0] strb;
        
        function void post_randomize();
            // Sync aliased fields
            if (is_write) begin
                data = wdata;
                strb = wstrb;
                resp = bresp;
            end else begin
                data = rdata;
                resp = rresp;
                strb = 4'hF; // Default for read
            end
        endfunction
        
        `uvm_object_utils_begin(axi4_lite_transaction)
            `uvm_field_int(addr, UVM_ALL_ON)
            `uvm_field_int(wdata, UVM_ALL_ON)
            `uvm_field_int(wstrb, UVM_ALL_ON)
            `uvm_field_int(rdata, UVM_ALL_ON)
            `uvm_field_int(bresp, UVM_ALL_ON)
            `uvm_field_int(rresp, UVM_ALL_ON)
            `uvm_field_int(is_write, UVM_ALL_ON)
            `uvm_field_enum(axi_trans_type_t, trans_type, UVM_ALL_ON)
            `uvm_field_real(timestamp, UVM_ALL_ON)
            `uvm_field_int(completed, UVM_ALL_ON)
        `uvm_object_utils_end
        
        function new(string name = "axi4_lite_transaction");
            super.new(name);
        endfunction
    endclass

    // Include UVM component files in dependency order  
    // Components are now compiled within the package context
    
    // First include coverage and scoreboard (needed by monitor)
    `include "env/uart_axi4_coverage.sv"
    `include "env/uart_axi4_scoreboard.sv"
    `include "agents/axi4_lite/axi4_lite_monitor.sv"
    `include "monitors/bridge_status_monitor.sv"
    
    // Then include driver and monitor classes
    `include "agents/uart/uart_driver.sv"
    `include "agents/uart/uart_monitor.sv"
    
    // Then agent definitions
    `include "agents/uart_agent.sv"
    
    // Finally environment (when agents are ready)
    `include "env/uart_axi4_env.sv"
    
    // Sequence libraries (need transaction classes to be defined first)
    `include "sequences/basic_func_sequence.sv"
    `include "sequences/debug_single_write_sequence.sv"
    `include "sequences/error_injection_sequence.sv" 
    `include "sequences/performance_test_sequence.sv"
    `include "sequences/uart_protocol_active_sequence.sv"
    `include "sequences/uart_axi4_frame_builder_sequence.sv"
    `include "sequences/uart_axi4_register_block_sequence.sv"
    `include "sequences/uart_axi4_read_protocol_sequence.sv"  // Read protocol verification
    `include "sequences/register_sequences.sv"
    // NOTE: test_register_sequences.sv commented out due to identifier conflict
    // `include "sequences/test_register_sequences.sv"  // Test register sequences  
    `include "sequences/coverage_sequences.sv"
    `include "sequences/flow_control_sequences.sv"       // RTS/CTS flow control sequences
    
    // Test files
    `include "tests/uart_axi4_base_test.sv"
    `include "tests/axiuart_system_test.sv"
    `include "tests/uart_axi4_minimal_test.sv"
    `include "tests/uart_axi4_basic_test.sv"
    `include "tests/uart_axi4_multi_beat_write_test.sv"
    `include "tests/register_block_tests.sv"
    // `include "tests/extended_basic_test.sv"  // Temporarily disabled - field definition issues
    `include "tests/uart_coverage_debug_test.sv"
    `include "tests/uart_axi4_optimized_coverage_test.sv"
    `include "tests/uart_axi4_register_block_test.sv"
    `include "tests/uart_axi4_read_protocol_test.sv"         // Read protocol verification test
    `include "tests/uart_flow_control_tests.sv"         // RTS/CTS flow control tests
    
    // `include "tests/axiuart_register_toggle_test.sv"  // Temporarily disabled - field definition issues  
    // `include "tests/simple_register_sweep_test.sv"    // Temporarily disabled - field definition issues
    // `include "tests/axiuart_coverage_tests.sv" // Temporarily disabled due to compilation issues
    
    // Coverage enhancement sequences and tests
    // `include "../sequences/axiuart_register_sweep_sequence.sv" // Included in axiuart_register_toggle_test
    // `include "../tests/axiuart_coverage_tests.sv"  // Disabled - external package dependencies
    
    // Debug tests excluded - cause timeouts and provide redundant functionality:
    // `include "tests/uart_axi4_active_test.sv"           - replaced by basic_test
    // `include "tests/uart_frame_parser_debug_test.sv"    - debug-only, no validation
    // `include "tests/uart_axi4_frame_builder_test.sv"    - debug-only, no validation
    
    // Simple register test sequence
    `include "sequences/uart_axi4_register_simple_sequence.sv"

endpackage