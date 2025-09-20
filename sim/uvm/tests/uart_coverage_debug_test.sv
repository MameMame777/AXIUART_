`timescale 1ns / 1ps

class uart_coverage_debug_test extends uart_axi4_base_test;
    `uvm_component_utils(uart_coverage_debug_test)
    
    function new(string name = "uart_coverage_debug_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        // Enable debug logging for coverage
        set_report_verbosity_level(UVM_DEBUG);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        `uvm_info("DEBUG_TEST", "=== Starting Coverage Debug Test ===", UVM_LOW)
        
        // Wait for reset
        #100000;
        
        `uvm_info("DEBUG_TEST", "Starting manual UART frame generation", UVM_LOW)
        
        // Manually generate some UART activity to trigger coverage
        fork
            begin
                // Generate a simple write transaction
                generate_uart_write_frame(32'h00001000, 8'h42);
                #50000;
                
                // Generate a read transaction
                generate_uart_read_frame(32'h00001000);
                #50000;
                
                // Generate an alignment error
                generate_uart_write_frame(32'h00001001, 8'hAA); // Misaligned address
                #50000;
            end
        join
        
        `uvm_info("DEBUG_TEST", "=== Coverage Debug Test Completed ===", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
    // Helper task to generate UART write frame
    virtual task generate_uart_write_frame(bit [31:0] addr, bit [7:0] data);
        bit [7:0] frame_bytes[$];
        bit [7:0] crc;
        
        `uvm_info("DEBUG_TEST", $sformatf("Generating UART write: ADDR=0x%08X, DATA=0x%02X", addr, data), UVM_LOW)
        
        // Build frame: SOF + CMD + SIZE + ADDR + DATA + CRC
        frame_bytes.push_back(8'hAA); // SOF_HOST_TO_DEVICE
        frame_bytes.push_back(8'h01); // Write command
        frame_bytes.push_back(8'h01); // Size = 1 byte
        
        // Address (little-endian)
        frame_bytes.push_back(addr[7:0]);
        frame_bytes.push_back(addr[15:8]);
        frame_bytes.push_back(addr[23:16]);
        frame_bytes.push_back(addr[31:24]);
        
        // Data
        frame_bytes.push_back(data);
        
        // Calculate CRC
        crc = calculate_simple_crc(frame_bytes);
        frame_bytes.push_back(crc);
        
        // Send frame over UART
        send_uart_frame(frame_bytes);
    endtask
    
    // Helper task to generate UART read frame
    virtual task generate_uart_read_frame(bit [31:0] addr);
        bit [7:0] frame_bytes[$];
        bit [7:0] crc;
        
        `uvm_info("DEBUG_TEST", $sformatf("Generating UART read: ADDR=0x%08X", addr), UVM_LOW)
        
        // Build frame: SOF + CMD + SIZE + ADDR + CRC
        frame_bytes.push_back(8'hAA); // SOF_HOST_TO_DEVICE
        frame_bytes.push_back(8'h00); // Read command
        frame_bytes.push_back(8'h01); // Size = 1 byte
        
        // Address (little-endian)
        frame_bytes.push_back(addr[7:0]);
        frame_bytes.push_back(addr[15:8]);
        frame_bytes.push_back(addr[23:16]);
        frame_bytes.push_back(addr[31:24]);
        
        // Calculate CRC
        crc = calculate_simple_crc(frame_bytes);
        frame_bytes.push_back(crc);
        
        // Send frame over UART
        send_uart_frame(frame_bytes);
    endtask
    
    // Simple CRC calculation (placeholder)
    function bit [7:0] calculate_simple_crc(bit [7:0] data_bytes[$]);
        bit [7:0] crc = 8'h00;
        foreach(data_bytes[i]) begin
            crc = crc ^ data_bytes[i];
        end
        return crc;
    endfunction
    
    // Send UART frame by driving uart_rx directly
    virtual task send_uart_frame(bit [7:0] frame_bytes[$]);
        `uvm_info("DEBUG_TEST", $sformatf("Sending UART frame with %0d bytes", frame_bytes.size()), UVM_LOW)
        
        foreach(frame_bytes[i]) begin
            send_uart_byte(frame_bytes[i]);
            #10000; // Inter-byte delay
        end
    endtask
    
    // Send single UART byte (start bit, 8 data bits, stop bit)
    virtual task send_uart_byte(bit [7:0] data);
        int bit_time_ns = 8680; // Bit time for 115200 baud
        
        // Start bit
        force uart_axi4_tb_top.uart_if_inst.uart_rx = 1'b0;
        #bit_time_ns;
        
        // Data bits (LSB first)
        for(int i = 0; i < 8; i++) begin
            force uart_axi4_tb_top.uart_if_inst.uart_rx = data[i];
            #bit_time_ns;
        end
        
        // Stop bit
        force uart_axi4_tb_top.uart_if_inst.uart_rx = 1'b1;
        #bit_time_ns;
        
        // Release force
        release uart_axi4_tb_top.uart_if_inst.uart_rx;
        #bit_time_ns;
    endtask

endclass