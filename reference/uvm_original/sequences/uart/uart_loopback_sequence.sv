// UART Loopback Test Sequence
// Target Board: Zybo Z7-20
// Date: July 26, 2025
// Description: UART loopback functionality test

`ifndef UART_LOOPBACK_SEQUENCE_SV
`define UART_LOOPBACK_SEQUENCE_SV

class uart_loopback_sequence extends axi4_lite_base_sequence;
    
    // Test data patterns
    bit [7:0] test_patterns[] = {
        8'h00, 8'h55, 8'hAA, 8'hFF,
        8'h0F, 8'hF0, 8'h33, 8'hCC,
        8'h41, 8'h42, 8'h43  // 'A', 'B', 'C'
    };
    
    // UVM registration
    `uvm_object_utils(uart_loopback_sequence)
    
    // Constructor
    function new(string name = "uart_loopback_sequence");
        super.new(name);
    endfunction
    
    // Main sequence body
    virtual task body();
        bit [31:0] rdata;
        bit [1:0] resp;
        bit [7:0] expected_data;
        int timeout_count;
        
        `uvm_info("UART_LOOP", "Starting UART loopback test", UVM_LOW)
        
        // Step 1: Initialize UART
        setup_uart();
        
        // Step 2: Enable loopback mode (if supported)
        read_modify_write(ADDR_CONTROL_REG, 32'h00000010, 32'h00000010); // Set loopback bit
        
        // Step 3: Test each pattern
        foreach (test_patterns[i]) begin
            expected_data = test_patterns[i];
            `uvm_info("UART_LOOP", $sformatf("Testing pattern %0d: 0x%02h", i, expected_data), UVM_MEDIUM)
            
            // Send data
            write_register(ADDR_TX_DATA_REG, {24'h000000, expected_data});
            
            // Wait for transmission
            wait_for_tx_complete();
            
            // Wait for receive
            if (wait_for_rx_data(expected_data)) begin
                `uvm_info("UART_LOOP", $sformatf("Pattern 0x%02h loopback successful", expected_data), UVM_MEDIUM)
            end else begin
                `uvm_error("UART_LOOP", $sformatf("Pattern 0x%02h loopback failed", expected_data))
            end
            
            #1us; // Inter-pattern delay
        end
        
        // Step 4: Test burst transmission
        test_burst_loopback();
        
        // Step 5: Disable loopback
        read_modify_write(ADDR_CONTROL_REG, 32'h00000010, 32'h00000000); // Clear loopback bit
        
        // Step 6: Final error check
        read_register(ADDR_ERROR_STATUS, rdata, resp);
        if (resp == AXI_RESP_OKAY && rdata != 0) begin
            `uvm_warning("UART_LOOP", $sformatf("Errors detected: 0x%08h", rdata))
        end
        
        `uvm_info("UART_LOOP", "UART loopback test completed", UVM_LOW)
    endtask
    
    // Setup UART for loopback test
    task setup_uart();
        `uvm_info("UART_LOOP", "Configuring UART for loopback", UVM_MEDIUM)
        
        // Enable UART
        write_register(ADDR_CONTROL_REG, 32'h00000001);
        
        // Set FIFO thresholds
        write_register(ADDR_FIFO_THRESH, 32'h00010001); // Low thresholds for quick response
        
        // Clear any existing errors
        write_register(ADDR_ERROR_STATUS, 32'hFFFFFFFF); // Clear all error bits
        
        #100ns; // Allow configuration to settle
    endtask
    
    // Wait for TX completion
    task wait_for_tx_complete();
        bit [31:0] status;
        bit [1:0] resp;
        int timeout = 0;
        
        do begin
            #100ns;
            read_register(ADDR_FIFO_STATUS, status, resp);
            timeout++;
            if (timeout > 1000) begin
                `uvm_error("UART_LOOP", "TX completion timeout")
                return;
            end
        end while (resp == AXI_RESP_OKAY && status[8] == 1'b0); // Wait for TX FIFO empty
        
        `uvm_info("UART_LOOP", "TX completed", UVM_HIGH)
    endtask
    
    // Wait for RX data and verify
    function bit wait_for_rx_data(bit [7:0] expected);
        bit [31:0] status, rx_data;
        bit [1:0] resp;
        int timeout = 0;
        
        // Wait for RX data available
        do begin
            #100ns;
            read_register(ADDR_FIFO_STATUS, status, resp);
            timeout++;
            if (timeout > 1000) begin
                `uvm_error("UART_LOOP", "RX data timeout")
                return 0;
            end
        end while (resp == AXI_RESP_OKAY && status[0] == 1'b1); // Wait for RX FIFO not empty
        
        // Read received data
        read_register(ADDR_RX_DATA_REG, rx_data, resp);
        
        if (resp != AXI_RESP_OKAY) begin
            `uvm_error("UART_LOOP", "Failed to read RX data")
            return 0;
        end
        
        if (rx_data[7:0] == expected) begin
            `uvm_info("UART_LOOP", $sformatf("RX data match: expected=0x%02h, received=0x%02h", 
                     expected, rx_data[7:0]), UVM_HIGH)
            return 1;
        end else begin
            `uvm_error("UART_LOOP", $sformatf("RX data mismatch: expected=0x%02h, received=0x%02h", 
                      expected, rx_data[7:0]))
            return 0;
        end
    endfunction
    
    // Test burst loopback
    task test_burst_loopback();
        bit [7:0] burst_data[] = {'H', 'e', 'l', 'l', 'o', ' ', 'W', 'o', 'r', 'l', 'd', '!'};
        bit [31:0] rx_data;
        bit [1:0] resp;
        
        `uvm_info("UART_LOOP", "Starting burst loopback test", UVM_MEDIUM)
        
        // Send burst data
        foreach (burst_data[i]) begin
            write_register(ADDR_TX_DATA_REG, {24'h000000, burst_data[i]});
            #50ns; // Small delay between writes
        end
        
        // Wait for all transmissions
        wait_for_tx_complete();
        
        // Receive and verify burst data
        foreach (burst_data[i]) begin
            if (wait_for_rx_data(burst_data[i])) begin
                `uvm_info("UART_LOOP", $sformatf("Burst byte %0d ('%c') OK", i, burst_data[i]), UVM_HIGH)
            end else begin
                `uvm_error("UART_LOOP", $sformatf("Burst byte %0d ('%c') failed", i, burst_data[i]))
            end
        end
        
        `uvm_info("UART_LOOP", "Burst loopback test completed", UVM_MEDIUM)
    endtask

endclass

`endif // UART_LOOPBACK_SEQUENCE_SV
