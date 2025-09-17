// Basic Functionality Test Sequence
// Target Board: Zybo Z7-20
// Date: July 26, 2025
// Description: Basic register access and UART communication test

`ifndef BASIC_FUNC_SEQUENCE_SV
`define BASIC_FUNC_SEQUENCE_SV

class basic_func_sequence extends axi4_lite_base_sequence;
    
    // UVM registration
    `uvm_object_utils(basic_func_sequence)
    
    // Constructor
    function new(string name = "basic_func_sequence");
        super.new(name);
    endfunction
    
    // Main sequence body
    virtual task body();
        bit [31:0] rdata;
        bit [1:0] resp;
        
        `uvm_info("BASIC_FUNC", "Starting basic functionality test", UVM_LOW)
        
        // Step 1: Reset and initialize
        #100ns;
        
        // Step 2: Read initial status register
        read_register(ADDR_STATUS_REG, rdata, resp);
        if (resp != AXI_RESP_OKAY) begin
            `uvm_error("BASIC_FUNC", "Failed to read status register")
        end
        `uvm_info("BASIC_FUNC", $sformatf("Initial status: 0x%08h", rdata), UVM_LOW)
        
        // Step 3: Read FIFO status
        read_register(ADDR_FIFO_STATUS, rdata, resp);
        if (resp == AXI_RESP_OKAY) begin
            `uvm_info("BASIC_FUNC", $sformatf("FIFO status: TX_empty=%b, RX_empty=%b", 
                     rdata[8], rdata[0]), UVM_LOW)
        end
        
        // Step 4: Configure control register
        write_register(ADDR_CONTROL_REG, 32'h00000001); // Enable UART
        
        // Step 5: Verify control register
        read_register(ADDR_CONTROL_REG, rdata, resp);
        if (resp == AXI_RESP_OKAY && rdata[0] == 1'b1) begin
            `uvm_info("BASIC_FUNC", "UART enabled successfully", UVM_LOW)
        end else begin
            `uvm_error("BASIC_FUNC", "Failed to enable UART")
        end
        
        // Step 6: Test TX data register
        write_register(ADDR_TX_DATA_REG, 32'h00000041); // Send 'A'
        
        // Step 7: Wait and check TX status
        #1us;
        read_register(ADDR_FIFO_STATUS, rdata, resp);
        if (resp == AXI_RESP_OKAY) begin
            `uvm_info("BASIC_FUNC", $sformatf("After TX: FIFO status=0x%08h", rdata), UVM_LOW)
        end
        
        // Step 8: Configure FIFO thresholds
        write_register(ADDR_FIFO_THRESH, 32'h00080004); // TX thresh=8, RX thresh=4
        
        // Step 9: Verify threshold configuration
        read_register(ADDR_FIFO_THRESH, rdata, resp);
        if (resp == AXI_RESP_OKAY) begin
            `uvm_info("BASIC_FUNC", $sformatf("FIFO thresholds: TX=%0d, RX=%0d", 
                     rdata[23:16], rdata[7:0]), UVM_LOW)
        end
        
        // Step 10: Test multiple data writes
        for (int i = 0; i < 5; i++) begin
            write_register(ADDR_TX_DATA_REG, 32'h00000030 + i); // Send '0' to '4'
            #100ns;
        end
        
        // Step 11: Final status check
        read_register(ADDR_STATUS_REG, rdata, resp);
        `uvm_info("BASIC_FUNC", $sformatf("Final status: 0x%08h", rdata), UVM_LOW)
        
        read_register(ADDR_ERROR_STATUS, rdata, resp);
        if (resp == AXI_RESP_OKAY) begin
            `uvm_info("BASIC_FUNC", $sformatf("Error status: 0x%08h", rdata), UVM_LOW)
            if (rdata != 0) begin
                `uvm_warning("BASIC_FUNC", "Errors detected in basic test")
            end
        end
        
        `uvm_info("BASIC_FUNC", "Basic functionality test completed", UVM_LOW)
    endtask

endclass

`endif // BASIC_FUNC_SEQUENCE_SV
