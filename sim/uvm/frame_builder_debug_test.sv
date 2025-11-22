`timescale 1ns / 1ps

module frame_builder_debug_test;

    // Clock and Reset
    logic clk;
    logic reset;
    
    // Frame_Builder Input Signals
    logic [7:0] cmd;
    logic [31:0] addr;
    logic [31:0] data;
    logic [7:0] error_status;
    logic start_frame;
    
    // Frame_Builder Output Signals (to TX FIFO)
    logic [7:0] tx_fifo_data;
    logic tx_fifo_write;
    logic tx_fifo_full;
    
    // Internal state monitoring
    logic [2:0] current_state;
    logic [7:0] calculated_crc;
    
    // Frame_Builder Instantiation
    Frame_Builder dut (
        .clk(clk),
        .reset(reset),
        .cmd(cmd),
        .addr(addr),
        .data(data),
        .error_status(error_status),
        .start_frame(start_frame),
        .tx_fifo_data(tx_fifo_data),
        .tx_fifo_write(tx_fifo_write),
        .tx_fifo_full(tx_fifo_full)
    );
    
    // Access internal signals for debugging
    assign current_state = dut.current_state;
    assign calculated_crc = dut.calculated_crc;
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5ns clk = ~clk; // 100MHz clock
    end
    
    // Test sequence
    initial begin
        $display("=== Frame_Builder Debug Test ===");
        
        // Initialize
        reset = 1;
        cmd = 8'h00;
        addr = 32'h00000000;
        data = 32'h00000000;
        error_status = 8'h00;
        start_frame = 0;
        tx_fifo_full = 0;
        
        // Reset
        repeat(10) @(posedge clk);
        reset = 0;
        repeat(2) @(posedge clk);
        
        // Test 1: Read Response Frame (0xa1 command)
        $display("Test 1: Read Response Frame");
        cmd = 8'ha1;
        addr = 32'h12345678;
        data = 32'hdeadbeef;
        error_status = 8'h00;
        start_frame = 1;
        
        @(posedge clk);
        start_frame = 0;
        
        // Monitor frame building process
        repeat(50) begin
            @(posedge clk);
            if (tx_fifo_write) begin
                $display("Time %0t: TX FIFO Write - Data: 0x%02x, State: %0d", 
                         $time, tx_fifo_data, current_state);
            end
        end
        
        repeat(10) @(posedge clk);
        
        // Test 2: Write Response Frame (0xa2 command)
        $display("\nTest 2: Write Response Frame");
        cmd = 8'ha2;
        addr = 32'h87654321;
        data = 32'h12345678;
        error_status = 8'h00;
        start_frame = 1;
        
        @(posedge clk);
        start_frame = 0;
        
        // Monitor frame building process
        repeat(50) begin
            @(posedge clk);
            if (tx_fifo_write) begin
                $display("Time %0t: TX FIFO Write - Data: 0x%02x, State: %0d", 
                         $time, tx_fifo_data, current_state);
            end
        end
        
        repeat(10) @(posedge clk);
        
        // Test 3: Error Response Frame (0xae command)
        $display("\nTest 3: Error Response Frame");
        cmd = 8'hae;
        addr = 32'h00000000;
        data = 32'h00000000;
        error_status = 8'h01; // Error code
        start_frame = 1;
        
        @(posedge clk);
        start_frame = 0;
        
        // Monitor frame building process
        repeat(50) begin
            @(posedge clk);
            if (tx_fifo_write) begin
                $display("Time %0t: TX FIFO Write - Data: 0x%02x, State: %0d", 
                         $time, tx_fifo_data, current_state);
            end
        end
        
        repeat(10) @(posedge clk);
        
        // Test 4: FIFO Full Condition
        $display("\nTest 4: FIFO Full Condition");
        tx_fifo_full = 1;  // Simulate full FIFO
        cmd = 8'ha1;
        addr = 32'haaaaaaaa;
        data = 32'hbbbbbbbb;
        error_status = 8'h00;
        start_frame = 1;
        
        @(posedge clk);
        start_frame = 0;
        
        // Monitor - should not write when FIFO is full
        repeat(20) begin
            @(posedge clk);
            if (tx_fifo_write) begin
                $display("ERROR: TX FIFO Write when FIFO is full!");
            end
        end
        
        tx_fifo_full = 0; // Release FIFO
        repeat(30) begin
            @(posedge clk);
            if (tx_fifo_write) begin
                $display("Time %0t: TX FIFO Write - Data: 0x%02x, State: %0d", 
                         $time, tx_fifo_data, current_state);
            end
        end
        
        repeat(10) @(posedge clk);
        $display("=== Frame_Builder Debug Test Complete ===");
        $finish;
    end
    
    // Comprehensive monitoring
    always @(posedge clk) begin
        if (start_frame) begin
            $display("Time %0t: Frame building started - CMD: 0x%02x, ADDR: 0x%08x, DATA: 0x%08x, ERROR: 0x%02x", 
                     $time, cmd, addr, data, error_status);
        end
    end

endmodule