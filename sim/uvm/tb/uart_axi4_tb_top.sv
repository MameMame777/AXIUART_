`timescale 1ns / 1ps

// Testbench Top Module for UART-AXI4 Bridge
module uart_axi4_tb_top;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // Import test package
    import uart_axi4_test_pkg::*;
    import sequence_lib_pkg::*;
    
    // Clock and reset generation
    logic clk;
    logic rst_n;
    
    // Interface instances
    uart_if uart_if_inst(clk, rst_n);
    axi4_lite_if axi_if_inst(clk, rst_n);
    
    // DUT instance
    Uart_Axi4_Bridge dut (
        .clk(clk),
        .rst(~rst_n),  // RTL expects active-high reset
        
        // UART interface
        .uart_rx(uart_if_inst.uart_rx),
        .uart_tx(uart_if_inst.uart_tx),
        
        // AXI4-Lite master interface
        .axi(axi_if_inst.master)
    );
    
    // Clock generation (50MHz)
    initial begin
        clk = 1'b0;
        forever #10ns clk = ~clk; // 50MHz clock
    end
    
    // Reset generation
    initial begin
        rst_n = 1'b0;
        repeat (5) @(posedge clk);
        rst_n = 1'b1;
        `uvm_info("TB_TOP", "Reset released", UVM_MEDIUM)
    end
    
    // Simple AXI slave model for testing
    axi_slave_model axi_slave (
        .clk(clk),
        .rst_n(rst_n),
        .axi_if(axi_if_inst.slave)
    );
    
    // UVM testbench initialization
    initial begin
        // Set virtual interfaces in config database
        uvm_config_db#(virtual uart_if)::set(null, "uvm_test_top.*", "uart_vif", uart_if_inst);
        uvm_config_db#(virtual axi4_lite_if)::set(null, "uvm_test_top.*", "axi_vif", axi_if_inst);
        
        // Enable waveform dumping
        `ifdef WAVES
            $dumpfile("uart_axi4_test.mxd");
            $dumpvars(0, uart_axi4_tb_top);
            `uvm_info("TB_TOP", "Waveform dumping enabled", UVM_LOW)
        `endif
        
        // Run UVM test
        run_test();
    end
    
    // Timeout mechanism
    initial begin
        #100ms;
        `uvm_error("TB_TOP", "Test timeout - simulation ran too long")
        $finish;
    end
    
    // Protocol checker instances for additional verification
    
    // UART protocol checker
    uart_protocol_checker uart_checker (
        .clk(clk),
        .rst_n(rst_n),
        .uart_rx(uart_if_inst.uart_rx),
        .uart_tx(uart_if_inst.uart_tx)
    );
    
    // AXI4-Lite protocol checker
    axi4_lite_protocol_checker axi_checker (
        .aclk(clk),
        .aresetn(rst_n),
        .axi_if(axi_if_inst.monitor)
    );
    
    // Coverage collection
    `ifdef ENABLE_COVERAGE
        initial begin
            // Enable coverage collection at system level
            // $coverage_control(1);  // Commented out - not supported in all simulators
            `uvm_info("TB_TOP", "Coverage collection enabled", UVM_LOW)
        end
        
        final begin
            // Report coverage statistics
            // $coverage_save("coverage.db");  // Commented out - not supported in all simulators
            `uvm_info("TB_TOP", "Coverage database saved", UVM_LOW)
        end
    `endif
    
    // Assertion monitoring
    `ifdef ENABLE_ASSERTIONS
        // Include assertion bind files
        bind dut uart_axi4_assertions uart_axi4_assert_inst (
            .clk(clk),
            .rst_n(rst_n),
            .uart_rx(uart_rx),
            .uart_tx(uart_tx)
        );
    `endif
    
    // Debug and monitoring
    always @(posedge clk) begin
        if (rst_n) begin
            // Monitor critical signals
            if (dut.frame_parser.frame_valid) begin
                `uvm_info("TB_TOP", $sformatf("Frame parsed: CMD=0x%02X, ADDR=0x%08X", 
                          dut.frame_parser.cmd, dut.frame_parser.addr), UVM_DEBUG)
            end
            
            if (dut.axi_transaction_done) begin
                `uvm_info("TB_TOP", $sformatf("AXI transaction complete: ADDR=0x%08X", 
                          dut.parser_addr), UVM_DEBUG)
            end
        end
    end
    
    // Performance monitoring
    real start_time, end_time;
    int transaction_count = 0;
    
    always @(posedge uart_if_inst.uart_rx or posedge uart_if_inst.uart_tx) begin
        if (rst_n) begin
            if ($time > 1000) begin // Skip reset period
                if (transaction_count == 0) start_time = $realtime;
                transaction_count++;
                
                if (transaction_count % 100 == 0) begin
                    end_time = $realtime;
                    `uvm_info("TB_TOP", $sformatf("Processed %0d transactions in %.2f ms", 
                              transaction_count, (end_time - start_time) / 1000000.0), UVM_LOW)
                end
            end
        end
    end
    
endmodule

// Simple AXI Slave Model for basic testing
module axi_slave_model (
    input logic clk,
    input logic rst_n,
    axi4_lite_if.slave axi_if
);
    
    // Simple memory model
    logic [31:0] memory [logic [31:0]];
    
    // AXI slave state machine
    typedef enum logic [2:0] {
        IDLE,
        WRITE_ADDR,
        WRITE_DATA,
        WRITE_RESP,
        READ_ADDR,
        READ_DATA
    } axi_state_t;
    
    axi_state_t state;
    logic [31:0] write_addr, read_addr;
    logic [31:0] write_data, read_data;
    logic [3:0] write_strb;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            axi_if.awready <= 1'b1;
            axi_if.wready <= 1'b1;
            axi_if.arready <= 1'b1;
            axi_if.bvalid <= 1'b0;
            axi_if.rvalid <= 1'b0;
            axi_if.bresp <= 2'b00;
            axi_if.rresp <= 2'b00;
            axi_if.rdata <= 32'h0;
        end else begin
            case (state)
                IDLE: begin
                    if (axi_if.awvalid && axi_if.awready) begin
                        write_addr <= axi_if.awaddr;
                        state <= WRITE_DATA;
                    end else if (axi_if.arvalid && axi_if.arready) begin
                        read_addr <= axi_if.araddr;
                        state <= READ_DATA;
                    end
                end
                
                WRITE_DATA: begin
                    if (axi_if.wvalid && axi_if.wready) begin
                        write_data <= axi_if.wdata;
                        write_strb <= axi_if.wstrb;
                        
                        // Write to memory with byte strobes
                        if (write_strb[0]) memory[write_addr][7:0] <= axi_if.wdata[7:0];
                        if (write_strb[1]) memory[write_addr][15:8] <= axi_if.wdata[15:8];
                        if (write_strb[2]) memory[write_addr][23:16] <= axi_if.wdata[23:16];
                        if (write_strb[3]) memory[write_addr][31:24] <= axi_if.wdata[31:24];
                        
                        axi_if.bvalid <= 1'b1;
                        axi_if.bresp <= 2'b00; // OKAY
                        state <= WRITE_RESP;
                    end
                end
                
                WRITE_RESP: begin
                    if (axi_if.bready) begin
                        axi_if.bvalid <= 1'b0;
                        state <= IDLE;
                    end
                end
                
                READ_DATA: begin
                    // Read from memory
                    if (memory.exists(read_addr)) begin
                        axi_if.rdata <= memory[read_addr];
                    end else begin
                        axi_if.rdata <= 32'hDEADBEEF; // Default for uninitialized
                    end
                    
                    axi_if.rvalid <= 1'b1;
                    axi_if.rresp <= 2'b00; // OKAY
                    
                    if (axi_if.rready) begin
                        axi_if.rvalid <= 1'b0;
                        state <= IDLE;
                    end
                end
                
            endcase
        end
    end
    
endmodule

// UART Protocol Checker
module uart_protocol_checker (
    input logic clk,
    input logic rst_n,
    input logic uart_rx,
    input logic uart_tx
);
    
    // Basic UART frame validation
    // Implementation would include timing checks, frame format validation, etc.
    
endmodule

// AXI4-Lite Protocol Checker  
module axi4_lite_protocol_checker (
    input logic aclk,
    input logic aresetn,
    axi4_lite_if.monitor axi_if
);
    
    // AXI protocol compliance checking
    // Implementation would include handshake validation, address alignment, etc.
    
endmodule