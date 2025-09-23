`timescale 1ns / 1ps

// Comprehensive error injection sequences for coverage improvement
// Systematically tests all error handling paths in AXIUART subsystem

package axiuart_error_sequences_pkg;
    import uvm_pkg::*;
    import uart_axi4_test_pkg::*;
    `include "uvm_macros.svh"
    
    // Base error injection sequence with common functionality  
    virtual class axiuart_error_base_sequence extends uvm_sequence#(uart_frame_transaction);
        
        // Error injection controls
        rand int error_injection_rate = 25; // 25% chance of error per transaction
        rand int recovery_delay_cycles = 100; // Cycles to wait after error
        
        constraint error_rate_c {
            error_injection_rate inside {[10:50]}; // Reasonable error rates
            recovery_delay_cycles inside {[50:200]};
        }
        
        function new(string name = "axiuart_error_base_sequence");
            super.new(name);
        endfunction
        
        // Helper task to inject random delay after error
        virtual task post_error_recovery();
            #(recovery_delay_cycles * 1ns);
        endtask
        
    endclass
    
    // Sequence 1: UART Protocol Error Injection
    class axiuart_uart_error_injection_sequence extends axiuart_error_base_sequence;
        `uvm_object_utils(axiuart_uart_error_injection_sequence)
        
        function new(string name = "axiuart_uart_error_injection_sequence");
            super.new(name);
        endfunction
        
        virtual task body();
            uart_frame_transaction req;
            
            `uvm_info(get_type_name(), "Starting UART error injection sequence", UVM_MEDIUM)
            
            // Phase 1: Parity Error Injection
            inject_parity_errors();
            
            // Phase 2: Framing Error Injection  
            inject_framing_errors();
            
            // Phase 3: Start/Stop Bit Errors
            inject_timing_errors();
            
            // Phase 4: Timeout Conditions
            inject_timeout_errors();
            
            `uvm_info(get_type_name(), "UART error injection sequence completed", UVM_MEDIUM)
        endtask
        
        virtual task inject_parity_errors();
            `uvm_info(get_type_name(), "Injecting parity errors", UVM_MEDIUM)
            
            repeat (10) begin
                uart_transaction req;
                req = uart_transaction::type_id::create("req");
                start_item(req);
                
                // Configure normal transaction but force parity error
                if (!req.randomize() with {
                    length inside {[1:32]};
                    crc_enable == 1'b1; // Enable CRC to test interaction
                }) begin
                    `uvm_error(get_type_name(), "Failed to randomize UART transaction")
                end
                
                // Inject parity error
                if ($urandom_range(1, 100) <= error_injection_rate) begin
                    req.force_parity_error = 1'b1;
                    `uvm_info(get_type_name(), "Injecting parity error", UVM_HIGH)
                end
                
                finish_item(req);
                post_error_recovery();
            end
        endtask
        
        virtual task inject_framing_errors();
            `uvm_info(get_type_name(), "Injecting framing errors", UVM_MEDIUM)
            
            repeat (8) begin
                uart_transaction req;
                req = uart_transaction::type_id::create("req");
                start_item(req);
                
                if (!req.randomize() with {
                    length inside {[1:64]};
                }) begin
                    `uvm_error(get_type_name(), "Failed to randomize UART transaction")
                end
                
                // Inject framing error (missing/corrupted stop bit)
                if ($urandom_range(1, 100) <= error_injection_rate) begin
                    req.force_framing_error = 1'b1;
                    `uvm_info(get_type_name(), "Injecting framing error", UVM_HIGH)
                end
                
                finish_item(req);
                post_error_recovery();
            end
        endtask
        
        virtual task inject_timing_errors();
            `uvm_info(get_type_name(), "Injecting timing errors", UVM_MEDIUM)
            
            repeat (6) begin
                uart_transaction req = uart_transaction::type_id::create("req");
                start_item(req);
                
                if (!req.randomize() with {
                    length inside {[1:16]};
                }) begin
                    `uvm_error(get_type_name(), "Failed to randomize UART transaction")
                end
                
                // Inject start bit timing error
                if ($urandom_range(1, 100) <= error_injection_rate) begin
                    req.force_start_bit_error = 1'b1;
                    `uvm_info(get_type_name(), "Injecting start bit timing error", UVM_HIGH)
                end
                
                finish_item(req);
                post_error_recovery();
            end
        endtask
        
        virtual task inject_timeout_errors();
            `uvm_info(get_type_name(), "Injecting timeout errors", UVM_MEDIUM)
            
            repeat (5) begin
                uart_transaction req = uart_transaction::type_id::create("req");
                start_item(req);
                
                if (!req.randomize() with {
                    length inside {[8:128]};
                }) begin
                    `uvm_error(get_type_name(), "Failed to randomize UART transaction")
                end
                
                // Force timeout by interrupting transmission mid-frame
                if ($urandom_range(1, 100) <= error_injection_rate) begin
                    req.force_timeout_error = 1'b1;
                    req.timeout_position = $urandom_range(1, req.length-1);
                    `uvm_info(get_type_name(), 
                        $sformatf("Injecting timeout at byte %0d", req.timeout_position), UVM_HIGH)
                end
                
                finish_item(req);
                post_error_recovery();
            end
        endtask
        
    endclass
    
    // Sequence 2: CRC Fault Injection
    class axiuart_crc_fault_sequence extends axiuart_error_base_sequence;
        `uvm_object_utils(axiuart_crc_fault_sequence)
        
        function new(string name = "axiuart_crc_fault_sequence");
            super.new(name);
        endfunction
        
        virtual task body();
            `uvm_info(get_type_name(), "Starting CRC fault injection sequence", UVM_MEDIUM)
            
            // Phase 1: CRC Mismatch Injection
            inject_crc_mismatches();
            
            // Phase 2: CRC Enable/Disable Mid-Frame
            inject_crc_state_changes();
            
            // Phase 3: CRC Calculation Timing Issues
            inject_crc_timing_faults();
            
            `uvm_info(get_type_name(), "CRC fault injection sequence completed", UVM_MEDIUM)
        endtask
        
        virtual task inject_crc_mismatches();
            `uvm_info(get_type_name(), "Injecting CRC mismatches", UVM_MEDIUM)
            
            repeat (15) begin
                uart_transaction req = uart_transaction::type_id::create("req");
                start_item(req);
                
                if (!req.randomize() with {
                    crc_enable == 1'b1; // Force CRC enabled
                    length inside {[4:255]}; // Various frame lengths
                }) begin
                    `uvm_error(get_type_name(), "Failed to randomize CRC transaction")
                end
                
                // Inject CRC mismatch
                if ($urandom_range(1, 100) <= error_injection_rate) begin
                    req.force_crc_error = 1'b1;
                    req.crc_error_type = $urandom_range(1, 3); // 1=1bit flip, 2=multi-bit, 3=wrong poly
                    `uvm_info(get_type_name(), 
                        $sformatf("Injecting CRC error type %0d", req.crc_error_type), UVM_HIGH)
                end
                
                finish_item(req);
                post_error_recovery();
            end
        endtask
        
        virtual task inject_crc_state_changes();
            `uvm_info(get_type_name(), "Injecting CRC state changes", UVM_MEDIUM)
            
            repeat (8) begin
                uart_transaction req = uart_transaction::type_id::create("req");
                start_item(req);
                
                if (!req.randomize() with {
                    length inside {[16:128]}; // Long enough for mid-frame change
                }) begin
                    `uvm_error(get_type_name(), "Failed to randomize CRC state transaction")
                end
                
                // Force CRC enable change during frame processing
                if ($urandom_range(1, 100) <= error_injection_rate) begin
                    req.force_crc_state_change = 1'b1;
                    req.crc_change_position = $urandom_range(2, req.length-2);
                    `uvm_info(get_type_name(), 
                        $sformatf("CRC state change at position %0d", req.crc_change_position), UVM_HIGH)
                end
                
                finish_item(req);
                post_error_recovery();
            end
        endtask
        
        virtual task inject_crc_timing_faults();
            `uvm_info(get_type_name(), "Injecting CRC timing faults", UVM_MEDIUM)
            
            repeat (6) begin
                uart_transaction req = uart_transaction::type_id::create("req");
                start_item(req);
                
                if (!req.randomize() with {
                    crc_enable == 1'b1;
                    length inside {[1:8]}; // Short frames for timing stress
                }) begin
                    `uvm_error(get_type_name(), "Failed to randomize CRC timing transaction")
                end
                
                // Force CRC calculation delay
                if ($urandom_range(1, 100) <= error_injection_rate) begin
                    req.force_crc_delay = 1'b1;
                    req.crc_delay_cycles = $urandom_range(1, 10);
                    `uvm_info(get_type_name(), 
                        $sformatf("CRC calculation delay: %0d cycles", req.crc_delay_cycles), UVM_HIGH)
                end
                
                finish_item(req);
                post_error_recovery();
            end
        endtask
        
    endclass
    
    // Sequence 3: FIFO Boundary Violation  
    class axiuart_fifo_boundary_sequence extends axiuart_error_base_sequence;
        `uvm_object_utils(axiuart_fifo_boundary_sequence)
        
        function new(string name = "axiuart_fifo_boundary_sequence");
            super.new(name);
        endfunction
        
        virtual task body();
            `uvm_info(get_type_name(), "Starting FIFO boundary sequence", UVM_MEDIUM)
            
            // Phase 1: FIFO Overflow Tests
            inject_fifo_overflow();
            
            // Phase 2: FIFO Underflow Tests  
            inject_fifo_underflow();
            
            // Phase 3: Rapid FIFO Level Changes
            inject_fifo_rapid_changes();
            
            `uvm_info(get_type_name(), "FIFO boundary sequence completed", UVM_MEDIUM)
        endtask
        
        virtual task inject_fifo_overflow();
            `uvm_info(get_type_name(), "Testing FIFO overflow conditions", UVM_MEDIUM)
            
            // Send burst of large transactions to fill FIFO
            repeat (20) begin
                uart_transaction req = uart_transaction::type_id::create("req");
                start_item(req);
                
                if (!req.randomize() with {
                    length inside {[32:128]}; // Large transactions
                    cmd == 8'h02; // Write operations fill TX FIFO
                }) begin
                    `uvm_error(get_type_name(), "Failed to randomize FIFO overflow transaction")
                end
                
                finish_item(req);
                
                // Minimal delay to stress FIFO
                #10;
            end
            
            post_error_recovery();
        endtask
        
        virtual task inject_fifo_underflow();
            `uvm_info(get_type_name(), "Testing FIFO underflow conditions", UVM_MEDIUM)
            
            // Send burst of read operations when FIFO likely empty
            repeat (10) begin
                uart_transaction req = uart_transaction::type_id::create("req");
                start_item(req);
                
                if (!req.randomize() with {
                    length inside {[1:16]}; // Small reads
                    cmd == 8'h01; // Read operations drain RX FIFO
                }) begin
                    `uvm_error(get_type_name(), "Failed to randomize FIFO underflow transaction")
                end
                
                finish_item(req);
                #5; // Very short delay
            end
            
            post_error_recovery();
        endtask
        
        virtual task inject_fifo_rapid_changes();
            `uvm_info(get_type_name(), "Testing rapid FIFO level changes", UVM_MEDIUM)
            
            // Alternate between fills and drains rapidly
            repeat (15) begin
                uart_transaction req = uart_transaction::type_id::create("req");
                start_item(req);
                
                if (!req.randomize() with {
                    length inside {[8:32]};
                    cmd inside {8'h01, 8'h02}; // Mix reads and writes
                }) begin
                    `uvm_error(get_type_name(), "Failed to randomize FIFO rapid change transaction")
                end
                
                finish_item(req);
                
                // Vary delays to create different FIFO fill patterns
                #($urandom_range(5, 50));
            end
            
            post_error_recovery();
        endtask
        
    endclass
    
    // Sequence 4: AXI Protocol Error Injection
    class axiuart_axi_error_sequence extends axiuart_error_base_sequence;
        `uvm_object_utils(axiuart_axi_error_sequence)
        
        function new(string name = "axiuart_axi_error_sequence");
            super.new(name);
        endfunction
        
        virtual task body();
            `uvm_info(get_type_name(), "Starting AXI error injection sequence", UVM_MEDIUM)
            
            // Phase 1: AXI Address Errors
            inject_axi_address_errors();
            
            // Phase 2: AXI Protocol Violations
            inject_axi_protocol_errors();
            
            // Phase 3: AXI Timeout Conditions
            inject_axi_timeout_errors();
            
            `uvm_info(get_type_name(), "AXI error injection sequence completed", UVM_MEDIUM)
        endtask
        
        virtual task inject_axi_address_errors();
            `uvm_info(get_type_name(), "Injecting AXI address errors", UVM_MEDIUM)
            
            repeat (12) begin
                uart_transaction req = uart_transaction::type_id::create("req");
                start_item(req);
                
                if (!req.randomize() with {
                    length inside {[4:32]};
                }) begin
                    `uvm_error(get_type_name(), "Failed to randomize AXI address transaction")
                end
                
                // Force invalid AXI addresses
                if ($urandom_range(1, 100) <= error_injection_rate) begin
                    case ($urandom_range(1, 4))
                        1: req.force_unmapped_address = 1'b1;     // Unmapped address space
                        2: req.force_misaligned_address = 1'b1;   // Misaligned access
                        3: req.force_out_of_bounds_address = 1'b1; // Beyond valid range
                        4: req.force_reserved_address = 1'b1;     // Reserved register space
                    endcase
                    `uvm_info(get_type_name(), "Injecting AXI address error", UVM_HIGH)
                end
                
                finish_item(req);
                post_error_recovery();
            end
        endtask
        
        virtual task inject_axi_protocol_errors();
            `uvm_info(get_type_name(), "Injecting AXI protocol errors", UVM_MEDIUM)
            
            repeat (8) begin
                uart_transaction req = uart_transaction::type_id::create("req");
                start_item(req);
                
                if (!req.randomize()) begin
                    `uvm_error(get_type_name(), "Failed to randomize AXI protocol transaction")
                end
                
                // Force AXI protocol violations
                if ($urandom_range(1, 100) <= error_injection_rate) begin
                    case ($urandom_range(1, 3))
                        1: req.force_axi_size_error = 1'b1;       // Invalid SIZE encoding
                        2: req.force_axi_burst_error = 1'b1;      // Invalid BURST type
                        3: req.force_axi_prot_error = 1'b1;       // Invalid PROT signals
                    endcase
                    `uvm_info(get_type_name(), "Injecting AXI protocol error", UVM_HIGH)
                end
                
                finish_item(req);
                post_error_recovery();
            end
        endtask
        
        virtual task inject_axi_timeout_errors();
            `uvm_info(get_type_name(), "Injecting AXI timeout errors", UVM_MEDIUM)
            
            repeat (6) begin
                uart_transaction req = uart_transaction::type_id::create("req");
                start_item(req);
                
                if (!req.randomize() with {
                    length inside {[16:64]}; // Longer transactions for timeout
                }) begin
                    `uvm_error(get_type_name(), "Failed to randomize AXI timeout transaction")
                end
                
                // Force AXI transaction timeout
                if ($urandom_range(1, 100) <= error_injection_rate) begin
                    req.force_axi_timeout = 1'b1;
                    req.axi_timeout_phase = $urandom_range(1, 3); // 1=addr, 2=data, 3=resp
                    `uvm_info(get_type_name(), 
                        $sformatf("AXI timeout in phase %0d", req.axi_timeout_phase), UVM_HIGH)
                end
                
                finish_item(req);
                post_error_recovery();
            end
        endtask
        
    endclass
    
    // Sequence 5: Combined Multi-Layer Error Injection
    class axiuart_multi_error_sequence extends axiuart_error_base_sequence;
        `uvm_object_utils(axiuart_multi_error_sequence)
        
        function new(string name = "axiuart_multi_error_sequence");
            super.new(name);
        endfunction
        
        virtual task body();
            `uvm_info(get_type_name(), "Starting multi-layer error injection sequence", UVM_MEDIUM)
            
            // Inject simultaneous errors across multiple layers
            inject_combined_errors();
            
            // Test error recovery and interaction
            inject_error_recovery_scenarios();
            
            `uvm_info(get_type_name(), "Multi-layer error injection sequence completed", UVM_MEDIUM)
        endtask
        
        virtual task inject_combined_errors();
            `uvm_info(get_type_name(), "Injecting combined multi-layer errors", UVM_MEDIUM)
            
            repeat (10) begin
                uart_transaction req = uart_transaction::type_id::create("req");
                start_item(req);
                
                if (!req.randomize() with {
                    length inside {[8:64]};
                    crc_enable == 1'b1;
                }) begin
                    `uvm_error(get_type_name(), "Failed to randomize multi-error transaction")
                end
                
                // Inject multiple simultaneous errors
                if ($urandom_range(1, 100) <= error_injection_rate) begin
                    // UART + CRC error combination
                    if ($urandom_range(1, 2) == 1) begin
                        req.force_parity_error = 1'b1;
                        req.force_crc_error = 1'b1;
                        `uvm_info(get_type_name(), "Injecting UART parity + CRC error", UVM_HIGH)
                    end else begin
                        // FIFO + AXI error combination  
                        req.force_fifo_full = 1'b1;
                        req.force_axi_timeout = 1'b1;
                        `uvm_info(get_type_name(), "Injecting FIFO full + AXI timeout", UVM_HIGH)
                    end
                end
                
                finish_item(req);
                post_error_recovery();
            end
        endtask
        
        virtual task inject_error_recovery_scenarios();
            `uvm_info(get_type_name(), "Testing error recovery scenarios", UVM_MEDIUM)
            
            repeat (8) begin
                uart_transaction error_req, clean_req;
                
                // Inject error
                error_req = uart_transaction::type_id::create("error_req");
                start_item(error_req);
                if (!error_req.randomize() with { length inside {[4:32]}; }) begin
                    `uvm_error(get_type_name(), "Failed to randomize error recovery transaction")
                end
                
                error_req.force_framing_error = 1'b1; // Guaranteed error
                finish_item(error_req);
                
                // Wait for recovery
                post_error_recovery();
                
                // Send clean transaction to verify recovery
                clean_req = uart_transaction::type_id::create("clean_req");
                start_item(clean_req);
                if (!clean_req.randomize() with { 
                    length inside {[1:16]};
                    crc_enable == 1'b1;
                }) begin
                    `uvm_error(get_type_name(), "Failed to randomize clean recovery transaction")
                end
                    
                finish_item(clean_req);
                
                #100; // Allow system to stabilize
            end
        endtask
        
    endclass

endpackage