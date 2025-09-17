// UART Physical Interface Test Sequence
// Target Board: Zybo Z7-20
// Date: July 26, 2025
// Description: Test sequence for UART physical layer functionality

`ifndef UART_PHYSICAL_SEQUENCE_SV
`define UART_PHYSICAL_SEQUENCE_SV

class uart_physical_sequence extends uart_base_sequence;
    
    // UVM registration
    `uvm_object_utils(uart_physical_sequence)
    
    // Constructor
    function new(string name = "uart_physical_sequence");
        super.new(name);
    endfunction
    
    // Main sequence body
    virtual task body();
        `uvm_info("UART_PHY", "Starting UART physical interface test", UVM_LOW)
        
        // Step 1: Basic transmission test
        test_basic_transmission();
        
        // Step 2: Flow control test
        test_flow_control();
        
        // Step 3: Error injection test
        test_error_injection();
        
        // Step 4: Timing variation test
        test_timing_variations();
        
        // Step 5: Continuous data stream test
        test_continuous_stream();
        
        `uvm_info("UART_PHY", "UART physical interface test completed", UVM_LOW)
    endtask
    
    // Test basic UART transmission
    task test_basic_transmission();
        bit [7:0] test_data[] = {
            8'h00, 8'h55, 8'hAA, 8'hFF,
            8'h0F, 8'hF0, 8'h33, 8'hCC
        };
        
        `uvm_info("UART_PHY", "Testing basic UART transmission", UVM_MEDIUM)
        
        // Setup receive mode first
        setup_receive();
        
        // Send each test pattern
        foreach (test_data[i]) begin
            `uvm_info("UART_PHY", $sformatf("Sending data pattern: 0x%02h", test_data[i]), UVM_MEDIUM)
            send_byte(test_data[i]);
            
            // Allow time for transmission
            #(12 * (1000000000 / UART_BAUD_RATE)); // 12 bit times
        end
    endtask
    
    // Test flow control functionality
    task test_flow_control();
        bit [7:0] flow_test_data[] = {'F', 'L', 'O', 'W'};
        
        `uvm_info("UART_PHY", "Testing UART flow control", UVM_MEDIUM)
        
        // Test with flow control enabled
        foreach (flow_test_data[i]) begin
            `uvm_info("UART_PHY", $sformatf("Sending with flow control: '%c'", flow_test_data[i]), UVM_MEDIUM)
            send_byte(flow_test_data[i], 1); // Enable flow control
            
            #(15 * (1000000000 / UART_BAUD_RATE)); // Extra time for flow control
        end
        
        // Test flow control timing
        test_flow_control_timing();
    endtask
    
    // Test flow control timing scenarios
    task test_flow_control_timing();
        uart_transaction tr;
        
        `uvm_info("UART_PHY", "Testing flow control timing scenarios", UVM_MEDIUM)
        
        // Test RTS assertion timing
        tr = uart_transaction::type_id::create("flow_timing_tr");
        if (!tr.randomize() with {
            trans_type == uart_transaction::TX;
            data == 8'h54; // 'T'
            use_flow_control == 1;
            rts_assert == 1;
            cts_ready == 0; // CTS not initially ready
        }) begin
            `uvm_error("UART_PHY", "Failed to randomize flow control timing transaction")
        end
        
        start_item(tr);
        finish_item(tr);
        
        #(20 * (1000000000 / UART_BAUD_RATE));
    endtask
    
    // Test error injection at physical layer
    task test_error_injection();
        `uvm_info("UART_PHY", "Testing UART error injection", UVM_MEDIUM)
        
        // Test frame error
        send_byte_with_error(8'h45, 0, 1, 0); // 'E' with frame error
        #(15 * (1000000000 / UART_BAUD_RATE));
        
        // Test parity error (if supported)
        send_byte_with_error(8'h50, 1, 0, 0); // 'P' with parity error
        #(15 * (1000000000 / UART_BAUD_RATE));
        
        // Test overrun error
        send_byte_with_error(8'h4F, 0, 0, 1); // 'O' with overrun error
        #(15 * (1000000000 / UART_BAUD_RATE));
        
        // Test multiple errors
        send_byte_with_error(8'h4D, 1, 1, 0); // 'M' with multiple errors
        #(15 * (1000000000 / UART_BAUD_RATE));
    endtask
    
    // Test timing variations
    task test_timing_variations();
        uart_transaction tr;
        int timing_variations[] = {1, 2, 3, 5, 8}; // Different bit periods
        
        `uvm_info("UART_PHY", "Testing UART timing variations", UVM_MEDIUM)
        
        foreach (timing_variations[i]) begin
            `uvm_info("UART_PHY", $sformatf("Testing bit period variation: %0d", timing_variations[i]), UVM_MEDIUM)
            
            tr = uart_transaction::type_id::create("timing_tr");
            if (!tr.randomize() with {
                trans_type == uart_transaction::TX;
                data == 8'h30 + i; // '0', '1', '2', etc.
                bit_period == timing_variations[i];
                frame_gap == timing_variations[i] * 2;
            }) begin
                `uvm_error("UART_PHY", "Failed to randomize timing variation transaction")
            end
            
            start_item(tr);
            finish_item(tr);
            
            #(20 * timing_variations[i] * (1000000000 / UART_BAUD_RATE));
        end
    endtask
    
    // Test continuous data stream
    task test_continuous_stream();
        string test_message = "Hello UART World! This is a continuous data stream test. 0123456789 ABCDEFGHIJKLMNOPQRSTUVWXYZ";
        
        `uvm_info("UART_PHY", "Testing continuous UART data stream", UVM_MEDIUM)
        `uvm_info("UART_PHY", $sformatf("Transmitting message: \"%s\"", test_message), UVM_LOW)
        
        // Send the entire message
        send_string(test_message);
        
        // Add line ending
        send_byte(8'h0D); // CR
        send_byte(8'h0A); // LF
        
        // Allow time for complete transmission
        #(test_message.len() * 12 * (1000000000 / UART_BAUD_RATE));
        
        `uvm_info("UART_PHY", "Continuous stream transmission completed", UVM_MEDIUM)
    endtask

endclass

// Virtual sequence to coordinate AXI4-Lite and UART sequences
class uart_axi_coordination_sequence extends uvm_sequence;
    
    // Sequence handles
    basic_func_sequence axi_basic_seq;
    uart_physical_sequence uart_phy_seq;
    
    // UVM registration
    `uvm_object_utils(uart_axi_coordination_sequence)
    
    // Constructor
    function new(string name = "uart_axi_coordination_sequence");
        super.new(name);
    endfunction
    
    // Pre-body task
    virtual task pre_body();
        if (starting_phase != null) begin
            starting_phase.raise_objection(this);
        end
    endtask
    
    // Post-body task
    virtual task post_body();
        if (starting_phase != null) begin
            starting_phase.drop_objection(this);
        end
    endtask
    
    // Main sequence body
    virtual task body();
        `uvm_info("COORD_SEQ", "Starting coordinated AXI4-Lite and UART test", UVM_LOW)
        
        // Create sequences
        axi_basic_seq = basic_func_sequence::type_id::create("axi_basic_seq");
        uart_phy_seq = uart_physical_sequence::type_id::create("uart_phy_seq");
        
        // Run coordinated test
        fork
            // AXI4-Lite configuration and control
            begin
                axi_basic_seq.start(p_sequencer);
            end
            
            // UART physical layer activity
            begin
                #2us; // Allow AXI setup to complete first
                uart_phy_seq.start(p_sequencer);
            end
        join
        
        `uvm_info("COORD_SEQ", "Coordinated test completed", UVM_LOW)
    endtask

endclass

`endif // UART_PHYSICAL_SEQUENCE_SV
