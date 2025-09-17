// Protocol Handler UVM Sequences
// Target Board: Zybo Z7-20  
// Date: August 1, 2025
// Description: UVM sequences for Protocol_Handler testing and debugging

`timescale 1ns / 1ps

package protocol_handler_sequences_pkg;
    import uvm_pkg::*;
    import protocol_handler_test_pkg::*;
    
    // Base sequence for protocol handler
    class protocol_handler_base_sequence extends uvm_sequence #(protocol_handler_seq_item);
        `uvm_object_utils(protocol_handler_base_sequence)
        
        function new(string name = "protocol_handler_base_sequence");
            super.new(name);
        endfunction
        
        task pre_body();
            if (starting_phase != null)
                starting_phase.raise_objection(this);
        endtask
        
        task post_body();
            if (starting_phase != null)
                starting_phase.drop_objection(this);
        endtask
    endclass
    
    // Reset sequence
    class protocol_handler_reset_sequence extends protocol_handler_base_sequence;
        `uvm_object_utils(protocol_handler_reset_sequence)
        
        function new(string name = "protocol_handler_reset_sequence");
            super.new(name);
        endfunction
        
        task body();
            protocol_handler_seq_item item;
            
            `uvm_info("RESET_SEQ", "Starting reset sequence", UVM_MEDIUM)
            
            item = protocol_handler_seq_item::type_id::create("reset_item");
            item.transaction_type = protocol_handler_seq_item::RESET_SEQUENCE;
            start_item(item);
            finish_item(item);
            
            `uvm_info("RESET_SEQ", "Reset sequence completed", UVM_MEDIUM)
        endtask
    endclass
    
    // Single character test sequence
    class protocol_handler_char_sequence extends protocol_handler_base_sequence;
        `uvm_object_utils(protocol_handler_char_sequence)
        
        rand bit [7:0] test_char = 8'h52; // Default 'R'
        
        function new(string name = "protocol_handler_char_sequence");
            super.new(name);
        endfunction
        
        task body();
            protocol_handler_seq_item item;
            
            `uvm_info("CHAR_SEQ", $sformatf("Testing single character: 0x%02x (%c)", 
                     test_char, test_char), UVM_MEDIUM)
            
            item = protocol_handler_seq_item::type_id::create("char_item");
            item.transaction_type = protocol_handler_seq_item::UART_CHAR;
            item.uart_data = test_char;
            start_item(item);
            finish_item(item);
            
            `uvm_info("CHAR_SEQ", "Character sequence completed", UVM_MEDIUM)
        endtask
    endclass
    
    // Read register sequence
    class protocol_handler_read_sequence extends protocol_handler_base_sequence;
        `uvm_object_utils(protocol_handler_read_sequence)
        
        rand bit [7:0] reg_address = 8'h00; // Default control register
        
        function new(string name = "protocol_handler_read_sequence");
            super.new(name);
        endfunction
        
        task body();
            protocol_handler_seq_item item;
            
            `uvm_info("READ_SEQ", $sformatf("Testing read from register: 0x%02x", 
                     reg_address), UVM_MEDIUM)
            
            item = protocol_handler_seq_item::type_id::create("read_item");
            item.transaction_type = protocol_handler_seq_item::READ_CMD;
            item.reg_addr = reg_address;
            start_item(item);
            finish_item(item);
            
            `uvm_info("READ_SEQ", "Read sequence completed", UVM_MEDIUM)
        endtask
    endclass
    
    // Write register sequence
    class protocol_handler_write_sequence extends protocol_handler_base_sequence;
        `uvm_object_utils(protocol_handler_write_sequence)
        
        rand bit [7:0] reg_address = 8'h00;  // Default control register
        rand bit [31:0] reg_data = 32'h00000007; // Default enable all UART
        
        function new(string name = "protocol_handler_write_sequence");
            super.new(name);
        endfunction
        
        task body();
            protocol_handler_seq_item item;
            
            `uvm_info("WRITE_SEQ", $sformatf("Testing write to register: 0x%02x = 0x%08x", 
                     reg_address, reg_data), UVM_MEDIUM)
            
            item = protocol_handler_seq_item::type_id::create("write_item");
            item.transaction_type = protocol_handler_seq_item::WRITE_CMD;
            item.reg_addr = reg_address;
            item.reg_data = reg_data;
            start_item(item);
            finish_item(item);
            
            `uvm_info("WRITE_SEQ", "Write sequence completed", UVM_MEDIUM)
        endtask
    endclass
    
    // Complete protocol test sequence
    class protocol_handler_complete_sequence extends protocol_handler_base_sequence;
        `uvm_object_utils(protocol_handler_complete_sequence)
        
        function new(string name = "protocol_handler_complete_sequence");
            super.new(name);
        endfunction
        
        task body();
            protocol_handler_reset_sequence reset_seq;
            protocol_handler_char_sequence char_seq;
            protocol_handler_read_sequence read_seq;
            protocol_handler_write_sequence write_seq;
            
            `uvm_info("COMPLETE_SEQ", "Starting complete protocol test", UVM_MEDIUM)
            
            // Step 1: Reset the system
            reset_seq = protocol_handler_reset_sequence::type_id::create("reset_seq");
            reset_seq.start(m_sequencer);
            
            // Step 2: Test individual characters
            char_seq = protocol_handler_char_sequence::type_id::create("char_seq");
            
            // Test 'R' character
            char_seq.test_char = 8'h52; // 'R'
            char_seq.start(m_sequencer);
            
            // Test 'W' character
            char_seq.test_char = 8'h57; // 'W'
            char_seq.start(m_sequencer);
            
            // Test invalid character
            char_seq.test_char = 8'h58; // 'X'
            char_seq.start(m_sequencer);
            
            // Step 3: Test read commands
            read_seq = protocol_handler_read_sequence::type_id::create("read_seq");
            
            // Read control register
            read_seq.reg_address = 8'h00;
            read_seq.start(m_sequencer);
            
            // Read status register
            read_seq.reg_address = 8'h01;
            read_seq.start(m_sequencer);
            
            // Read FIFO status
            read_seq.reg_address = 8'h04;
            read_seq.start(m_sequencer);
            
            // Step 4: Test write commands
            write_seq = protocol_handler_write_sequence::type_id::create("write_seq");
            
            // Enable UART
            write_seq.reg_address = 8'h00;
            write_seq.reg_data = 32'h00000007; // Enable UART, TX, RX
            write_seq.start(m_sequencer);
            
            // Verify write
            read_seq.reg_address = 8'h00;
            read_seq.start(m_sequencer);
            
            `uvm_info("COMPLETE_SEQ", "Complete protocol test finished", UVM_MEDIUM)
        endtask
    endclass
    
    // Debug focused sequence - specifically for current issue
    class protocol_handler_debug_sequence extends protocol_handler_base_sequence;
        `uvm_object_utils(protocol_handler_debug_sequence)
        
        function new(string name = "protocol_handler_debug_sequence");
            super.new(name);
        endfunction
        
        task body();
            protocol_handler_reset_sequence reset_seq;
            protocol_handler_char_sequence char_seq;
            protocol_handler_read_sequence read_seq;
            
            `uvm_info("DEBUG_SEQ", "Starting focused debug sequence", UVM_HIGH)
            
            // Reset first
            reset_seq = protocol_handler_reset_sequence::type_id::create("reset_seq");
            reset_seq.start(m_sequencer);
            
            // Wait for reset to settle
            #1000ns;
            
            // Test exactly what we're sending in real hardware
            char_seq = protocol_handler_char_sequence::type_id::create("char_seq");
            
            // Send 'R' as first character
            `uvm_info("DEBUG_SEQ", "Sending 'R' character (0x52)", UVM_HIGH)
            char_seq.test_char = 8'h52; // 'R'
            char_seq.start(m_sequencer);
            
            // Wait and observe
            #5000ns;
            
            // Send '0' as address high nibble
            `uvm_info("DEBUG_SEQ", "Sending '0' character (0x30)", UVM_HIGH)
            char_seq.test_char = 8'h30; // '0'
            char_seq.start(m_sequencer);
            
            #5000ns;
            
            // Send '0' as address low nibble
            `uvm_info("DEBUG_SEQ", "Sending '0' character (0x30)", UVM_HIGH)
            char_seq.test_char = 8'h30; // '0'
            char_seq.start(m_sequencer);
            
            // Wait for response
            #10000ns;
            
            `uvm_info("DEBUG_SEQ", "Debug sequence completed - check for response", UVM_HIGH)
        endtask
    endclass
    
endpackage
