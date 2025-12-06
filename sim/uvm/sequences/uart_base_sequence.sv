`timescale 1ns / 1ps

//------------------------------------------------------------------------------
// SEQUENCE: uart_base_sequence
//
// UBUS-compliant base sequence for UART frame transactions
// Implements automatic objection management via pre_body/post_body hooks
//------------------------------------------------------------------------------

virtual class uart_base_sequence extends uvm_sequence #(uart_frame_transaction);

  function new(string name="uart_base_seq");
    super.new(name);
  endfunction
  
  // Raise objection in pre_body so only ROOT sequences raise objections.
  // Sub-sequences started within a parent sequence will NOT raise objections
  // because starting_phase will be null when called via start() without phase argument.
  virtual task pre_body();
    if (starting_phase != null) begin
      `uvm_info(get_type_name(),
        $sformatf("%s pre_body() raising %s objection", 
          get_sequence_path(),
          starting_phase.get_name()), UVM_MEDIUM);
      starting_phase.raise_objection(this);
    end
  endtask

  // Drop objection in post_body when the root sequence completes.
  virtual task post_body();
    if (starting_phase != null) begin
      `uvm_info(get_type_name(),
        $sformatf("%s post_body() dropping %s objection", 
          get_sequence_path(),
          starting_phase.get_name()), UVM_MEDIUM);
      starting_phase.drop_objection(this);
    end
  endtask
  
endclass : uart_base_sequence
