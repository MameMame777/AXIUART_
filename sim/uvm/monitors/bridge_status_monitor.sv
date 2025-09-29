`timescale 1ns / 1ps

class bridge_status_monitor extends uvm_component;

    `uvm_component_utils(bridge_status_monitor)

    virtual bridge_status_if vif;
    uart_axi4_env_config cfg;

    bit disable_seen;
    bit reenable_seen;
    bit initial_enable_seen;
    time disable_time;
    time reenable_time;
    int report_verbosity;

    covergroup bridge_enable_cg @(posedge vif.clk);
        option.per_instance = 1;
        bridge_state: coverpoint vif.bridge_enable iff (vif.rst_n) {
            bins enabled = {1'b1};
            bins disabled = {1'b0};
            bins disable_transition = (1 => 0);
            bins enable_transition = (0 => 1);
        }
    endgroup

    function new(string name = "bridge_status_monitor", uvm_component parent = null);
        super.new(name, parent);
        bridge_enable_cg = new();
        report_verbosity = UVM_LOW;
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        if (!uvm_config_db#(virtual bridge_status_if)::get(this, "", "bridge_status_vif", vif)) begin
            `uvm_fatal("BRIDGE_MON", "Failed to get bridge_status_vif")
        end

        if (!uvm_config_db#(uart_axi4_env_config)::get(this, "", "cfg", cfg)) begin
            `uvm_warning("BRIDGE_MON", "Configuration object not provided; using defaults")
            report_verbosity = UVM_LOW;
        end else begin
            report_verbosity = cfg.bridge_status_verbosity;
        end
    endfunction

    virtual task run_phase(uvm_phase phase);
        forever begin
            @(posedge vif.clk);

            if (!vif.rst_n) begin
                disable_seen = 1'b0;
                reenable_seen = 1'b0;
                initial_enable_seen = 1'b0;
                continue;
            end

            bridge_enable_cg.sample();

            if (vif.bridge_enable) begin
                initial_enable_seen = 1'b1;
                if (disable_seen && !reenable_seen) begin
                    reenable_seen = 1'b1;
                    reenable_time = $time;
                    `uvm_info("BRIDGE_MON", $sformatf("bridge_enable re-asserted at %0t ns",
                              reenable_time / 1ns), report_verbosity)
                end
            end else begin
                if (!disable_seen) begin
                    disable_seen = 1'b1;
                    disable_time = $time;
                    `uvm_info("BRIDGE_MON", $sformatf("bridge_enable deasserted at %0t ns",
                              disable_time / 1ns), report_verbosity)
                end
            end
        end
    endtask

    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);

        if (!initial_enable_seen) begin
            `uvm_warning("BRIDGE_MON", "bridge_enable was never observed high after reset")
        end

        if (!disable_seen) begin
            `uvm_error("BRIDGE_MON", "bridge_enable never deasserted during the test")
        end else if (!reenable_seen) begin
            `uvm_error("BRIDGE_MON", "bridge_enable never re-asserted after deassertion")
        end else begin
            `uvm_info("BRIDGE_MON", "bridge_enable toggled low and recovered high", report_verbosity)
        end
    endfunction

endclass
