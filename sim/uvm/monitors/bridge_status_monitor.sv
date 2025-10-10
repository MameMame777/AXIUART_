`timescale 1ns / 1ps

class bridge_status_monitor extends uvm_component;

    `uvm_component_utils(bridge_status_monitor)

    virtual bridge_status_if vif;
    uart_axi4_env_config cfg;

    int report_verbosity;

    // Note: bridge_enable functionality removed - monitor now tracks general bridge status
    covergroup bridge_status_cg @(posedge vif.clk);
        option.per_instance = 1;
        // Monitor general bridge activity instead of enable/disable states
        bridge_active: coverpoint (vif.rst_n) {
            bins active = {1'b1};
            bins reset = {1'b0};
        }
    endgroup

    function new(string name = "bridge_status_monitor", uvm_component parent = null);
        super.new(name, parent);
        bridge_status_cg = new();
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
                // Reset state - no bridge_enable related variables to reset
                continue;
            end

            bridge_status_cg.sample();

            // Bridge status monitoring (bridge_enable removed)
            // Monitor other bridge status signals if needed
        end
    endtask


    virtual function void report_phase(uvm_phase phase);
        string test_name;
        super.report_phase(phase);
        
        // Get test name from command line arguments
        if (!$value$plusargs("UVM_TESTNAME=%s", test_name)) begin
            test_name = "unknown_test";
        end

        // Bridge status monitoring completed (bridge_enable functionality removed)
        `uvm_info("BRIDGE_MON", "Bridge status monitoring completed", report_verbosity)
    endfunction

endclass
