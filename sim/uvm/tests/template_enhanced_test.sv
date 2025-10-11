`timescale 1ns / 1ps

// Template for Enhanced UVM Test Development
// Created: October 10, 2025
// Purpose: Standard template with mandatory enhanced reporting

class template_enhanced_test extends enhanced_uart_axi4_base_test;
    
    `uvm_component_utils(template_enhanced_test)
    
    function new(string name = "template_enhanced_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Enhanced build phase with test-specific reporting
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Configure test-specific reporting IDs
        configure_test_specific_reporting();
        
        `uvm_info("TEMPLATE_TEST", "Template test with enhanced reporting initialized", UVM_LOW)
    endfunction
    
    // Test-specific report ID configuration
    virtual function void configure_test_specific_reporting();
        // Define test-specific report categories
        this.set_report_id_verbosity_hier("TEMPLATE_START", UVM_MEDIUM);
        this.set_report_id_verbosity_hier("TEMPLATE_PROGRESS", UVM_MEDIUM);
        this.set_report_id_verbosity_hier("TEMPLATE_RESULT", UVM_LOW);
        this.set_report_id_verbosity_hier("TEMPLATE_DEBUG", UVM_HIGH);
        
        // Configure test-specific component verbosity
        // Adjust based on test requirements
        set_report_verbosity_level_hier("*sequence*", UVM_MEDIUM);
        
        `uvm_info("TEMPLATE_CONFIG", "Test-specific reporting configuration complete", UVM_LOW)
    endfunction
    
    // Enhanced test execution with categorized reporting
    virtual task run_phase(uvm_phase phase);
        `uvm_info("TEMPLATE_START", "=== TEMPLATE ENHANCED TEST START ===", UVM_LOW)
        `uvm_info("TEMPLATE_START", "Purpose: [Describe test purpose here]", UVM_LOW)
        
        phase.raise_objection(this);
        
        // Test implementation template
        execute_test_sequence();
        
        phase.drop_objection(this);
        
        `uvm_info("TEMPLATE_RESULT", "=== TEMPLATE ENHANCED TEST END ===", UVM_LOW)
    endtask
    
    // Test sequence execution template
    virtual task execute_test_sequence();
        `uvm_info("TEMPLATE_PROGRESS", "Starting test sequence execution", UVM_MEDIUM)
        
        // Template sequence execution
        // Replace with actual test implementation
        
        // Example sequence start
        `uvm_info("TEMPLATE_DEBUG", "Debug: Test sequence step 1", UVM_HIGH)
        
        // Wait for test completion
        #10000ns;
        
        `uvm_info("TEMPLATE_PROGRESS", "Test sequence execution completed", UVM_MEDIUM)
    endtask
    
    // Enhanced result validation with detailed reporting
    virtual function void check_phase(uvm_phase phase);
        super.check_phase(phase);
        
        `uvm_info("TEMPLATE_RESULT", "Performing enhanced result validation", UVM_LOW)
        
        // Add test-specific validation logic here
        validate_test_results();
    endfunction
    
    // Test-specific result validation
    virtual function void validate_test_results();
        // Template for result validation
        `uvm_info("TEMPLATE_RESULT", "Expected: [Describe expected results]", UVM_LOW)
        `uvm_info("TEMPLATE_RESULT", "Actual: [Report actual results]", UVM_LOW)
        
        // Add actual validation logic
        // if (expected != actual) begin
        //     `uvm_error("TEMPLATE_RESULT", "Test validation failed")
        // end else begin
        //     `uvm_info("TEMPLATE_RESULT", "Test validation PASSED", UVM_LOW)
        // end
    endfunction
    
endclass : template_enhanced_test

// Usage Guidelines:
// 1. Copy this template for new test development
// 2. Replace "template" with your test name throughout
// 3. Implement configure_test_specific_reporting() for your test
// 4. Add actual test logic in execute_test_sequence()
// 5. Implement result validation in validate_test_results()
// 6. Use categorized report IDs consistently:
//    - [TEST_NAME]_START: Test initialization messages
//    - [TEST_NAME]_PROGRESS: Test execution progress
//    - [TEST_NAME]_RESULT: Test results and validation
//    - [TEST_NAME]_DEBUG: Detailed debugging information
