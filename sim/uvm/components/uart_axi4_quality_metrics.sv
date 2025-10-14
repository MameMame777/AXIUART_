`timescale 1ns/1ps

// QA-2.2 Automatic Quality Metrics System
// Comprehensive coverage, assertion, and timing quality measurement
// Author: QA Framework - FastMCP v2.0
// Date: 2025-10-14

class uart_axi4_quality_metrics extends uvm_object;
    `uvm_object_utils(uart_axi4_quality_metrics)
    
    // Coverage Metrics
    real functional_coverage_percent = 0.0;
    real code_coverage_percent = 0.0;
    real assertion_coverage_percent = 0.0;
    real toggle_coverage_percent = 0.0;
    
    // Assertion Metrics
    int assertion_pass_count = 0;
    int assertion_fail_count = 0;
    int assertion_total_count = 0;
    string assertion_failures[$];
    
    // Timing Metrics
    time min_response_time = 0;
    time max_response_time = 0;
    time avg_response_time = 0;
    time total_response_time = 0;
    int response_count = 0;
    
    // Performance Metrics
    real throughput_mbps = 0.0;
    int total_bytes_processed = 0;
    time simulation_duration = 0;
    
    // Quality Score Components
    real coverage_score = 0.0;
    real assertion_score = 0.0;
    real timing_score = 0.0;
    real overall_quality_score = 0.0;
    
    function new(string name = "uart_axi4_quality_metrics");
        super.new(name);
    endfunction
    
    // Update coverage metrics
    function void update_coverage_metrics(real func_cov, real code_cov, real assert_cov, real toggle_cov);
        functional_coverage_percent = func_cov;
        code_coverage_percent = code_cov;
        assertion_coverage_percent = assert_cov;
        toggle_coverage_percent = toggle_cov;
        
        // Calculate coverage score (weighted average)
        coverage_score = (functional_coverage_percent * 0.4) + 
                        (code_coverage_percent * 0.3) + 
                        (assertion_coverage_percent * 0.2) + 
                        (toggle_coverage_percent * 0.1);
    endfunction
    
    // Update assertion metrics
    function void update_assertion_metrics(int pass_count, int fail_count, string failures[$]);
        assertion_pass_count = pass_count;
        assertion_fail_count = fail_count;
        assertion_total_count = pass_count + fail_count;
        assertion_failures = failures;
        
        // Calculate assertion score
        if (assertion_total_count > 0) begin
            assertion_score = (real'(assertion_pass_count) / real'(assertion_total_count)) * 100.0;
        end else begin
            assertion_score = 0.0;
        end
    endfunction
    
    // Update timing metrics
    function void add_response_time(time response_time);
        response_count++;
        total_response_time += response_time;
        
        if (response_count == 1) begin
            min_response_time = response_time;
            max_response_time = response_time;
        end else begin
            if (response_time < min_response_time) min_response_time = response_time;
            if (response_time > max_response_time) max_response_time = response_time;
        end
        
        avg_response_time = total_response_time / response_count;
        
        // Calculate timing score based on response time consistency
        calculate_timing_score();
    endfunction
    
    // Calculate timing quality score
    function void calculate_timing_score();
        time response_variation;
        real variation_percent;
        
        if (response_count == 0) begin
            timing_score = 0.0;
            return;
        end
        
        response_variation = max_response_time - min_response_time;
        
        if (avg_response_time > 0) begin
            variation_percent = (real'(response_variation) / real'(avg_response_time)) * 100.0;
            
            // Score decreases with higher variation
            if (variation_percent < 10.0) begin
                timing_score = 100.0;
            end else if (variation_percent < 50.0) begin
                timing_score = 100.0 - (variation_percent - 10.0);
            end else begin
                timing_score = 60.0 - ((variation_percent - 50.0) / 2.0);
            end
            
            if (timing_score < 0.0) timing_score = 0.0;
        end else begin
            timing_score = 0.0;
        end
    endfunction
    
    // Update performance metrics
    function void update_performance_metrics(int bytes_processed, time sim_duration);
        total_bytes_processed = bytes_processed;
        simulation_duration = sim_duration;
        
        if (sim_duration > 0) begin
            // Calculate throughput in Mbps
            throughput_mbps = (real'(total_bytes_processed) * 8.0) / 
                             (real'(sim_duration) / 1000000000.0) / 1000000.0;
        end else begin
            throughput_mbps = 0.0;
        end
    endfunction
    
    // Calculate overall quality score
    function real calculate_overall_quality();
        // Weighted combination of all quality metrics
        overall_quality_score = (coverage_score * 0.5) + 
                               (assertion_score * 0.3) + 
                               (timing_score * 0.2);
        return overall_quality_score;
    endfunction
    
    // Generate quality report
    function string generate_quality_report();
        string report;
        
        report = "\n";
        report = {report, "================ QA-2.2 QUALITY METRICS REPORT ================\n"};
        
        // Coverage Metrics
        report = {report, "--- COVERAGE METRICS ---\n"};
        report = {report, $sformatf("Functional Coverage: %.1f%%\n", functional_coverage_percent)};
        report = {report, $sformatf("Code Coverage: %.1f%%\n", code_coverage_percent)};
        report = {report, $sformatf("Assertion Coverage: %.1f%%\n", assertion_coverage_percent)};
        report = {report, $sformatf("Toggle Coverage: %.1f%%\n", toggle_coverage_percent)};
        report = {report, $sformatf("Coverage Score: %.1f/100\n", coverage_score)};
        
        // Assertion Metrics
        report = {report, "\n--- ASSERTION METRICS ---\n"};
        report = {report, $sformatf("Assertions Passed: %0d\n", assertion_pass_count)};
        report = {report, $sformatf("Assertions Failed: %0d\n", assertion_fail_count)};
        report = {report, $sformatf("Total Assertions: %0d\n", assertion_total_count)};
        report = {report, $sformatf("Assertion Score: %.1f/100\n", assertion_score)};
        
        if (assertion_failures.size() > 0) begin
            report = {report, "Assertion Failures:\n"};
            foreach (assertion_failures[i]) begin
                report = {report, $sformatf("  - %s\n", assertion_failures[i])};
            end
        end
        
        // Timing Metrics
        report = {report, "\n--- TIMING METRICS ---\n"};
        report = {report, $sformatf("Min Response Time: %0t ns\n", min_response_time)};
        report = {report, $sformatf("Max Response Time: %0t ns\n", max_response_time)};
        report = {report, $sformatf("Avg Response Time: %0t ns\n", avg_response_time)};
        report = {report, $sformatf("Response Count: %0d\n", response_count)};
        report = {report, $sformatf("Timing Score: %.1f/100\n", timing_score)};
        
        // Performance Metrics
        report = {report, "\n--- PERFORMANCE METRICS ---\n"};
        report = {report, $sformatf("Total Bytes Processed: %0d\n", total_bytes_processed)};
        report = {report, $sformatf("Simulation Duration: %0t ns\n", simulation_duration)};
        report = {report, $sformatf("Throughput: %.3f Mbps\n", throughput_mbps)};
        
        // Overall Quality Assessment
        calculate_overall_quality();
        report = {report, "\n--- OVERALL QUALITY ASSESSMENT ---\n"};
        report = {report, $sformatf("Overall Quality Score: %.1f/100\n", overall_quality_score)};
        
        // Quality Grade
        if (overall_quality_score >= 90.0) begin
            report = {report, "Quality Grade: A+ (Excellent)\n"};
        end else if (overall_quality_score >= 80.0) begin
            report = {report, "Quality Grade: A (Good)\n"};
        end else if (overall_quality_score >= 70.0) begin
            report = {report, "Quality Grade: B (Acceptable)\n"};
        end else if (overall_quality_score >= 60.0) begin
            report = {report, "Quality Grade: C (Needs Improvement)\n"};
        end else begin
            report = {report, "Quality Grade: F (Poor)\n"};
        end
        
        report = {report, "===============================================================\n"};
        
        return report;
    endfunction
    
    // Export metrics to JSON format
    function string export_metrics_json();
        string json_str;
        
        json_str = "{\n";
        json_str = {json_str, "  \"coverage\": {\n"};
        json_str = {json_str, $sformatf("    \"functional\": %.1f,\n", functional_coverage_percent)};
        json_str = {json_str, $sformatf("    \"code\": %.1f,\n", code_coverage_percent)};
        json_str = {json_str, $sformatf("    \"assertion\": %.1f,\n", assertion_coverage_percent)};
        json_str = {json_str, $sformatf("    \"toggle\": %.1f,\n", toggle_coverage_percent)};
        json_str = {json_str, $sformatf("    \"score\": %.1f\n", coverage_score)};
        json_str = {json_str, "  },\n"};
        
        json_str = {json_str, "  \"assertions\": {\n"};
        json_str = {json_str, $sformatf("    \"passed\": %0d,\n", assertion_pass_count)};
        json_str = {json_str, $sformatf("    \"failed\": %0d,\n", assertion_fail_count)};
        json_str = {json_str, $sformatf("    \"total\": %0d,\n", assertion_total_count)};
        json_str = {json_str, $sformatf("    \"score\": %.1f\n", assertion_score)};
        json_str = {json_str, "  },\n"};
        
        json_str = {json_str, "  \"timing\": {\n"};
        json_str = {json_str, $sformatf("    \"min_response_ns\": %0d,\n", min_response_time)};
        json_str = {json_str, $sformatf("    \"max_response_ns\": %0d,\n", max_response_time)};
        json_str = {json_str, $sformatf("    \"avg_response_ns\": %0d,\n", avg_response_time)};
        json_str = {json_str, $sformatf("    \"response_count\": %0d,\n", response_count)};
        json_str = {json_str, $sformatf("    \"score\": %.1f\n", timing_score)};
        json_str = {json_str, "  },\n"};
        
        json_str = {json_str, "  \"performance\": {\n"};
        json_str = {json_str, $sformatf("    \"bytes_processed\": %0d,\n", total_bytes_processed)};
        json_str = {json_str, $sformatf("    \"duration_ns\": %0d,\n", simulation_duration)};
        json_str = {json_str, $sformatf("    \"throughput_mbps\": %.3f\n", throughput_mbps)};
        json_str = {json_str, "  },\n"};
        
        json_str = {json_str, $sformatf("  \"overall_score\": %.1f,\n", overall_quality_score)};
        json_str = {json_str, $sformatf("  \"timestamp\": \"%0t\"\n", $time)};
        json_str = {json_str, "}\n"};
        
        return json_str;
    endfunction
    
endclass