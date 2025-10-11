# PowerShell script to update UVM test class inheritance
# Updates all test classes to inherit from enhanced_uart_axi4_base_test

param(
    [string]$TestDirectory = "e:\Nautilus\workspace\fpgawork\AXIUART_\sim\uvm\tests",
    [switch]$DryRun = $false
)

Write-Host "UVM Test Inheritance Updater" -ForegroundColor Green
Write-Host "Purpose: Update test classes to inherit from enhanced_uart_axi4_base_test" -ForegroundColor Yellow
Write-Host "Directory: $TestDirectory" -ForegroundColor Cyan

if ($DryRun) {
    Write-Host "DRY RUN MODE - No files will be modified" -ForegroundColor Yellow
}

# Get all SystemVerilog test files
$testFiles = Get-ChildItem -Path $TestDirectory -Filter "*.sv" | Where-Object {
    $_.Name -like "*test*.sv" -and 
    $_.Name -ne "enhanced_uart_axi4_base_test.sv" -and
    $_.Name -ne "uart_axi4_base_test.sv"
}

Write-Host "Found $($testFiles.Count) test files to process" -ForegroundColor Green

$updatedCount = 0
$skippedCount = 0

foreach ($file in $testFiles) {
    Write-Host "`nProcessing: $($file.Name)" -ForegroundColor Cyan
    
    $content = Get-Content $file.FullName -Raw
    
    # Check if file needs updating
    if ($content -match "extends uart_axi4_base_test" -and $content -notmatch "enhanced_uart_axi4_base_test") {
        Write-Host "  - Needs update: Found 'extends uart_axi4_base_test'" -ForegroundColor Yellow
        
        if (-not $DryRun) {
            # Update inheritance
            $updatedContent = $content -replace "extends uart_axi4_base_test", "extends enhanced_uart_axi4_base_test"
            
            # Add test-specific reporting configuration if build_phase exists
            if ($content -match "virtual function void build_phase\(uvm_phase phase\);") {
                # Add configure_test_specific_reporting call after super.build_phase
                $updatedContent = $updatedContent -replace 
                    "(virtual function void build_phase\(uvm_phase phase\);\s*super\.build_phase\(phase\);)",
                    "`$1`n        configure_test_specific_reporting();"
                
                # Add the configuration function before existing functions
                $className = ($file.BaseName -replace "_test$", "") -replace "uart_axi4_", ""
                $reportIdPrefix = "TEST_" + $className.ToUpper()
                
                $configFunction = @"

    // Test-specific reporting configuration
    virtual function void configure_test_specific_reporting();
        // Configure test-specific IDs for $className testing
        uvm_report_server::set_id_verbosity("${reportIdPrefix}_START", UVM_HIGH);
        uvm_report_server::set_id_verbosity("${reportIdPrefix}_PROGRESS", UVM_MEDIUM);
        uvm_report_server::set_id_verbosity("${reportIdPrefix}_RESULT", UVM_HIGH);
    endfunction
"@
                
                # Insert before the first virtual task or function after build_phase
                $updatedContent = $updatedContent -replace 
                    "(configure_test_specific_reporting\(\);\s*endfunction\s*)(virtual task|virtual function)",
                    "`$1$configFunction`n`n    `$2"
            }
            
            Set-Content -Path $file.FullName -Value $updatedContent -Encoding UTF8
            Write-Host "  - Updated successfully" -ForegroundColor Green
            $updatedCount++
        } else {
            Write-Host "  - Would be updated (DRY RUN)" -ForegroundColor Magenta
        }
    } elseif ($content -match "enhanced_uart_axi4_base_test") {
        Write-Host "  - Already updated" -ForegroundColor Green
        $skippedCount++
    } else {
        Write-Host "  - No inheritance pattern found" -ForegroundColor Gray
        $skippedCount++
    }
}

Write-Host "`n=== Summary ===" -ForegroundColor Green
Write-Host "Files processed: $($testFiles.Count)"
Write-Host "Files updated: $updatedCount"
Write-Host "Files skipped: $skippedCount"

if ($DryRun) {
    Write-Host "`nTo apply changes, run without -DryRun flag" -ForegroundColor Yellow
} else {
    Write-Host "`nAll applicable files have been updated" -ForegroundColor Green
}