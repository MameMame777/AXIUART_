#!/usr/bin/env pwsh

# UART AXI4 Test Summary Script
param(
    [string]$TestName = "uart_axi4_basic_test"
)

Write-Host "=== UART AXI4 Test Summary ===" -ForegroundColor Green
Write-Host "Test: $TestName" -ForegroundColor Cyan
Write-Host "Starting test execution..." -ForegroundColor Yellow

# Check if test was already run (dsim.log exists)
if (Test-Path "dsim.log") {
    Write-Host "Reading existing test results from dsim.log..." -ForegroundColor Yellow
    $logContent = Get-Content "dsim.log"
} else {
    Write-Host "Running test and capturing output..." -ForegroundColor Yellow
    $output = & ".\run_uvm.ps1" -TestName $TestName 2>&1
    $logContent = Get-Content "dsim.log" -ErrorAction SilentlyContinue
}

# Count actual UVM errors (excluding report summary lines)
$errorLines = $logContent | Select-String "UVM_ERROR" | Where-Object { $_.Line -notmatch "UVM_ERROR\s*:" }
$fatalLines = $logContent | Select-String "UVM_FATAL" | Where-Object { $_.Line -notmatch "UVM_FATAL\s*:" }
$errorCount = $errorLines.Count
$fatalCount = $fatalLines.Count

# Extract execution information from log
$executionTime = $logContent | Select-String "Simulation terminated" | Select-Object -Last 1
$reportSummary = $logContent | Select-String "UVM Report Summary" -A 10

# Extract timing and completion info  
$testComplete = $logContent | Select-String "Test.*completed|simulation.*terminated" | Select-Object -Last 1

Write-Host "`n=== Test Results Analysis ===" -ForegroundColor Green
if ($executionTime) {
    Write-Host "✓ DSIM execution completed successfully" -ForegroundColor Green
} else {
    Write-Host "✗ DSIM execution may have failed" -ForegroundColor Red
}

if ($errorCount -eq 0 -and $fatalCount -eq 0) {
    Write-Host "✓ UVM test passed (UVM_ERROR: 0)" -ForegroundColor Green
} else {
    Write-Host "✗ UVM test failed (UVM_ERROR: $errorCount)" -ForegroundColor Red
}

if ($logContent | Select-String "UVM_WARNING") {
    $warningCount = ($logContent | Select-String "UVM_WARNING" | Where-Object { $_.Line -notmatch "UVM_WARNING\s*:" }).Count
    Write-Host "⚠ UVM warnings detected: $warningCount" -ForegroundColor Yellow
}

# Show summary
Write-Host "`n=== Test Results ===" -ForegroundColor Green
Write-Host "UVM_ERROR Count: $errorCount" -ForegroundColor $(if($errorCount -eq 0) {"Green"} else {"Red"})
Write-Host "UVM_FATAL Count: $fatalCount" -ForegroundColor $(if($fatalCount -eq 0) {"Green"} else {"Red"})

if ($testComplete) {
    Write-Host "Completion: $($testComplete.Line)" -ForegroundColor Green
}

# Show errors if any
if ($errorCount -gt 0) {
    Write-Host "`n=== Error Details ===" -ForegroundColor Red
    $errorLines | Select-Object -First 5 | ForEach-Object {
        Write-Host $_.Line -ForegroundColor Red
    }
    if ($errorCount -gt 5) {
        Write-Host "... and $($errorCount - 5) more errors" -ForegroundColor Red
    }
}

# Overall result
Write-Host "`n=== Overall Result ===" -ForegroundColor Green
if ($errorCount -eq 0 -and $fatalCount -eq 0) {
    Write-Host "✅ TEST PASSED - No errors detected!" -ForegroundColor Green
} else {
    Write-Host "❌ TEST FAILED - Errors detected" -ForegroundColor Red
}

Write-Host "===========================================" -ForegroundColor Green