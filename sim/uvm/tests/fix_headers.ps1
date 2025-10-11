# Fix corrupted file headers
param()

$files = @(
    "axiuart_system_test.sv",
    "uart_axi4_simple_write_test.sv", 
    "uart_axi4_multi_beat_write_test.sv",
    "register_block_tests.sv",
    "uart_coverage_debug_test.sv",
    "uart_axi4_optimized_coverage_test.sv",
    "uart_axi4_register_block_test.sv",
    "uart_axi4_read_protocol_test.sv",
    "uart_flow_control_tests.sv"
)

foreach ($file in $files) {
    if (Test-Path $file) {
        Write-Host "Fixing $file..."
        $content = Get-Content $file -Raw -Encoding UTF8
        # Remove any invalid characters from the beginning and ensure it starts with backtick
        $fixed = $content -replace '^[^\x20-\x7E\r\n\t]*', '`'
        $fixed | Set-Content $file -Encoding UTF8 -NoNewline
        Write-Host "  Fixed: $file"
    }
}

Write-Host "File header fix complete."