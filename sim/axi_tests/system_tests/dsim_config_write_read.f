# DSIM configuration for UART Write-Read Test
+acc+rwb
+timescale+1ns/1ps

# Include all necessary SystemVerilog files
../../../rtl/axi4_lite_if.sv
../../../rtl/Address_Aligner.sv
../../../rtl/fifo_sync.sv
../../../rtl/Uart_Rx.sv  
../../../rtl/Uart_Tx.sv
../../../rtl/Frame_Parser.sv
../../../rtl/Frame_Builder.sv
../../../rtl/Axi4_Lite_Master.sv
../../../rtl/Register_Block.sv
../../../rtl/Crc8_Calculator.sv
../../../rtl/Uart_Axi4_Bridge.sv

# Test bench
uart_write_read_test.sv

+define+ENABLE_DEBUG