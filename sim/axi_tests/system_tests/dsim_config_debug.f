// DSIM configuration file for UART response debug test
-timescale 1ns/1ps

// Include directories  
+incdir+../../../rtl

// RTL files
../../../rtl/axi4_lite_if.sv
../../../rtl/Address_Aligner.sv
../../../rtl/Crc8_Calculator.sv
../../../rtl/Axi4_Lite_Master.sv
../../../rtl/Register_Block.sv
../../../rtl/fifo_sync.sv
../../../rtl/Uart_Rx.sv
../../../rtl/Uart_Tx.sv
../../../rtl/Frame_Parser.sv
../../../rtl/Frame_Builder.sv
../../../rtl/Uart_Axi4_Bridge.sv

// Test file
uart_response_debug_test.sv

// Top level
-top uart_response_debug_test

// Simulation control
+access+r