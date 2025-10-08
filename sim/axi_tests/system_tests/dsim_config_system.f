# DSIM Configuration File for UART-AXI System Test
# Complete end-to-end test with UART Parser + AXI Master + Register Block

# Timescale
+timescale+1ns/1ps

# Include directories for interfaces
+incdir+../../../rtl

# Core RTL files - Complete system
../../../rtl/axi4_lite_if.sv
../../../rtl/Address_Aligner.sv
../../../rtl/Axi4_Lite_Master.sv
../../../rtl/Register_Block.sv

# UART and Parser modules
../../../rtl/Uart_Rx.sv
../../../rtl/Uart_Tx.sv
../../../rtl/fifo_sync.sv
../../../rtl/Crc8_Calculator.sv
../../../rtl/Frame_Parser.sv
../../../rtl/Frame_Builder.sv
../../../rtl/Uart_Axi4_Bridge.sv

# Test files
uart_axi_system_test.sv

# Top-level module
-top uart_axi_system_test

# Simulation options
+acc+rwb