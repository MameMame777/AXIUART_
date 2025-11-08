# DSIM Configuration File for UART-AXI4 Bridge Verification
# This file specifies all source files for compilation

# Timescale specification
+timescale+1ns/1ps

# UVM Library and include paths
+define+UVM_NO_DEPRECATED
+define+UVM_OBJECT_MUST_HAVE_CONSTRUCTOR
+define+ENABLE_DEBUG

# Include paths for file resolution
+incdir+..
+incdir+../env
+incdir+../agents
+incdir+../sequences
+incdir+../tests

# RTL source files (in dependency order)
../../rtl/interfaces/uart_if.sv
../../rtl/interfaces/axi4_lite_if.sv
../../rtl/Crc8_Calculator.sv
../../rtl/fifo_sync.sv
../../rtl/Address_Aligner.sv
../../rtl/Uart_Rx.sv
../../rtl/Uart_Tx.sv
../../rtl/Frame_Parser.sv
../../rtl/Frame_Builder.sv
../../rtl/Axi4_Lite_Master.sv
../../rtl/Register_Block.sv
../../rtl/Uart_Axi4_Bridge.sv
../../rtl/AXIUART_Top.sv

# Assertions modules
../rtl/uart_axi4_assertions.sv
../assertions/Uart_Axi4_Bridge_Timeout_Assertions.sv
../assertions/Uart_Axi4_Bridge_Timeout_Bind.sv

# UVM package files (in dependency order)
../packages/uart_axi4_test_pkg.sv

# Testbench top
../tb/uart_axi4_tb_top.sv

# Compilation options
+define+UVM_NO_DPI
+define+WAVES
+define+ENABLE_COVERAGE
+define+ENABLE_ASSERTIONS

# UVM library
-uvm 1.2

# Include directories
+incdir+../../rtl
+incdir+../../rtl/interfaces
+incdir+../packages
+incdir+../env
+incdir+../agents/uart
+incdir+../agents/axi4_lite
+incdir+../sequences
+incdir+../tests
+incdir+../tb

# Coverage options
+cover+fsm+line+cond+tgl+branch
+cover+hier+uart_axi4_tb_top.dut

# Assertion options
+assert