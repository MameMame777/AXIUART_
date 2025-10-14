# DSIM Configuration File for UART-AXI4 Bridge Verification
# This file specifies all source files for compilation
# Updated: 2025-10-13 - Fixed file paths for FastMCP compatibility

# Timescale specification
+timescale+1ns/1ps

# UVM Library and include paths
+define+UVM_NO_DEPRECATED
+define+UVM_OBJECT_MUST_HAVE_CONSTRUCTOR
+define+DEFINE_SIM
+define+UVM_NO_DPI
+define+WAVES
+define+ENABLE_COVERAGE
+define+ENABLE_ASSERTIONS
+define+COVERAGE_ENHANCED
+define+ERROR_INJECTION_ENABLED

# Include paths for file resolution (corrected paths)
+incdir+.
+incdir+env
+incdir+agents
+incdir+agents/uart
+incdir+agents/axi4_lite
+incdir+sequences
+incdir+tests
+incdir+packages
+incdir+interfaces
+incdir+monitors
+incdir+tb
+incdir+../../rtl
+incdir+../../rtl/interfaces

# RTL interface files (must be compiled first)
interfaces/bridge_status_if.sv
../../rtl/interfaces/axi4_lite_if.sv

# RTL source files (in dependency order)
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

# Frame Parser Assertions (bind statement approach)
../../rtl/Frame_Parser_Assertions.sv
../../rtl/Frame_Parser_Assertions_Bind.sv

# Emergency diagnostic assertions (corrected path)
../emergency_frame_parser_diagnostics.sv

# UVM package files (main package first, then extensions)  
packages/uart_axi4_test_pkg.sv
packages/axiuart_cov_pkg.sv

# Transaction and Base Classes - Core UVM components
agents/uart/uart_transaction.sv

# Base sequence (single instance to avoid duplication)
sequences/uart_base_sequence.sv

# Protocol verification sequences
sequences/uart_axi4_write_protocol_sequence.sv
sequences/uart_axi4_error_protocol_sequence.sv
sequences/uart_axi4_bridge_control_sequence.sv

# Critical test files - required for UVM test registry
tests/uart_axi4_base_test.sv
tests/enhanced_uart_axi4_base_test.sv
tests/uart_basic_test.sv

# Protocol Test Files - AXI4 verification suite
tests/uart_axi4_write_protocol_test.sv
tests/uart_axi4_error_protocol_test.sv
tests/uart_axi4_bridge_control_test.sv

# Testbench top
tb/uart_axi4_tb_top.sv

# UVM library
-uvm 1.2

# Coverage options
+cover+fsm+line+cond+tgl+branch
+cover+hier+uart_axi4_tb_top.dut

# Assertion options
+assert