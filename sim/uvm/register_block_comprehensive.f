# DSIM Configuration File for Register Block Comprehensive Testing
# This file specifies all source files for compilation

# Timescale specification
+timescale+1ns/1ps

# UVM Library and include paths
+define+UVM_NO_DEPRECATED
+define+UVM_OBJECT_MUST_HAVE_CONSTRUCTOR
+define+ENABLE_DEBUG
+define+DEFINE_SIM

# Include paths for file resolution
+incdir+.
+incdir+env
+incdir+agents
+incdir+sequences
+incdir+tests
+incdir+packages
+incdir+interfaces
+incdir+monitors

# RTL source files (in dependency order)
interfaces/bridge_status_if.sv
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

# UVM package files (main package first, then extensions)  
packages/uart_axi4_test_pkg.sv
packages/axiuart_cov_pkg.sv
sequences/axiuart_error_sequences_pkg.sv

# Test files
tests/register_block_comprehensive_test.sv

# UVM test environment
agents/uart/uart_transaction.sv
agents/uart/uart_sequencer.sv
agents/uart/uart_driver.sv
agents/uart/uart_monitor.sv
agents/uart/uart_agent.sv

agents/axi4_lite/axi4_lite_transaction.sv
agents/axi4_lite/axi4_lite_monitor.sv

env/uart_axi4_scoreboard.sv
env/uart_axi4_coverage.sv
env/uart_axi4_env.sv

tests/uart_axi4_base_test.sv

tb/uart_axi4_tb_top.sv