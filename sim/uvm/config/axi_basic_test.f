# DSIM Configuration for AXI Basic Operation Test
# Purpose: Test AXI Master + Register_Block isolation without UART complexity

# Timescale
-timescale 1ns/1ps

# Include paths
-incdir ../../../rtl
-incdir ../interfaces  
-incdir ../packages
-incdir ../tests
-incdir ../tb

# RTL source files (AXI components only)
../../../rtl/axi4_lite_if.sv
../../../rtl/Address_Aligner.sv
../../../rtl/Axi4_Lite_Master.sv
../../../rtl/Register_Block.sv

# Testbench files
../tb/axi_basic_tb.sv

# Top-level module
-top axi_basic_tb

# Compilation options
-sv

# Waveform generation  
-waves axi_basic_test.mxd