# DSIM Configuration File for AXI Integration Test
# Tests real AXI Master + Register_Block modules together

# Timescale
+timescale+1ns/1ps

# Include directories for interfaces
+incdir+../../../rtl

# Core RTL files
../../../rtl/axi4_lite_if.sv
../../../rtl/Address_Aligner.sv
../../../rtl/Axi4_Lite_Master.sv
../../../rtl/Register_Block.sv

# Test files
axi_integration_test.sv

# Top-level module
-top axi_integration_test

# Simulation options
+acc+rwb