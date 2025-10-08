# DSIM Configuration File for AXI Master Unit Test
# Phase 2: AXI Master component isolation testing

# SystemVerilog files
+timescale+1ns/1ps

# RTL source files  
../../../rtl/axi4_lite_if.sv
../../../rtl/Address_Aligner.sv
../../../rtl/Axi4_Lite_Master.sv

# Test files
axi_master_unit_test.sv

# Top module
+top+axi_master_unit_test

# SystemVerilog enable
+sv

# Enable assertions
+define+ENABLE_ASSERTIONS=1