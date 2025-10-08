# DSIM Configuration for Register_Block Unit Test
# Generated for AXI4 verification Phase 3

# Timescale specification
-timescale 1ns/1ps

# Include directories
+incdir+../../../rtl

# Interface files
../../../rtl/axi4_lite_if.sv

# DUT: Register_Block
../../../rtl/Register_Block.sv

# Test files
register_block_unit_test.sv

# Waveform dumping
+define+DUMP_WAVES

# Simulation control
-top register_block_unit_test

# Coverage options
+access+r